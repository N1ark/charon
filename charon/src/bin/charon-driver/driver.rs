//! Run the rustc compiler with our custom options and hooks.
use crate::CharonFailure;
use crate::toolchain::CHARON_SYSROOT_VAR;
use crate::translate::get_mir::instantiated_mir;
use crate::translate::translate_crate;
use charon_lib::errors::{DeferredOutput, ErrorCtx};
use charon_lib::export::CrateData;
use charon_lib::options::{self, CliOpts, MirLevel, selected_crate_var};
use charon_lib::transform::run_transformation_passes;
use charon_lib::utils::arg_value;
use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_data_structures::sync::{DynSync, IntoDynSyncSend};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::Config;
use rustc_interface::interface::Compiler;
use rustc_middle::mir;
use rustc_middle::ty::{GenericArgsRef, InstanceKind, TyCtxt, TypingEnv};
use rustc_middle::util::Providers;
use rustc_session::config::{OutputType, OutputTypes};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::{ErrorGuaranteed, Symbol};
use std::collections::VecDeque;
use std::num::NonZero;
use std::panic;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;
use std::{env, fmt, thread};

/// Helper that runs the compiler and catches its fatal errors.
fn run_compiler_with_callbacks(
    args: Vec<String>,
    callbacks: &mut (dyn Callbacks + Send),
) -> Result<(), CharonFailure> {
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, callbacks))
        .map_err(|_| CharonFailure::RustcError)
}

/// Tweak options to get usable MIR even for foreign crates.
fn set_mir_options(config: &mut Config) {
    config.opts.unstable_opts.always_encode_mir = true;
    config.opts.unstable_opts.mir_opt_level = Some(0);
    config.opts.unstable_opts.mir_preserve_ub = true;
    let disabled_mir_passes = ["CheckAlignment", "CheckNull"];
    for pass in disabled_mir_passes {
        config
            .opts
            .unstable_opts
            .mir_enable_passes
            .push((pass.to_owned(), false));
    }
}

/// The number of threads of the parallel parts of the work (rustc's front-end, our passes): one per
/// available CPU, up to a cap. Past it, more threads cost CPU time and memory but no wall time.
fn default_thread_count() -> usize {
    const MAX_THREADS: usize = 16;
    std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .min(MAX_THREADS)
}

/// Set up rayon's global pool, on which the transformation passes run. As visitors recurse on deep
/// types, its threads get the stack size of the thread that runs the passes.
fn init_thread_pool() {
    let mut builder = rayon::ThreadPoolBuilder::new()
        .thread_name(|_| "charon".to_owned())
        .stack_size(rustc_interface::util::DEFAULT_STACK_SIZE);
    // Like rayon, let `RAYON_NUM_THREADS` choose the number of threads.
    if env::var_os("RAYON_NUM_THREADS").is_none() {
        builder = builder.num_threads(default_thread_count());
    }
    builder.build_global().unwrap();
}

/// Enable rustc's parallel front-end.
fn set_parallel_frontend(config: &mut Config) {
    if config.opts.jobs.frontend.is_none() {
        config.opts.jobs.frontend = NonZero::new(default_thread_count()).filter(|n| n.get() > 1);
    }
}

// We use a static to be able to pass data to `override_queries`.
static SKIP_BORROWCK: AtomicBool = AtomicBool::new(false);
fn set_skip_borrowck() {
    SKIP_BORROWCK.store(true, Ordering::SeqCst);
}
fn skip_borrowck_if_set(providers: &mut Providers) {
    if SKIP_BORROWCK.load(Ordering::SeqCst) {
        providers.queries.mir_borrowck = |tcx, _def_id| {
            // Empty result, which is what is used for custom_mir bodies.
            Ok(tcx.arena.alloc(Default::default()))
        }
    }
}

fn setup_compiler(
    config: &mut Config,
    options: &CliOpts,
    is_target_crate: bool,
    do_translate: bool,
    emit_artifacts: bool,
    codegen: bool,
) {
    if is_target_crate && let Some(crate_name) = &config.opts.crate_name {
        // Rerun compilation if this variable changes. We don't do that for dependencies built for
        // the host, like build scripts.
        let var = selected_crate_var(crate_name);
        config.track_state = Some(Box::new(move |sess| {
            let value = env::var(&var).ok().map(|value| Symbol::intern(&value));
            let var = Symbol::intern(&var);
            sess.env_depinfo.borrow_mut().insert((var, value));
        }));
    }

    if do_translate {
        if options.skip_borrowck {
            // We use a static to be able to pass data to `override_queries`.
            set_skip_borrowck();
        }

        config.override_queries = Some(|_sess, providers| {
            skip_borrowck_if_set(providers);

            // TODO: catch the MIR in-flight to avoid stealing issues?
            // providers.mir_built = |tcx, def_id| {
            //     let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
            //     let mut mir = mir.steal();
            //     // use the mir
            //     tcx.alloc_steal_mir(mir)
            // };
        });

        config.opts.unstable_opts.no_codegen = !codegen;
        if !emit_artifacts {
            config.opts.output_types = OutputTypes::new(&[(OutputType::Object, None)]);
        }
        set_parallel_frontend(config);
    }
    set_mir_options(config);
}

/// Run the rustc checks that come before MIR building. Returns whether rustc reported errors. This
/// lets us avoid running Charon translation on crates rustc already rejects. Between the items it
/// checks, each thread runs `help_translation`.
fn precheck_rustc_errors(tcx: TyCtxt<'_>, help_translation: &(impl Fn() + DynSync)) -> bool {
    type QueryResult = Result<(), ErrorGuaranteed>;

    tcx.par_hir_for_each_module(|module| {
        help_translation();
        tcx.ensure_ok().check_mod_attrs(module);
        tcx.ensure_ok().check_mod_unstable_api_usage(module);
    });

    // `check_type_wf` checks all items in parallel; we do the same first, with breaks.
    let items = tcx.hir_crate_items(());
    let check_wf = |def_id| {
        help_translation();
        tcx.ensure_result().check_well_formed(def_id)
    };
    let _ = items.par_items(|item| check_wf(item.owner_id.def_id));
    let _ = items.par_impl_items(|item| check_wf(item.owner_id.def_id));
    let _ = items.par_trait_items(|item| check_wf(item.owner_id.def_id));
    let _ = items.par_foreign_items(|item| check_wf(item.owner_id.def_id));
    let _ = items.par_nested_bodies(check_wf);
    let _ = items.par_opaques(check_wf);
    let _: QueryResult = tcx.ensure_result().check_type_wf(());
    for &trait_def_id in tcx.all_local_trait_impls(()).keys() {
        let _: QueryResult = tcx.ensure_result().coherent_trait(trait_def_id);
    }
    let _: QueryResult = tcx.ensure_result().crate_inherent_impls_validity_check(());
    let _: QueryResult = tcx.ensure_result().crate_inherent_impls_overlap_check(());

    tcx.par_hir_body_owners(|def_id| {
        help_translation();
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::AnonConst) && !tcx.is_typeck_child(def_id.to_def_id()) {
            tcx.ensure_ok().typeck(def_id);
        }
    });

    tcx.dcx().has_errors().is_some()
}

/// The bodies the translation is going to read, in the order it will read them. Rustc's other
/// threads prepare them ahead of the translation, a bounded number at a time.
pub struct BodyRequests<'tcx> {
    /// The local bodies we may compute: the body owners that have MIR.
    owners: IntoDynSyncSend<FxHashSet<LocalDefId>>,
    /// The thread that runs the translation.
    translation_thread: thread::ThreadId,
    requests: IntoDynSyncSend<Mutex<Requests<'tcx>>>,
    /// Notified when `requests` changes.
    requests_changed: IntoDynSyncSend<Condvar>,
}

/// A body the translation is going to read.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BodyRequest<'tcx> {
    /// The MIR of a local item (we compute it in rustc's query cache).
    Local(LocalDefId),
    /// The MIR of `def_id` at the translation's level, instantiated with `args` in `typing_env`,
    /// as [`instantiated_mir`] returns it.
    Instantiated {
        def_id: DefId,
        args: GenericArgsRef<'tcx>,
        typing_env: TypingEnv<'tcx>,
    },
}

enum Prepared<'tcx> {
    Queued,
    InProgress,
    /// The instantiated body, if any; `None` if computing it panicked.
    Ready(Option<Option<mir::Body<'tcx>>>),
}

#[derive(Default)]
struct Requests<'tcx> {
    prepared: FxHashMap<BodyRequest<'tcx>, Prepared<'tcx>>,
    queue: VecDeque<BodyRequest<'tcx>>,
    /// The number of `Ready` bodies the translation hasn't read yet, which we bound so as to only
    /// work a little ahead of it (that's both memory and work taken from rustc's checks).
    ready: usize,
    translation_done: bool,
}

/// How many bodies we prepare ahead of the translation.
const MAX_READY_BODIES: usize = 64;

impl<'tcx> BodyRequests<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        let owners = tcx
            .hir_body_owners()
            .filter(|&def_id| !matches!(tcx.def_kind(def_id), DefKind::AnonConst))
            .collect();
        BodyRequests {
            owners: IntoDynSyncSend(owners),
            translation_thread: thread::current().id(),
            requests: IntoDynSyncSend(Default::default()),
            requests_changed: IntoDynSyncSend(Condvar::new()),
        }
    }

    /// Ask for this body to be prepared ahead of time.
    pub fn request(&self, request: BodyRequest<'tcx>) {
        // A local item without a body: rustc would ICE if we asked for its MIR.
        let local_def_id = match request {
            BodyRequest::Local(def_id) => Some(def_id),
            BodyRequest::Instantiated { def_id, .. } => def_id.as_local(),
        };
        if let Some(def_id) = local_def_id
            && !self.owners.contains(&def_id)
        {
            return;
        }
        let requests = &mut *self.requests.lock().unwrap();
        if !requests.prepared.contains_key(&request) {
            requests.prepared.insert(request, Prepared::Queued);
            requests.queue.push_back(request);
            self.requests_changed.notify_all();
        }
    }

    /// Take this instantiated body if it was prepared, waiting for it if it is being prepared.
    pub fn take(&self, request: BodyRequest<'tcx>) -> Option<Option<mir::Body<'tcx>>> {
        let mut requests = self.requests.lock().unwrap();
        loop {
            match requests.prepared.get(&request)? {
                Prepared::InProgress => {
                    requests = self.requests_changed.wait(requests).unwrap();
                    continue;
                }
                Prepared::Queued => {}
                Prepared::Ready(_) => requests.ready -= 1,
            }
            let Prepared::Ready(body) = requests.prepared.remove(&request).unwrap() else {
                return None;
            };
            self.requests_changed.notify_all();
            return body;
        }
    }

    /// Forget this body, which the translation won't read anymore.
    pub fn discard(&self, request: BodyRequest<'tcx>) {
        let requests = &mut *self.requests.lock().unwrap();
        if let Some(Prepared::Ready(_)) = requests.prepared.remove(&request) {
            requests.ready -= 1;
            self.requests_changed.notify_all();
        }
    }

    fn translation_done(&self) {
        self.requests.lock().unwrap().translation_done = true;
        self.requests_changed.notify_all();
    }

    /// Prepare the requested bodies until the translation is done.
    fn prepare_bodies(&self, tcx: TyCtxt<'tcx>, level: MirLevel) {
        // The translation may run this itself while it waits for the checks (see
        // `wait_for_rustc_checks`): then we must not wait for it.
        if thread::current().id() != self.translation_thread {
            while self.prepare_next(tcx, level, true) {}
        }
    }

    /// Prepare the requested bodies we can prepare now.
    fn help_translation(&self, tcx: TyCtxt<'tcx>, level: MirLevel) {
        while self.prepare_next(tcx, level, false) {}
    }

    /// Prepare the next requested body. Returns `false` if the translation is done, or if there
    /// is nothing to prepare for now and `wait` is not set.
    fn prepare_next(&self, tcx: TyCtxt<'tcx>, level: MirLevel, wait: bool) -> bool {
        let request = {
            let mut requests = self.requests.lock().unwrap();
            loop {
                if requests.translation_done {
                    return false;
                }
                if requests.ready < MAX_READY_BODIES
                    && let Some(request) = requests.queue.pop_front()
                {
                    if let Some(prepared @ Prepared::Queued) = requests.prepared.get_mut(&request) {
                        *prepared = Prepared::InProgress;
                        break request;
                    }
                    continue;
                }
                if !wait {
                    return false;
                }
                requests = self.requests_changed.wait(requests).unwrap();
            }
        };
        let body = match request {
            BodyRequest::Local(def_id) => {
                compute_mir(tcx, level, def_id);
                Some(None)
            }
            // If this panics, the translation will compute the body itself and report the panic.
            BodyRequest::Instantiated {
                def_id,
                args,
                typing_env,
            } => charon_lib::transform::ctx::without_panic_messages(|| {
                panic::catch_unwind(panic::AssertUnwindSafe(|| {
                    instantiated_mir(tcx, def_id, args, typing_env, level)
                }))
                .ok()
            }),
        };
        let requests = &mut *self.requests.lock().unwrap();
        if let Some(prepared) = requests.prepared.get_mut(&request) {
            *prepared = Prepared::Ready(body);
            requests.ready += 1;
        }
        self.requests_changed.notify_all();
        true
    }
}

fn compute_mir(tcx: TyCtxt<'_>, level: MirLevel, def_id: LocalDefId) {
    match level {
        MirLevel::Built => tcx.ensure_done().mir_built(def_id),
        MirLevel::Promoted => tcx.ensure_done().mir_promoted(def_id),
        MirLevel::Elaborated => tcx
            .ensure_done()
            .mir_drops_elaborated_and_const_checked(def_id),
        MirLevel::Optimized => {}
    }
}

/// Compute the MIR bodies the translation will ask for, using rustc's parallel frontend, starting
/// with the ones it requested. The translation would otherwise compute them one by one (for
/// elaborated MIR this includes running borrowck); rustc computes them anyway after the
/// translation.
fn prefetch_local_mir<'tcx>(tcx: TyCtxt<'tcx>, level: MirLevel, requests: &BodyRequests<'tcx>) {
    tcx.par_hir_body_owners(|def_id| {
        requests.help_translation(tcx, level);
        if requests.owners.contains(&def_id) {
            compute_mir(tcx, level, def_id);
        }
    });
}

/// Run rustc checks that normally happen close to codegen, so that we get all the post-mono errors
/// etc.
fn check_late_rustc_errors(tcx: TyCtxt<'_>) {
    tcx.par_hir_body_owners(|def_id| {
        let _ = tcx.instance_mir(InstanceKind::Item(def_id.to_def_id()));
    });

    if tcx.dcx().err_count() == 0 {
        let _ = tcx.collect_and_partition_mono_items(());
    }
}

/// Run the rustc driver with our custom hooks. Returns `None` if the crate was not compiled with
/// charon (e.g. because it was a dependency). Otherwise returns the transformed crate and its
/// serialized output.
pub fn run_rustc_driver() -> Result<Option<(TransformOutput, CliOpts)>, CharonFailure> {
    // Retreive the command-line arguments pased to `charon_driver`. The first arg is the path to
    // the current executable, we skip it.
    let mut compiler_args: Vec<String> = env::args().skip(1).collect();
    trace!(
        "charon-driver called with args: {}",
        compiler_args.iter().format(" ")
    );

    // When called using cargo, we tell cargo to use `charon-driver` by setting the `RUSTC_WRAPPER`
    // env var. This uses `charon-driver` for all the crates being compiled.
    // We may however not want to be calling charon on all crates; `CARGO_PRIMARY_PACKAGE` tells us
    // whether the crate was specifically selected or is a dependency.
    let is_workspace_dependency =
        env::var("CHARON_USING_CARGO").is_ok() && env::var("CARGO_PRIMARY_PACKAGE").is_err();
    // Let rustc emit artifacts (metadata, binaries) normally if invoked by `cargo` or when
    // explicitly requested.
    let emit_artifacts =
        env::var("CHARON_USING_CARGO").is_ok() || env::var("CHARON_EMIT_ARTIFACTS").is_ok();
    // Let rustc emit codegen artifacts, more specifically.
    let mut codegen = emit_artifacts;
    // Determines if we are being invoked to build a crate for the "target" architecture, in
    // contrast to the "host" architecture. Host crates are for build scripts and proc macros and
    // still need to be built like normal; target crates need to be processed by Charon.
    //
    // Currently, we detect this by checking for "--target=", which is never set for host crates.
    // This matches what Miri does, which hopefully makes it reliable enough. This relies on us
    // always invoking cargo itself with `--target`, which `charon` ensures.
    let is_target_crate = arg_value(&compiler_args, "--target").is_some();
    // Whether this is the crate we want to translate.
    let is_selected_crate = !is_workspace_dependency && is_target_crate;

    let mut error_ctx = ErrorCtx::new();

    // Retrieve the Charon options by deserializing them from the environment variable
    // (cargo-charon serialized the arguments and stored them in a specific environment
    // variable before calling cargo with `RUSTC_WRAPPER=charon-driver`).
    let options = match env::var(options::CHARON_ARGS)
        .ok()
        .map(|opts| serde_json::from_str::<options::CliOpts>(&opts).unwrap())
    {
        Some(options) => options,
        None if !is_selected_crate => Default::default(),
        None => {
            register_error!(
                error_ctx,
                no_crate,
                "environment variable `CHARON_ARGS` not set; \
                don't call `charon-driver` directly, call `charon rustc` instead"
            );
            return Err(CharonFailure::CharonError(1));
        }
    };

    if options.sysroot.as_deref() == Some("default") {
        // Do nothing
    } else if let Some(sysroot) = options.sysroot.as_ref()
        && sysroot != "miri"
    {
        compiler_args.push(format!("--sysroot={sysroot}"));
    } else if is_target_crate && let Ok(sysroot) = env::var(CHARON_SYSROOT_VAR) {
        // Charon built a sysroot for us to use.
        compiler_args.push(format!("--sysroot={sysroot}"));
        // The Miri sysroot (which is what Charon builds atm) doesn't support codegen.
        codegen = false;
    }

    let output = if !is_selected_crate {
        trace!("Skipping charon; running compiler normally instead.");
        // Run the compiler normally.
        let mut callback = RunCompilerNormallyCallbacks { is_target_crate };
        run_compiler_with_callbacks(compiler_args, &mut callback)?;
        None
    } else {
        error_ctx.continue_on_failure = !options.abort_on_error;
        error_ctx.error_on_warnings = options.error_on_warnings;

        // To select an impl, the new solver builds the proof tree of the whole goal without
        // using its evaluation cache, which makes our many trait resolutions much slower.
        if options.old_trait_solver
            && !compiler_args.iter().any(|arg| arg.contains("next-solver"))
            && !options.rustc_args.iter().any(|arg| arg.contains("next-solver"))
        {
            compiler_args.push("-Znext-solver=coherence".to_owned());
        }
        for extra_flag in options.rustc_args.iter().cloned() {
            compiler_args.push(extra_flag);
        }

        init_thread_pool();
        // Call the Rust compiler with our custom callback.
        let mut callback = CharonCallbacks {
            options: &options,
            emit_artifacts,
            codegen,
            error_ctx: Some(error_ctx),
            transform: None,
        };
        let result = charon_lib::timing::time("rustc-driver", || {
            run_compiler_with_callbacks(compiler_args, &mut callback)
        });
        // If `transform` is not set here, there was a fatal error. On failure we exit without
        // waiting for the transformation passes; their output stays held back and their files are
        // discarded.
        let transform = match (result, callback.transform) {
            (Ok(()), Some(transform)) => transform,
            (result, transform) => {
                if let Some(transform) = transform {
                    transform.discard_files();
                }
                return Err(result.err().unwrap_or(CharonFailure::RustcError));
            }
        };
        // rustc is done printing: the passes' output can go to stderr as it comes, from another
        // thread so the passes don't wait for it. With logging on, the logs would come out of
        // order.
        if env::var_os("RUST_LOG").is_none() {
            charon_lib::errors::print_in_background();
        }
        transform.output.lock().unwrap().release();
        let output = transform.thread.join();
        if let Err(e) = charon_lib::errors::finish_printing_in_background() {
            panic!("failed printing to stderr: {e}");
        }
        let output = output.unwrap_or_else(|payload| panic::resume_unwind(payload));
        Some((output, options))
    };
    Ok(output)
}

/// The callbacks for Charon
pub struct CharonCallbacks<'a> {
    options: &'a CliOpts,
    /// Whether rustc should emit the artifacts (metadata, binaries) it normally would. This is
    /// needed under cargo so later crate invocations can consume earlier selected crates.
    emit_artifacts: bool,
    /// Whether to let rustc run codegen as it normally would.
    codegen: bool,
    /// Context for errors; `take()`n by translation.
    error_ctx: Option<ErrorCtx>,
    /// The thread that runs the transformation passes on the translated crate. `None` at the start
    /// or if we couldn't translate anything.
    transform: Option<Transformation>,
}

/// The transformation passes and the serialization of their result, which run alongside the end
/// of rustc's compilation.
struct Transformation {
    thread: JoinHandle<TransformOutput>,
    /// The messages of the passes, held back until rustc is done.
    output: Arc<Mutex<DeferredOutput>>,
    files: Arc<Mutex<OutputFiles>>,
}

/// The output files are serialized to temporary files, which only become the real output once
/// rustc succeeded.
#[derive(PartialEq)]
enum OutputFiles {
    NotStarted,
    Writing,
    Discarded,
}

/// The result of the transformation thread.
pub struct TransformOutput {
    pub crate_data: CrateData,
    pub error_count: usize,
    /// The serialized output, as pairs of a temporary file and the destination it should be moved
    /// to. `Err` if serialization failed.
    pub files: Result<Vec<(PathBuf, PathBuf)>, ()>,
}

impl Transformation {
    /// Make sure no output file is left behind, because rustc failed.
    fn discard_files(self) {
        let mut files = self.files.lock().unwrap();
        if *files == OutputFiles::NotStarted {
            *files = OutputFiles::Discarded;
            return;
        }
        drop(files);
        if let Ok(output) = self.thread.join() {
            for (tmp, _) in output.files.into_iter().flatten() {
                let _ = std::fs::remove_file(tmp);
            }
        }
    }
}

/// Serialize the crate to temporary files next to its targets.
fn serialize_to_temp_files(
    crate_data: &CrateData,
    options: &CliOpts,
) -> Result<Vec<(PathBuf, PathBuf)>, ()> {
    let targets = options.targets(&crate_data.translated.crate_name);
    trace!("Targets: {:?}", targets);
    let mut files = vec![];
    for (target, format) in targets {
        let tmp = target.with_added_extension(format!("{}.tmp", std::process::id()));
        files.push((tmp.clone(), target));
        let result = crate_data.serialize_to_file(&tmp, format, !options.no_dedup_serialized_ast);
        if result.is_err() {
            for (tmp, _) in files {
                let _ = std::fs::remove_file(tmp);
            }
            return Err(());
        }
    }
    Ok(files)
}
impl<'a> Callbacks for CharonCallbacks<'a> {
    fn config(&mut self, config: &mut Config) {
        setup_compiler(
            config,
            self.options,
            true,
            true,
            self.emit_artifacts,
            self.codegen,
        );
    }

    /// The MIR is modified in place: borrow-checking requires the "promoted" MIR, which causes the
    /// "built" MIR (which results from the conversion to HIR to MIR) to become unaccessible.
    /// Because we require built MIR at the moment, we hook ourselves before MIR-based analysis
    /// passes.
    fn after_expansion<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        // Set up our own `DefId` debug routine.
        rustc_hir::def_id::DEF_ID_DEBUG
            .swap(&(def_id_debug as fn(_, &mut fmt::Formatter<'_>) -> _));

        let options = self.options;
        let mut error_ctx = self.error_ctx.take().unwrap();
        let sysroot = compiler.sess.opts.sysroot.path().to_owned();
        // We don't translate crates that rustc rejects. Our errors are held back until rustc's
        // checks pass; if they fail, we discard the translation, panics included.
        let deferred_output = Arc::new(Mutex::new(DeferredOutput::default()));
        error_ctx.deferred_output = Some(deferred_output.clone());
        let body_requests = Arc::new(BodyRequests::new(tcx));
        let translation_requests = body_requests.clone();
        let rustc_checks = move |prepare_bodies: bool| {
            let done = || {
                let _ = rustc_const_uneval::RUSTC_CHECKS_DONE.set(());
            };
            let _done = rustc_data_structures::defer(done);
            let level = options.mir_level();
            // Computing the bodies the translation is about to need is what it would otherwise do
            // in parallel with the checks.
            let help_translation = || body_requests.help_translation(tcx, level);
            if charon_lib::timing::time("rustc-precheck-errors", || {
                precheck_rustc_errors(tcx, &help_translation)
            }) {
                return Err(());
            }
            deferred_output.lock().unwrap().release();
            charon_lib::timing::time("rustc-prefetch-mir", || {
                prefetch_local_mir(tcx, level, &body_requests)
            });
            if prepare_bodies {
                done();
                body_requests.prepare_bodies(tcx, level);
            }
            Ok(())
        };
        let translate = move || {
            let _done = rustc_data_structures::defer(|| translation_requests.translation_done());
            charon_lib::timing::time("translate-crate", || {
                translate_crate::translate(
                    tcx,
                    options,
                    error_ctx,
                    sysroot,
                    translation_requests.clone(),
                )
            })
        };

        // Rather than waiting for rustc's checks, we run them on rustc's other threads while we
        // translate on this one (the first closure of a join runs on the current thread). This
        // relies on `wait_for_rustc_checks`, which doesn't cover built MIR: borrowck (e.g. for
        // opaque types) steals the built MIR of plain functions.
        let translated = if rustc_data_structures::sync::is_dyn_thread_safe()
            && options.mir_level() != MirLevel::Built
        {
            let (translated, checks) = rustc_data_structures::sync::par_join(
                move || IntoDynSyncSend(panic::catch_unwind(panic::AssertUnwindSafe(translate))),
                move || rustc_checks(true),
            );
            if checks.is_err() {
                return Compilation::Continue;
            }
            translated
                .0
                .unwrap_or_else(|panic| panic::resume_unwind(panic))
        } else if rustc_checks(false).is_ok() {
            translate()
        } else {
            return Compilation::Continue;
        };
        let Ok(mut ctx) = translated else {
            return Compilation::Continue;
        };

        // The rest of the compilation can't affect the translated crate, so we run the
        // transformation passes alongside it. Their errors are held back until rustc is done, so
        // that they come after rustc's own as if we ran them sequentially.
        // We also serialize the result before rustc is done, to temporary files.
        let output = Arc::new(Mutex::new(DeferredOutput::default()));
        ctx.errors.get_mut().unwrap().deferred_output = Some(output.clone());
        let files = Arc::new(Mutex::new(OutputFiles::NotStarted));
        let thread_files = files.clone();
        let options = options.clone();
        let thread = thread::Builder::new()
            .name("charon".to_owned())
            .stack_size(rustc_interface::util::DEFAULT_STACK_SIZE)
            .spawn(move || {
                charon_lib::timing::time("transformation-passes", || {
                    run_transformation_passes(&options, &mut ctx)
                });
                // Serialization prints its errors directly.
                if let Err(e) = charon_lib::errors::finish_printing_in_background() {
                    panic!("failed printing to stderr: {e}");
                }
                let error_count = ctx.error_ctx().error_count;
                let crate_data = CrateData::new(ctx);
                let files = {
                    let mut files = thread_files.lock().unwrap();
                    if *files == OutputFiles::Discarded {
                        Ok(vec![])
                    } else {
                        *files = OutputFiles::Writing;
                        drop(files);
                        charon_lib::timing::time("serialize", || {
                            serialize_to_temp_files(&crate_data, &options)
                        })
                    }
                };
                TransformOutput {
                    crate_data,
                    error_count,
                    files,
                }
            })
            .unwrap();
        self.transform = Some(Transformation {
            thread,
            output,
            files,
        });

        Compilation::Continue
    }
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if !self.emit_artifacts {
            charon_lib::timing::time("rustc-late-checks", || check_late_rustc_errors(tcx));
        }
        Compilation::Continue
    }
}

/// Dummy callbacks used to run the compiler normally when we shouldn't be analyzing the crate.
pub struct RunCompilerNormallyCallbacks {
    is_target_crate: bool,
}

impl Callbacks for RunCompilerNormallyCallbacks {
    fn config(&mut self, config: &mut Config) {
        setup_compiler(
            config,
            &Default::default(),
            self.is_target_crate,
            false,
            true,
            true,
        );
    }
}

/// Custom `DefId` debug routine that doesn't print unstable values like ids and hashes.
fn def_id_debug(def_id: rustc_hir::def_id::DefId, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    rustc_middle::ty::tls::with_opt(|opt_tcx| {
        if let Some(tcx) = opt_tcx {
            let crate_name = if def_id.is_local() {
                tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE)
            } else {
                tcx.cstore_untracked().crate_name(def_id.krate)
            };
            write!(
                f,
                "{}{}",
                crate_name,
                tcx.def_path(def_id).to_string_no_crate_verbose()
            )?;
        } else {
            write!(f, "<can't access `tcx` to print `DefId` path>")?;
        }
        Ok(())
    })
}
