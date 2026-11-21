//! Translating items in parallel.
//!
//! Worker jobs on rustc's thread pool pop items from a shared worklist and translate them, each
//! with its own `TranslateCtx`. The workers share the state that identifies items (ids, names),
//! the caches of computations that don't depend on the item (names, context-free types), and the
//! state of method usage. Since ids are assigned in whatever order the workers encounter items, we
//! log what each translation does (see `translate_log`), merge the workers' results into the main
//! context once the worklist is empty, and renumber everything as the sequential translation does.
use super::translate_crate::*;
use super::translate_ctx::*;
use super::translate_log::{MemoRef, TranslationLog};
use crate::driver::{BodyRequest, BodyRequests};
use crate::hax;
use crate::hax::state::ShardedMap;
use charon_lib::ast::*;
use charon_lib::errors::{DeferredOutput, ErrorCtx};
use charon_lib::ids::IndexVec;
use charon_lib::options::{CliOpts, TranslateOptions};
use rustc_data_structures::sync::Lock;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use rustc_middle::ty::TyCtxt;
use std::collections::VecDeque;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

/// A context-free type: its translation, the items it mentions and whether these are local, and
/// what translating it did.
pub(crate) type MonoType = (Ty, Vec<(ItemId, bool)>, Option<MemoRef>);

/// The state shared by the workers.
pub(crate) struct ParShared<'tcx> {
    env: WorkerEnv<'tcx>,
    /// The ids of the items, see `TranslateCtx::id_map`.
    pub(crate) ids: ShardedMap<TransItemSource<'tcx>, ItemId>,
    pub(crate) reverse_ids: ShardedMap<ItemId, TransItemSource<'tcx>>,
    /// The number of ids of each kind we gave out: types, functions, globals, trait decls, trait
    /// impls.
    counts: [AtomicUsize; 5],
    pub(crate) names: ShardedMap<ItemId, Name>,
    pub(crate) queue: Lock<Worklist<'tcx>>,
    /// See `TranslateCtx::requested_bodies`.
    pub(crate) requested_bodies: Lock<HashMap<TransItemSource<'tcx>, BodyRequest<'tcx>>>,
    pub(crate) methods: Lock<Methods>,
    /// The translated items that translation doesn't look up.
    pub(crate) funs: Lock<IndexMap<FunDeclId, FunDecl>>,
    pub(crate) globals: Lock<IndexMap<GlobalDeclId, GlobalDecl>>,
    pub(crate) impls: Lock<IndexMap<TraitImplId, TraitImpl>>,
    pub(crate) files: Lock<Files>,
    /// See `TranslateCtx::cached_names`.
    pub(crate) cached_names: ShardedMap<RustcItem<'tcx>, (Name, Option<MemoRef>)>,
    /// See `TranslateCtx::mono_type_cache`.
    pub(crate) mono_types: ShardedMap<hax::Ty<'tcx>, MonoType>,
    /// The translation contexts not in use by a job.
    ctxs: Mutex<Vec<AssertSend<Box<TranslateCtx<'tcx>>>>>,
    /// The number of contexts we created, which is also the index of the next one.
    ctx_count: AtomicUsize,
    max_jobs: usize,
    jobs: AtomicUsize,
}

#[derive(Default)]
pub(crate) struct Worklist<'tcx> {
    pub(crate) queue: VecDeque<TransItemSource<'tcx>>,
    pub(crate) processed: HashSet<TransItemSource<'tcx>>,
}

/// See the fields of the same name of `TranslateCtx` and `TranslatedCrate`.
#[derive(Default)]
pub(crate) struct Methods {
    pub(crate) method_status: IndexMap<TraitDeclId, IndexVec<TraitMethodId, MethodStatus>>,
    pub(crate) assoc_item_id_map: HashMap<hax::DefId, AssocItemId>,
    pub(crate) assoc_item_names: IndexMap<TraitDeclId, AssocItemNames>,
}

/// The items a worker translated that aren't in its `translated` crate nor in the shared one.
#[derive(Default)]
pub(crate) struct ParItems {
    pub(crate) types: HashMap<TypeDeclId, TypeDecl>,
}

impl ParItems {
    pub(crate) fn get(&self, id: ItemId) -> Option<ItemRef<'_>> {
        Some(ItemRef::Type(self.types.get(id.as_type()?)?))
    }
}

/// See the fields of the same name of `TranslateCtx` and `TranslatedCrate`.
#[derive(Default)]
pub(crate) struct Files {
    pub(crate) file_to_id: HashMap<FileName, FileId>,
    pub(crate) files: IndexVec<FileId, File>,
}

/// What we need to create the contexts of workers.
struct WorkerEnv<'tcx> {
    tcx: TyCtxt<'tcx>,
    cli_options: CliOpts,
    hax_state: hax::StateWithBase<'tcx>,
    sysroot: PathBuf,
    deferred_output: Option<Arc<Mutex<DeferredOutput>>>,
    body_requests: Arc<BodyRequests<'tcx>>,
}

/// The values we move to worker threads. Rustc types are only `DynSend`, and rustc's thread pool
/// only runs when they may be sent (`rustc_data_structures::sync::is_dyn_thread_safe`).
struct AssertSend<T>(T);
unsafe impl<T> Send for AssertSend<T> {}
unsafe impl<T> Sync for AssertSend<T> {}
impl<T> AssertSend<T> {
    // A method, so that closures capture the whole wrapper.
    fn into_inner(self) -> T {
        self.0
    }
}

thread_local! {
    /// Whether this thread must not run translation workers. A thread waiting inside a
    /// translation, or inside other work that a translation may wait for, may run another job: it
    /// must not translate then.
    static TRANSLATING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The scope of the parallel translation, to spawn jobs from anywhere.
    static SCOPE: std::cell::Cell<*const ()> = const { std::cell::Cell::new(std::ptr::null()) };
}

/// Return the memory freed so far to the OS. Freeing the workers' state leaves memory that the
/// allocator would otherwise keep around.
pub(crate) fn purge_freed_memory() {
    #[cfg(all(feature = "jemalloc", not(windows)))]
    // SAFETY: `arena.<MALLCTL_ARENAS_ALL>.purge` takes no arguments.
    unsafe {
        tikv_jemalloc_sys::mallctl(
            c"arena.4096.purge".as_ptr(),
            std::ptr::null_mut(),
            std::ptr::null_mut(),
            std::ptr::null_mut(),
            0,
        );
    }
}

/// Run `f`, during which this thread doesn't run translation workers.
pub(crate) fn without_translation_jobs<R>(f: impl FnOnce() -> R) -> R {
    let outer = TRANSLATING.replace(true);
    let _restore = rustc_data_structures::defer(|| TRANSLATING.set(outer));
    f()
}

/// Whether we can translate in parallel with these options.
pub(crate) fn can_translate_in_parallel(ctx: &TranslateCtx<'_>) -> bool {
    use charon_lib::name_matcher::PatElem;
    rustc_data_structures::sync::is_dyn_thread_safe()
        && ctx.cache.is_none()
        && ctx.errors.borrow().continue_on_failure()
        && !ctx.options.collect_instantiated_layouts
        // Matching an impl pattern needs the impl, which may be in another worker's crate.
        && !ctx.options.item_opacities.iter().any(|(pat, _)| {
            pat.elems.iter().any(|elem| matches!(elem, PatElem::Impl(_)))
        })
}

impl<'tcx> TranslateCtx<'tcx> {
    /// Translate the items in the worklist in parallel with `threads` workers, then renumber.
    pub(crate) fn translate_in_parallel(&mut self, cli_options: &CliOpts, threads: usize) {
        let shared = Arc::new(ParShared {
            env: WorkerEnv {
                tcx: self.tcx,
                cli_options: cli_options.clone(),
                hax_state: self.hax_state.clone(),
                sysroot: self.sysroot.clone(),
                deferred_output: self.errors.borrow().deferred_output.clone(),
                body_requests: self.body_requests.clone(),
            },
            ids: Default::default(),
            reverse_ids: Default::default(),
            counts: Default::default(),
            names: Default::default(),
            queue: Default::default(),
            requested_bodies: Default::default(),
            methods: Default::default(),
            funs: Default::default(),
            globals: Default::default(),
            impls: Default::default(),
            files: Default::default(),
            cached_names: Default::default(),
            mono_types: Default::default(),
            ctxs: Default::default(),
            ctx_count: AtomicUsize::new(1),
            max_jobs: threads,
            jobs: Default::default(),
        });
        self.share_state(&shared);
        self.par = Some(shared.clone());

        let main = AssertSend((&mut *self, shared.clone()));
        rustc_thread_pool::scope(move |scope| {
            let (ctx, shared) = main.into_inner();
            let old_scope = SCOPE.replace(scope as *const _ as *const ());
            // Once the queue is empty, the workers translate what they enqueue themselves, and the
            // scope waits for them. Meanwhile this thread is an idle thread of the pool: it helps
            // with the jobs, and else gives up its rustc thread slot, which the workers may need.
            loop {
                shared.spawn_jobs();
                let Some(src) = shared.pop() else {
                    break;
                };
                TRANSLATING.set(true);
                ctx.translate_item(&src);
                TRANSLATING.set(false);
                shared.done(ctx, &src);
            }
            SCOPE.set(old_scope);
        });

        self.par = None;
        let mut workers: Vec<TranslateCtx<'tcx>> =
            std::mem::take(&mut *shared.ctxs.lock().unwrap())
                .into_iter()
                .map(|ctx| *ctx.0)
                .collect();
        for worker in &mut workers {
            worker.par = None;
        }
        let shared = Arc::into_inner(shared).expect("the workers are done");
        charon_lib::timing::time("translate-merge", || self.merge_workers(shared, workers));
        purge_freed_memory();
    }

    /// Move the state the workers share from this context to `shared`.
    fn share_state(&mut self, shared: &ParShared<'tcx>) {
        for (src, id) in self.id_map.drain() {
            shared.ids.insert(src, id);
        }
        for (id, src) in self.reverse_id_map.drain() {
            shared.reverse_ids.insert(id, src);
        }
        let krate = &mut self.translated;
        let counts = [
            krate.type_decls.slot_count(),
            krate.fun_decls.slot_count(),
            krate.global_decls.slot_count(),
            krate.trait_decls.slot_count(),
            krate.trait_impls.slot_count(),
        ];
        for (count, n) in shared.counts.iter().zip(counts) {
            count.store(n, Ordering::Relaxed);
        }
        for (id, name) in std::mem::take(&mut krate.item_names) {
            shared.names.insert(id, name);
        }
        let mut queue = shared.queue.lock();
        queue.queue = std::mem::take(&mut self.items_to_translate);
        queue.processed = std::mem::take(&mut self.processed);
        drop(queue);
        *shared.requested_bodies.lock() = std::mem::take(&mut self.requested_bodies);
        *shared.methods.lock() = Methods {
            method_status: std::mem::take(&mut self.method_status),
            assoc_item_id_map: std::mem::take(&mut self.assoc_item_id_map),
            assoc_item_names: std::mem::take(&mut krate.assoc_item_names),
        };
        *shared.funs.lock() = std::mem::take(&mut krate.fun_decls);
        *shared.globals.lock() = std::mem::take(&mut krate.global_decls);
        *shared.impls.lock() = std::mem::take(&mut krate.trait_impls);
        *shared.files.lock() = Files {
            file_to_id: std::mem::take(&mut self.file_to_id),
            files: std::mem::take(&mut krate.files),
        };
        use super::translate_cache::MemoKey;
        for (item, name) in std::mem::take(&mut self.cached_names) {
            let memo = self.log_memo_ref(&MemoKey::Name(item.clone()));
            shared.cached_names.insert(item, (name, memo));
        }
        for (ty, (tr_ty, deps)) in std::mem::take(&mut self.mono_type_cache) {
            let memo = self.log_memo_ref(&MemoKey::Ty(ty.clone()));
            shared.mono_types.insert(ty, (tr_ty, deps, memo));
        }
    }

    /// Put the results of the workers and the shared state back into this context.
    fn merge_workers(&mut self, shared: ParShared<'tcx>, mut workers: Vec<TranslateCtx<'tcx>>) {
        let ParShared {
            ids,
            reverse_ids,
            counts,
            names,
            queue,
            methods,
            funs,
            globals,
            impls,
            files,
            ..
        } = shared;
        let queue = queue.into_inner();
        self.processed = queue.processed;
        let methods = methods.into_inner();
        self.method_status = methods.method_status;
        self.assoc_item_id_map = methods.assoc_item_id_map;
        let files = files.into_inner();
        self.file_to_id = files.file_to_id;
        let krate = &mut self.translated;
        krate.assoc_item_names = methods.assoc_item_names;
        krate.files = files.files;
        krate.fun_decls = funs.into_inner();
        krate.global_decls = globals.into_inner();
        krate.trait_impls = impls.into_inner();
        let counts = counts.map(|count| count.into_inner());
        fn extend<I: charon_lib::ids::Idx, T>(items: &mut IndexMap<I, T>, count: usize) {
            items.reserve_slots(count.saturating_sub(items.slot_count()));
        }
        extend(&mut krate.type_decls, counts[0]);
        extend(&mut krate.fun_decls, counts[1]);
        extend(&mut krate.global_decls, counts[2]);
        extend(&mut krate.trait_decls, counts[3]);
        extend(&mut krate.trait_impls, counts[4]);

        // Merge the workers' items and logs, in the order of their index.
        workers.sort_by_key(|ctx| ctx.worker_index);
        let main_items = std::mem::take(&mut self.par_items);
        self.merge_par_items(main_items);
        let main_log = self.log.as_mut().unwrap();
        let mut logs = vec![std::mem::take(&mut **main_log)];
        for mut worker in workers {
            // An item may have been translated by several workers, which got the same result.
            fn merge_items<I: charon_lib::ids::Idx, T>(
                into: &mut IndexMap<I, T>,
                from: IndexMap<I, T>,
            ) {
                for (id, item) in from.into_iter_indexed() {
                    if into.get(id).is_none() {
                        into.set_slot_extend(id, item);
                    }
                }
            }
            let krate = &mut self.translated;
            let worker_krate = std::mem::take(&mut worker.translated);
            merge_items(&mut krate.type_decls, worker_krate.type_decls);
            merge_items(&mut krate.fun_decls, worker_krate.fun_decls);
            merge_items(&mut krate.global_decls, worker_krate.global_decls);
            merge_items(&mut krate.trait_decls, worker_krate.trait_decls);
            merge_items(&mut krate.trait_impls, worker_krate.trait_impls);
            self.merge_par_items(std::mem::take(&mut worker.par_items));
            for (parent, child, _) in worker.containment_graph.all_edges() {
                self.containment_graph.add_edge(parent, child, ());
            }
            logs.push(*worker.log.take().unwrap());
            // Give the memory of this worker back before merging the next one.
            drop(worker);
            purge_freed_memory();
        }
        // Sized upfront, as growing them would hold two copies at once.
        self.id_map.reserve(ids.len());
        self.id_map.extend(ids.into_entries());
        self.reverse_id_map.reserve(reverse_ids.len());
        self.reverse_id_map.extend(reverse_ids.into_entries());
        let krate = &mut self.translated;
        krate.item_names.reserve(names.len());
        krate.item_names.extend(names.into_entries());
        // The memoized computations of this context may have raised errors formatted without all
        // the names, we don't want to reuse them.
        self.cached_item_metas.clear();
        let mut log = TranslationLog::merge(logs);
        // The workers didn't know all the names when formatting their errors.
        log.mark_worker_errors();
        self.log = Some(Box::new(log));
    }

    fn merge_par_items(&mut self, items: ParItems) {
        // An item may have been translated by several workers, which got the same result.
        let krate = &mut self.translated;
        for (id, decl) in items.types {
            if krate.type_decls.get(id).is_none() {
                krate.type_decls.set_slot_extend(id, decl);
            }
        }
    }

    /// Create the context of a new worker.
    fn new_worker(shared: &Arc<ParShared<'tcx>>) -> Box<TranslateCtx<'tcx>> {
        let env = &shared.env;
        let mut error_ctx = ErrorCtx::new();
        let options = TranslateOptions::new(&mut error_ctx, &env.cli_options);
        error_ctx.deferred_output = env.deferred_output.clone();
        let mut ctx = TranslateCtx::new(
            env.tcx,
            env.sysroot.clone(),
            env.hax_state.clone(),
            options,
            error_ctx,
            &env.cli_options,
            env.body_requests.clone(),
        );
        let index = shared.ctx_count.fetch_add(1, Ordering::Relaxed);
        ctx.par = Some(shared.clone());
        ctx.worker_index = index;
        ctx.register_target_info();
        ctx.start_translation_log();
        ctx.log_finish_start();
        Box::new(ctx)
    }
}

impl<'tcx> ParShared<'tcx> {
    /// Mark this item of the shared crate as having errors.
    pub(crate) fn set_has_errors(&self, id: ItemId) {
        let mut funs = self.funs.lock();
        let mut globals = self.globals.lock();
        let mut impls = self.impls.lock();
        let item_meta = match id {
            ItemId::Fun(id) => funs.get_mut(id).map(|decl| &mut decl.item_meta),
            ItemId::Global(id) => globals.get_mut(id).map(|decl| &mut decl.item_meta),
            ItemId::TraitImpl(id) => impls.get_mut(id).map(|decl| &mut decl.item_meta),
            _ => None,
        };
        if let Some(item_meta) = item_meta {
            item_meta.has_errors = true;
        }
    }

    /// Reserve an id for an item of this kind, see `TranslateCtx::reserve_item_id`.
    pub(crate) fn reserve_item_id(&self, kind: TransItemSourceKind) -> Option<ItemId> {
        use TransItemSourceKind::*;
        let kind_index = match kind {
            Type | VTable => 0,
            Fun | ClosureAsFnCast | VirtualMethod(..) | VTableMethod(..) | VTableDropShim(..)
            | IntrinsicFallback => 1,
            Global | VTableInstance(..) => 2,
            TraitDecl => 3,
            TraitImpl(..) => 4,
            InherentImpl | Module => return None,
        };
        let index = self.counts[kind_index].fetch_add(1, Ordering::Relaxed);
        Some(match kind_index {
            0 => ItemId::Type(TypeDeclId::from_usize(index)),
            1 => ItemId::Fun(FunDeclId::from_usize(index)),
            2 => ItemId::Global(GlobalDeclId::from_usize(index)),
            3 => ItemId::TraitDecl(TraitDeclId::from_usize(index)),
            _ => ItemId::TraitImpl(TraitImplId::from_usize(index)),
        })
    }

    pub(crate) fn push(self: &Arc<Self>, src: TransItemSource<'tcx>) {
        self.queue.lock().queue.push_back(src);
        self.spawn_jobs();
    }

    /// Pop the next item to translate, if any.
    fn pop(&self) -> Option<TransItemSource<'tcx>> {
        let mut worklist = self.queue.lock();
        while let Some(src) = worklist.queue.pop_front() {
            if worklist.processed.insert(src.clone()) {
                return Some(src);
            }
        }
        None
    }

    fn done(&self, ctx: &TranslateCtx<'tcx>, src: &TransItemSource<'tcx>) {
        if let Some(request) = self.requested_bodies.lock().remove(src) {
            ctx.body_requests.discard(request);
        }
    }

    /// Spawn jobs while there are queued items and free threads.
    fn spawn_jobs(self: &Arc<Self>) {
        let scope = SCOPE.get();
        // Until rustc's checks are done, the other threads may run our jobs inside theirs, which
        // a translation may need to wait for (see `wait_for_rustc_checks`).
        if scope.is_null() || rustc_const_uneval::RUSTC_CHECKS_DONE.get().is_none() {
            return;
        }
        // SAFETY: `SCOPE` is only set inside the scope.
        let scope: &rustc_thread_pool::Scope<'_> = unsafe { &*(scope as *const _) };
        loop {
            let jobs = self.jobs.load(Ordering::Relaxed);
            if jobs >= self.max_jobs || self.queue.lock().queue.len() <= jobs {
                return;
            }
            if self
                .jobs
                .compare_exchange(jobs, jobs + 1, Ordering::Relaxed, Ordering::Relaxed)
                .is_ok()
            {
                let shared = AssertSend(self.clone());
                scope.spawn(move |scope| shared.into_inner().run_job(scope));
            }
        }
    }

    /// Translate items until the worklist is empty.
    fn run_job(self: Arc<Self>, scope: &rustc_thread_pool::Scope<'_>) {
        if TRANSLATING.get() {
            // The main thread spawns jobs again soon.
            self.jobs.fetch_sub(1, Ordering::Relaxed);
            return;
        }
        let old_scope = SCOPE.replace(scope as *const _ as *const ());
        let ctx = self.ctxs.lock().unwrap().pop();
        let mut ctx = match ctx {
            Some(ctx) => ctx.0,
            None => TranslateCtx::new_worker(&self),
        };
        while let Some(src) = self.pop() {
            TRANSLATING.set(true);
            ctx.translate_item(&src);
            TRANSLATING.set(false);
            self.done(&ctx, &src);
        }
        self.ctxs.lock().unwrap().push(AssertSend(ctx));
        self.jobs.fetch_sub(1, Ordering::Relaxed);
        self.spawn_jobs();
        SCOPE.set(old_scope);
    }
}
