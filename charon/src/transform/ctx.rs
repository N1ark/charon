use crate::ast::bodies::insert_statements;
use crate::ast::*;
use crate::errors::{ErrorCtx, Level, PANIC_NOTE_SHOWN, PANIC_NOTE_SHOWN_BY_US};
use crate::formatter::{FmtCtx, IntoFormatter};
use crate::llbc_ast;
use crate::llbc_ast::FreshIds;
use crate::options::TranslateOptions;
use crate::pretty::FmtWithCtx;
use crate::register_error;
use crate::transform::CowBox;
use crate::ullbc_ast;
use itertools::Itertools;
use rayon::prelude::*;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::cell::RefCell;
use std::sync::atomic::Ordering;
use std::sync::{Mutex, MutexGuard, PoisonError};
use std::{fmt, mem};

/// Simpler context used for rustc-independent code transformation. This only depends on rustc for
/// its error reporting machinery.
pub struct TransformCtx {
    /// The options that control transformation.
    pub options: TranslateOptions,
    /// The translated data.
    pub translated: TranslatedCrate,
    /// Context for tracking and reporting errors.
    pub errors: Mutex<ErrorCtx>,
}

/// An error raised while transforming items in parallel.
enum DeferredError {
    New {
        span: Span,
        msg: String,
        level: Level<'static>,
        /// The `display_key` and the rendering of the error: rendering can be costly, so we do it
        /// in parallel.
        rendered: (u64, String),
    },
    /// An error that the item already raised: we display each error once, so it only counts.
    Repeated,
}

/// What transforming an item in a parallel loop did besides changing the item itself. This is
/// applied in item order once the loop is done, so that the output doesn't depend on scheduling.
#[derive(Default)]
struct ItemEffects {
    errors: Vec<DeferredError>,
    /// The `display_key`s of the errors.
    error_keys: HashSet<u64>,
    /// Globals created while transforming this item. Until the loop is done they have temporary
    /// ids, starting at the first unused global id, and are only known to this item.
    new_globals: Vec<GlobalDecl>,
    /// The message of the panic that interrupted the transformation of this item, if any.
    panic_message: Option<String>,
}

/// Make the panics of items transformed in parallel record their message in the item's effects,
/// instead of printing it right away, so that we print it in order with the item's errors. Call
/// this early, so that it sees all the panics.
pub fn install_panic_hook() {
    static HOOK: std::sync::Once = std::sync::Once::new();
    HOOK.call_once(|| {
        // With a backtrace requested, keep the standard output.
        let capture = std::env::var_os("RUST_BACKTRACE").is_none_or(|v| v == "0");
        let default_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            // The same format as the default hook, except for the thread id.
            let message = || {
                let name = std::thread::current()
                    .name()
                    .unwrap_or("<unnamed>")
                    .to_owned();
                let location = info.location().unwrap();
                let msg = info.payload_as_str().unwrap_or("Box<dyn Any>");
                format!("\nthread '{name}' panicked at {location}:\n{msg}")
            };
            if SILENT_PANICS.get() {
                return;
            }
            let captured = capture
                && ITEM_EFFECTS.with_borrow_mut(|effects| {
                    let Some(effects) = effects else {
                        return false;
                    };
                    effects.panic_message = Some(message());
                    true
                });
            if captured {
                return;
            }
            // Print after what we printed before.
            let _ = crate::errors::finish_printing_in_background();
            if PANIC_NOTE_SHOWN_BY_US.load(Ordering::Relaxed) {
                eprintln!("{}", message());
            } else {
                PANIC_NOTE_SHOWN.store(true, Ordering::Relaxed);
                default_hook(info)
            }
        }));
    });
}

thread_local! {
    static SILENT_PANICS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Run `f` without printing the messages of the panics it causes: the caller handles them.
pub fn without_panic_messages<R>(f: impl FnOnce() -> R) -> R {
    let old = SILENT_PANICS.replace(true);
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    SILENT_PANICS.set(old);
    res.unwrap_or_else(|payload| std::panic::resume_unwind(payload))
}

/// What remains to do for an item after a parallel loop.
struct ParItemOutcome {
    has_errors: bool,
    /// See [`ItemEffects::new_globals`].
    new_globals: Vec<GlobalDecl>,
    /// The fresh block and statement ids created for this item were numbered locally; they must
    /// be renumbered from these.
    first_fresh_ids: Option<FreshIds>,
}

/// How many items the parallel loops that move or copy the items transform at a time.
const PAR_CHUNK: usize = 1024;

/// One value per thread of rayon's pool, e.g. a cache used while transforming items in parallel.
/// Use it from rayon's threads, or when no parallel loop is running.
pub(crate) struct PerThread<T>(Box<[Mutex<T>]>);

impl<T: Default> PerThread<T> {
    pub(crate) fn new() -> Self {
        Self::new_with(Default::default)
    }
}

impl<T> PerThread<T> {
    pub(crate) fn new_with(f: impl Fn() -> T) -> Self {
        Self(
            (0..rayon::current_num_threads())
                .map(|_| Mutex::new(f()))
                .collect(),
        )
    }
    pub(crate) fn get(&self) -> MutexGuard<'_, T> {
        let i = rayon::current_thread_index().unwrap_or(0);
        // A panic while transforming an item is caught and reported for that item; it mustn't
        // break the next items. Values like caches stay valid if their user panics.
        self.0[i].lock().unwrap_or_else(PoisonError::into_inner)
    }
}

thread_local! {
    /// The effects of the item currently being transformed on this thread, if we're inside a
    /// parallel loop.
    static ITEM_EFFECTS: RefCell<Option<ItemEffects>> = const { RefCell::new(None) };
}

/// The pointer metadata of the given global, which may be one of the globals the current item
/// created.
pub(crate) fn global_ptr_metadata(
    krate: &TranslatedCrate,
    id: GlobalDeclId,
) -> Option<ConstantExpr> {
    if let Some(global) = krate.global_decls.get(id) {
        return Some(global.ptr_metadata.clone());
    }
    let idx = id.index().checked_sub(krate.global_decls.slot_count())?;
    ITEM_EFFECTS
        .with_borrow(|effects| Some(effects.as_ref()?.new_globals.get(idx)?.ptr_metadata.clone()))
}

/// A pass that modifies ullbc bodies and can be fused with previous passes so that we run all of
/// them on a given body.
pub trait UllbcPass: Sync {
    /// Whether the pass should run.
    fn should_run(&self, _options: &TranslateOptions) -> bool {
        true
    }

    /// Transform a body.
    fn transform_body(&self, _ctx: &TransformCtx, _body: &mut ullbc_ast::ExprBody) {}

    /// Transform a function declaration. This forwards to `transform_body` by default.
    fn transform_function(&self, ctx: &TransformCtx, decl: &mut FunDecl) {
        if let Some(body) = decl.body.as_unstructured_mut() {
            self.transform_body(ctx, body)
        }
    }

    /// Transform an item. This forwards to `transform_function` by default. A pass that overrides
    /// this to transform other items than functions must say so with
    /// `transforms_non_function_items`.
    fn transform_item(&self, ctx: &TransformCtx, item: ItemRefMut<'_>) {
        if let ItemRefMut::Fun(decl) = item {
            self.transform_function(ctx, decl);
        }
    }

    /// Whether `transform_item` transforms other items than functions.
    fn transforms_non_function_items(&self) -> bool {
        false
    }

    /// Some passes carry function bodies, which must also be transformed. This is called before
    /// the batch of passes starts, with all the passes that come before this one. Rougly only
    /// useful for passes that inline some functions into others.
    fn apply_preceding_passes(
        &mut self,
        _ctx: &mut TransformCtx,
        _passes: &[CowBox<dyn UllbcPass>],
    ) {
    }

    /// Run after all the fused passes in the current block are done.
    fn finalize(&self, _ctx: &mut TransformCtx) {}

    /// The name of the pass, used for debug logging. The default implementation uses the type
    /// name.
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }
}

/// A pass that modifies llbc bodies.
pub trait LlbcPass: Sync {
    /// Whether the pass should run.
    fn should_run(&self, _options: &TranslateOptions) -> bool {
        true
    }

    /// Transform a body.
    fn transform_body(&self, _ctx: &TransformCtx, _body: &mut llbc_ast::ExprBody) {}

    /// Transform a function declaration. This forwards to `transform_body` by default.
    fn transform_function(&self, ctx: &TransformCtx, decl: &mut FunDecl) {
        if let Some(body) = decl.body.as_structured_mut() {
            self.transform_body(ctx, body)
        }
    }

    /// The name of the pass, used for debug logging. The default implementation uses the type
    /// name.
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }
}

/// A pass that modifies each function declaration on its own, whichever kind of body it has.
pub trait FunDeclPass: Sync {
    /// Whether the pass should run.
    fn should_run(&self, _options: &TranslateOptions) -> bool {
        true
    }

    fn transform_function(&self, options: &TranslateOptions, decl: &mut FunDecl);

    /// The name of the pass, used for debug logging. The default implementation uses the type
    /// name.
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }
}

/// A pass that transforms the crate data.
pub trait TransformPass: Sync {
    /// Whether the pass should run.
    fn should_run(&self, _options: &TranslateOptions) -> bool {
        true
    }

    fn transform_ctx(&self, ctx: &mut TransformCtx);

    /// The name of the pass, used for debug logging. The default implementation uses the type
    /// name.
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }
}

impl TransformCtx {
    /// The error context. A panic while it is in use (caught for the current item) leaves it
    /// usable.
    pub fn error_ctx(&self) -> MutexGuard<'_, ErrorCtx> {
        self.errors.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub(crate) fn has_errors(&self) -> bool {
        self.error_ctx().has_errors()
    }

    /// Span an error and register the error.
    pub(crate) fn span_err(&self, span: Span, msg: &str, level: Level<'static>) -> Error {
        let deferred = ITEM_EFFECTS.with_borrow_mut(|effects| {
            let effects = effects.as_mut()?;
            let key = ErrorCtx::display_key(span, msg, &level);
            let error = Error::new(span, msg.to_owned());
            if effects.error_keys.insert(key) {
                let rendered = error.render(&self.translated, level.clone());
                effects.errors.push(DeferredError::New {
                    span,
                    msg: msg.to_owned(),
                    level: level.clone(),
                    rendered: (key, rendered),
                });
            } else {
                effects.errors.push(DeferredError::Repeated);
            }
            Some(error)
        });
        deferred.unwrap_or_else(|| {
            self.error_ctx()
                .span_err(&self.translated, span, msg, level)
        })
    }

    /// Create a global holding a promoted constant of the function currently being transformed in
    /// a parallel loop. Until the end of the loop the global has a temporary id and is only known
    /// to this function; it is then added to the crate and named `{promoted_const#N}` under the
    /// function's name.
    pub(crate) fn add_promoted_global(
        &self,
        f: impl FnOnce(GlobalDeclId) -> GlobalDecl,
    ) -> GlobalDeclId {
        ITEM_EFFECTS.with_borrow_mut(|effects| {
            let new_globals = &mut effects
                .as_mut()
                .expect("globals can only be added while transforming items in parallel")
                .new_globals;
            let id = GlobalDeclId::from_usize(
                self.translated.global_decls.slot_count() + new_globals.len(),
            );
            new_globals.push(f(id));
            id
        })
    }

    pub(crate) fn opacity_for_name(&self, name: &Name) -> ItemOpacity {
        self.options.opacity_for_name(&self.translated, name)
    }

    /// Run an item transformation with its error context, reporting any panic on that item.
    pub(crate) fn with_def_id(
        &mut self,
        def_id: impl Into<ItemId>,
        def_id_is_local: bool,
        span: Span,
        f: impl FnOnce(&mut Self),
    ) {
        let def_id = def_id.into();
        let mut errors = self.error_ctx();
        let current_def_id = errors.def_id.replace(def_id);
        let current_def_id_is_local = mem::replace(&mut errors.def_id_is_local, def_id_is_local);
        drop(errors); // important: release the lock
        if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(self))).is_err() {
            let name = self
                .translated
                .item_name(def_id)
                .to_string_with_ctx(&self.into_fmt());
            register_error!(
                self,
                span,
                "Thread panicked while transforming item `{name}`."
            );
        }
        let mut errors = self.error_ctx();
        errors.def_id = current_def_id;
        errors.def_id_is_local = current_def_id_is_local;
    }

    /// Run `f` on each of `items` in parallel. Each call behaves as if run inside `with_def_id`
    /// for the item described by `meta`: errors are attributed to it and panics are caught. The
    /// errors are reported in order once all the items are done. The caller must then apply the
    /// returned effects of each item, in order.
    ///
    /// The effects of an item are tracked per thread, so `f` must not itself run work in
    /// parallel.
    fn par_with_def_ids<T: Send>(
        &self,
        items: &mut [T],
        meta: impl Fn(&T) -> (ItemId, bool, Span) + Sync,
        f: impl Fn(&Self, &mut T) + Sync,
    ) -> Vec<ParItemOutcome> {
        install_panic_hook();
        let outcomes: Vec<(ItemEffects, bool, FreshIds)> = items
            .par_iter_mut()
            .map(|item| {
                // Save the current effects in case rayon runs this inside another item's job.
                let outer = ITEM_EFFECTS.replace(Some(ItemEffects::default()));
                let (panicked, fresh_ids) = FreshIds::number_locally(|| {
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(self, item)))
                        .is_err()
                });
                let effects = ITEM_EFFECTS.replace(outer).unwrap();
                (effects, panicked, fresh_ids)
            })
            .collect();
        let fresh_ids = FreshIds::reserve(&outcomes.iter().map(|(_, _, ids)| *ids).collect_vec());
        let mut errors = self.error_ctx();
        items
            .iter()
            .zip(outcomes)
            .zip(fresh_ids)
            .map(|((item, (effects, panicked, _)), first_fresh_ids)| {
                let (def_id, def_id_is_local, span) = meta(item);
                if !effects.errors.is_empty() || panicked {
                    let current_def_id = errors.def_id.replace(def_id);
                    let current_def_id_is_local =
                        mem::replace(&mut errors.def_id_is_local, def_id_is_local);
                    for err in effects.errors {
                        match err {
                            DeferredError::New {
                                span,
                                msg,
                                level,
                                rendered,
                            } => {
                                errors.span_err_rendered(
                                    &self.translated,
                                    span,
                                    &msg,
                                    level,
                                    Some(rendered),
                                );
                            }
                            DeferredError::Repeated => errors.error_count += 1,
                        }
                    }
                    if panicked {
                        let name = self
                            .translated
                            .item_name(def_id)
                            .to_string_with_ctx(&self.into_fmt());
                        let msg = format!("Thread panicked while transforming item `{name}`.");
                        errors.report_panic(&self.translated, span, &msg, effects.panic_message);
                    }
                    errors.def_id = current_def_id;
                    errors.def_id_is_local = current_def_id_is_local;
                }
                ParItemOutcome {
                    has_errors: errors.item_has_errors(def_id),
                    new_globals: effects.new_globals,
                    first_fresh_ids,
                }
            })
            .collect()
    }

    /// Add the globals created while transforming function `fun_id` in a parallel loop to the
    /// crate, and update their ids in `decl`. `temp_ids` is the first temporary id, i.e. the
    /// number of global slots during the loop. `promoted_counts` maps names to the number of
    /// promoted constants named after them; it is computed on first use.
    fn add_promoted_globals(
        &mut self,
        temp_ids: usize,
        fun_id: FunDeclId,
        decl: &mut impl AstVisitable,
        globals: Vec<GlobalDecl>,
        promoted_counts: &mut Option<HashMap<PathElems, usize>>,
    ) {
        if globals.is_empty() {
            return;
        }
        let fun_name = self.translated.item_name(fun_id).clone();
        let promoted_counts = promoted_counts.get_or_insert_with(|| {
            let mut counts: HashMap<PathElems, usize> = HashMap::default();
            for (last, prefix) in self
                .translated
                .item_names
                .values()
                .filter_map(|n| n.name.split_last())
            {
                if matches!(last, PathElem::Builtin(BuiltinPathElem::PromotedConst, _)) {
                    *counts.entry(PathElems::new(prefix.to_vec())).or_default() += 1;
                }
            }
            counts
        });
        let promoted_count = promoted_counts.entry(fun_name.name.clone()).or_default();
        let first_promoted = mem::replace(promoted_count, *promoted_count + globals.len());
        let mut new_ids = Vec::with_capacity(globals.len());
        for (i, mut global) in globals.into_iter().enumerate() {
            let mut name = fun_name.clone();
            name.name.push(PathElem::Builtin(
                BuiltinPathElem::PromotedConst,
                Disambiguator::new(first_promoted + i),
            ));
            global.item_meta.name = name.clone();
            let id = self.translated.global_decls.push_with(|id| {
                global.def_id = id;
                global
            });
            self.translated.item_names.insert(id.into(), name);
            new_ids.push(id);
        }
        #[derive(Visitor)]
        struct RenameTempIds<'a> {
            temp_ids: usize,
            new_ids: &'a [GlobalDeclId],
            /// The bloom filter of the temporary ids.
            temp_bloom: ItemBloom,
        }
        impl VisitAstMut for RenameTempIds<'_> {
            fn visit_with_cached_type_info<T: AstVisitable + HashConsable>(
                &mut self,
                x: &mut HashConsed<WithCachedTypeInfo<T>>,
            ) -> ControlFlow<Self::Break> {
                // Avoid cloning and re-interning the values that can't mention a temporary id.
                if !x.type_info().items.intersects(self.temp_bloom) {
                    return ControlFlow::Continue(());
                }
                self.visit_inner(x)
            }
            fn enter_global_decl_id(&mut self, id: &mut GlobalDeclId) {
                if let Some(idx) = id.index().checked_sub(self.temp_ids) {
                    *id = self.new_ids[idx];
                }
            }
        }
        let temp_bloom = (temp_ids..temp_ids + new_ids.len())
            .map(|i| ItemBloom::of(GlobalDeclId::from_usize(i)))
            .collect();
        let _ = RenameTempIds {
            temp_ids,
            new_ids: &new_ids,
            temp_bloom,
        }
        .visit(decl);
    }

    /// Mutably iterate over the function declarations in parallel, without access to the rest of
    /// the crate.
    pub(crate) fn par_for_each_fun_decl_mut(
        &mut self,
        f: impl Fn(&TranslateOptions, &mut FunDecl) + Sync,
    ) {
        let mut fun_decls = mem::take(&mut self.translated.fun_decls);
        let mut decls: Vec<&mut FunDecl> = fun_decls.iter_mut().collect();
        let outcomes = self.par_with_def_ids(
            &mut decls,
            |decl| {
                (
                    decl.def_id.into(),
                    decl.item_meta.is_local,
                    decl.item_meta.span,
                )
            },
            |ctx, decl| f(&ctx.options, decl),
        );
        decls
            .par_iter_mut()
            .zip(&outcomes)
            .for_each(|(decl, outcome)| decl.body.globalize_fresh_ids(outcome.first_fresh_ids));
        for (decl, outcome) in decls.into_iter().zip(outcomes) {
            decl.item_meta.has_errors |= outcome.has_errors;
            assert!(outcome.new_globals.is_empty());
        }
        self.translated.fun_decls = fun_decls;
    }

    /// Mutably iterate over the function declarations in parallel. `f` works on a copy of each
    /// declaration; while it runs the crate contains this declaration with an `Opaque` body. We go
    /// through the declarations in chunks of `PAR_CHUNK`.
    pub(crate) fn par_for_each_fun_decl(&mut self, f: impl Fn(&Self, &mut FunDecl) + Sync) {
        let count = self.translated.fun_decls.iter().count();
        let mut promoted_counts = None;
        for start in (0..count).step_by(PAR_CHUNK) {
            let mut decls: Vec<FunDecl> = self
                .translated
                .fun_decls
                .iter_mut()
                .skip(start)
                .take(PAR_CHUNK)
                .collect_vec()
                .into_par_iter()
                .map(|decl| {
                    let body = mem::replace(&mut decl.body, Body::Opaque);
                    let mut copy = decl.clone();
                    if !body.has_contents() {
                        // Keep showing the bodies that aren't moved (e.g. `Body::Intrinsic`).
                        decl.body = body.clone();
                    }
                    copy.body = body;
                    copy
                })
                .collect();
            let temp_ids = self.translated.global_decls.slot_count();
            let outcomes = self.par_with_def_ids(
                &mut decls,
                |decl| {
                    (
                        decl.def_id.into(),
                        decl.item_meta.is_local,
                        decl.item_meta.span,
                    )
                },
                |ctx, decl| f(ctx, decl),
            );
            decls
                .par_iter_mut()
                .zip(&outcomes)
                .for_each(|(decl, outcome)| decl.body.globalize_fresh_ids(outcome.first_fresh_ids));
            for (decl, outcome) in decls.iter_mut().zip(outcomes) {
                self.add_promoted_globals(
                    temp_ids,
                    decl.def_id,
                    decl,
                    outcome.new_globals,
                    &mut promoted_counts,
                );
                decl.item_meta.has_errors |= outcome.has_errors;
            }
            // Put the transformed declarations back, dropping the copies in parallel.
            self.translated
                .fun_decls
                .iter_mut()
                .skip(start)
                .take(PAR_CHUNK)
                .collect_vec()
                .into_par_iter()
                .zip(decls)
                .for_each(|(slot, decl)| *slot = decl);
        }
    }

    /// Mutably iterate in parallel over the items for which `select` returns true, like
    /// `for_each_item_mut`. We go through these items in chunks of `PAR_CHUNK`; the items of the
    /// current chunk are missing from the crate while `f` runs, so `f` must not look at them
    /// through `ctx`.
    pub(crate) fn par_for_each_item_mut_where(
        &mut self,
        select: impl Fn(ItemId) -> bool,
        f: impl Fn(&Self, ItemRefMut<'_>) + Sync,
    ) {
        let ids = self
            .translated
            .all_ids()
            .filter(|&id| select(id))
            .collect_vec();
        for ids in ids.chunks(PAR_CHUNK) {
            let mut items: Vec<(ItemId, ItemByVal)> = ids
                .iter()
                .filter_map(|&id| Some((id, self.translated.remove_item_temporarily(id)?)))
                .collect();
            let outcomes = self.par_with_def_ids(
                &mut items,
                |(id, item)| {
                    let meta = item.as_ref().item_meta();
                    (*id, meta.is_local, meta.span)
                },
                |ctx, (_, item)| f(ctx, item.as_mut()),
            );
            for ((id, mut item), outcome) in items.into_iter().zip(outcomes) {
                assert!(outcome.new_globals.is_empty() && outcome.first_fresh_ids.is_none());
                item.as_mut().item_meta().has_errors |= outcome.has_errors;
                self.translated.put_item_back(id, item);
            }
        }
    }

    /// Like `par_for_each_item_mut_where`, except that `f` transforms copies of the items while
    /// the originals stay in the crate, so that `f` can look at any item through `ctx`. The copies
    /// then replace the originals.
    pub(crate) fn par_for_each_item_copy_where(
        &mut self,
        select: impl Fn(ItemId) -> bool,
        f: impl Fn(&Self, ItemRefMut<'_>) + Sync,
    ) {
        let mut items: Vec<(ItemId, ItemByVal)> = self
            .translated
            .all_ids()
            .filter(|&id| select(id))
            .filter_map(|id| Some((id, self.translated.get_item(id)?.to_owned())))
            .collect();
        let outcomes = self.par_with_def_ids(
            &mut items,
            |(id, item)| {
                let meta = item.as_ref().item_meta();
                (*id, meta.is_local, meta.span)
            },
            |ctx, (_, item)| f(ctx, item.as_mut()),
        );
        for ((id, mut item), outcome) in items.into_iter().zip(outcomes) {
            assert!(outcome.new_globals.is_empty() && outcome.first_fresh_ids.is_none());
            item.as_mut().item_meta().has_errors |= outcome.has_errors;
            self.translated.remove_item_temporarily(id);
            self.translated.put_item_back(id, item);
        }
    }

    /// Same as `for_each_item_mut`, for an `f` that only looks at the trait declarations of the
    /// crate. We transform the type declarations in parallel, then the trait declarations one by
    /// one, then the other items in parallel; the order of the iteration is the same as with
    /// `for_each_item_mut` hence so is what `f` sees.
    pub(crate) fn par_for_each_item_mut_reading_traits(
        &mut self,
        f: impl Fn(&Self, ItemRefMut<'_>) + Sync,
    ) {
        self.par_for_each_item_mut_where(|id| id.is_type(), &f);
        self.for_each_item_mut_where(|id| id.is_trait_decl(), |ctx, item| f(ctx, item));
        self.par_for_each_item_mut_where(|id| !id.is_type() && !id.is_trait_decl(), &f);
    }

    /// Run `f` on each item in parallel, with shared access to the whole crate, and return its
    /// results in item order. Errors are reported as with `for_each_item_mut`.
    pub(crate) fn par_for_each_item<R: Send>(
        &mut self,
        f: impl Fn(&Self, ItemRef<'_>) -> R + Sync,
    ) -> Vec<(ItemId, Option<R>)> {
        let mut results: Vec<(ItemId, Option<R>)> = self
            .translated
            .all_ids()
            .filter(|id| self.translated.get_item(*id).is_some())
            .map(|id| (id, None))
            .collect();
        let outcomes = self.par_with_def_ids(
            &mut results,
            |(id, _)| {
                let meta = self.translated.get_item(*id).unwrap().item_meta();
                (*id, meta.is_local, meta.span)
            },
            |ctx, (id, result)| *result = Some(f(ctx, ctx.translated.get_item(*id).unwrap())),
        );
        for ((id, _), outcome) in results.iter().zip(outcomes) {
            assert!(outcome.new_globals.is_empty() && outcome.first_fresh_ids.is_none());
            if let Some(mut item) = self.translated.get_item_mut(*id) {
                item.item_meta().has_errors |= outcome.has_errors;
            }
        }
        results
    }

    /// Same as `self.translated.drive_mut(visitor)`, except that the items are visited in
    /// parallel, each with the visitor of the thread it runs on. Only for visitors whose effect on
    /// a value doesn't depend on what they visited before.
    pub(crate) fn par_drive_mut<V: VisitAstMut + Send>(&mut self, visitors: &PerThread<V>) {
        let krate = &mut self.translated;
        let items = (
            mem::take(&mut krate.type_decls),
            mem::take(&mut krate.fun_decls),
            mem::take(&mut krate.global_decls),
            mem::take(&mut krate.trait_decls),
            mem::take(&mut krate.trait_impls),
        );
        let _ = krate.drive_mut(&mut *visitors.get());
        (
            krate.type_decls,
            krate.fun_decls,
            krate.global_decls,
            krate.trait_decls,
            krate.trait_impls,
        ) = items;
        krate
            .all_items_mut()
            .collect_vec()
            .into_par_iter()
            .for_each(|mut item| {
                let _ = item.drive_mut(&mut *visitors.get());
            });
    }

    /// Mutably iterate over the type declarations.
    /// Warning: each inspected type declaration becomes inaccessible from `ctx` during the course
    /// of this function.
    pub(crate) fn for_each_type_decl(&mut self, mut f: impl FnMut(&mut Self, &mut TypeDecl)) {
        let type_ids = self.translated.type_decls.all_indices();
        for id in type_ids {
            if let Some(mut decl) = self.translated.type_decls.remove(id) {
                let type_decl_id = decl.def_id;
                let is_local = decl.item_meta.is_local;
                let span = decl.item_meta.span;
                self.with_def_id(type_decl_id, is_local, span, |ctx| f(ctx, &mut decl));
                decl.item_meta.has_errors |= self.error_ctx().item_has_errors(type_decl_id);
                self.translated.type_decls.set_slot(id, decl);
            }
        }
    }

    /// Iterate mutably over all items, keeping access to `self`. To make this work, we move out
    /// each item before iterating over it. Items added during traversal will not be iterated over.
    pub fn for_each_item_mut(&mut self, f: impl for<'a> FnMut(&'a mut Self, ItemRefMut<'a>)) {
        self.for_each_item_mut_where(|_| true, f)
    }

    /// Same as `for_each_item_mut`, on the items for which `select` returns true.
    pub fn for_each_item_mut_where(
        &mut self,
        select: impl Fn(ItemId) -> bool,
        mut f: impl for<'a> FnMut(&'a mut Self, ItemRefMut<'a>),
    ) {
        for id in self.translated.all_ids().filter(|&id| select(id)) {
            if let Some(mut decl) = self.translated.remove_item_temporarily(id) {
                let is_local = decl.as_ref().item_meta().is_local;
                let span = decl.as_ref().item_meta().span;
                self.with_def_id(id, is_local, span, |ctx| f(ctx, decl.as_mut()));
                decl.as_mut().item_meta().has_errors |= self.error_ctx().item_has_errors(id);
                self.translated.put_item_back(id, decl);
            }
        }
    }
}

impl<'a> IntoFormatter for &'a TransformCtx {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        self.translated.into_fmt()
    }
}

impl fmt::Display for TransformCtx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.translated.fmt_with_ctx(&self.into_fmt(), f)
    }
}

/// A helper trait that captures common operations in body transformation.
pub trait BodyTransformCtx: Sized {
    fn get_crate(&self) -> &TranslatedCrate;
    fn get_options(&self) -> &TranslateOptions;
    fn get_params(&self) -> &GenericParams;
    fn get_locals_mut(&mut self) -> &mut Locals;

    fn insert_storage_live_stmt(&mut self, local: LocalId);
    fn insert_storage_dead_stmt(&mut self, local: LocalId);
    fn insert_assn_stmt(&mut self, place: Place, rvalue: Rvalue);

    fn to_fmt(&self) -> FmtCtx<'_> {
        self.get_crate().into_fmt()
    }

    /// Create a local & return the place pointing to it
    fn fresh_var(&mut self, name: Option<String>, ty: Ty) -> Place {
        let var = self.get_locals_mut().new_var(name, ty);
        self.insert_storage_live_stmt(var.local_id().unwrap());
        var
    }

    /// Assign an rvalue to a place, unless the rvalue is a move in which case we just use the
    /// moved place.
    fn rval_to_place(&mut self, rvalue: Rvalue, ty: Ty) -> Place {
        if let Rvalue::Use(Operand::Move(place), WithRetag::No) = rvalue {
            place
        } else {
            let var = self.fresh_var(None, ty);
            self.insert_assn_stmt(var.clone(), rvalue);
            var
        }
    }

    /// When `from_end` is true, we need to compute `len(p) - last_arg` instead of just using `last_arg`.
    /// Otherwise, we simply return `last_arg`.
    /// New local variables are created as needed.
    ///
    /// The `last_arg` is either the `offset` for `Index` or the `to` for `Subslice` for the projections.
    fn compute_subslice_end_idx(
        &mut self,
        len_place: &Place,
        last_arg: Operand,
        from_end: bool,
    ) -> Operand {
        if from_end {
            let len = match len_place.ty().kind() {
                TyKind::Array(_, len, _) => Operand::Const(len.clone()),
                TyKind::Slice(..) => self.compute_place_metadata(len_place),
                _ => panic!(
                    "called `compute_subslice_end_idx` on something that isn't an array or slice: {:?}",
                    len_place.ty()
                ),
            };
            // `storage_live(index_var)`
            // `index_var = len - last_arg`
            let index_var = self.fresh_var(None, Ty::mk_usize());
            self.insert_assn_stmt(
                index_var.clone(),
                Rvalue::BinaryOp(BinOp::Sub(OverflowMode::UB), len, last_arg),
            );
            Operand::Read(index_var)
        } else {
            last_arg
        }
    }

    fn is_sized_type_var(&mut self, ty: &Ty) -> bool {
        match ty.kind() {
            TyKind::TypeVar(..) => {
                if self.get_options().hide_marker_traits {
                    // If we're hiding `Sized`, let's consider everything to be sized.
                    return true;
                }
                let params = self.get_params();
                for clause in &params.trait_clauses {
                    let tref = clause.trait_.clone().erase();
                    // Check if it is `Sized<T>`
                    if tref.generics.types[0] == *ty
                        && self
                            .get_crate()
                            .trait_decls
                            .get(tref.id)
                            .and_then(|decl| decl.item_meta.lang_item.as_ref())
                            == Some(&from_rustc::LangItem::Sized)
                    {
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// Emit statements that compute the metadata of the given place. Returns an operand containing the
    /// metadata value.
    ///
    /// E.g., for:
    /// ```ignore
    /// let x = &(*ptr).field;
    /// ```
    /// if `(*ptr).field` is a DST like `[i32]`, this will get the metadata from the appropriate
    /// pointer:
    /// ```ignore
    /// let len = ptr.metadata;
    /// ```
    /// and return `Operand::Move(len)`.
    ///
    fn compute_place_metadata(&mut self, place: &Place) -> Operand {
        /// Compute the metadata for a place. Return `None` if the place has no metadata.
        fn compute_place_metadata_inner<T: BodyTransformCtx>(
            ctx: &mut T,
            place: &Place,
            metadata_ty: &Ty,
        ) -> Option<Operand> {
            let (subplace, proj) = match &place.kind {
                PlaceKind::Local(_) => return None,
                PlaceKind::Global(gref) => {
                    return global_ptr_metadata(ctx.get_crate(), gref.id).map(Operand::Const);
                }
                PlaceKind::Projection(proj) => (&proj.0, &proj.1),
            };
            match proj {
                // The outermost deref we encountered gives us the metadata of the place.
                ProjectionElem::Deref => {
                    let metadata_place = subplace
                        .clone()
                        .project(ProjectionElem::PtrMetadata, metadata_ty.clone());
                    Some(Operand::Read(metadata_place))
                }
                ProjectionElem::Field { .. } => {
                    compute_place_metadata_inner(ctx, subplace, metadata_ty)
                }
                // The pointee of an offset is sized, hence no metadata.
                ProjectionElem::Offset { .. } => None,
                // Indexing for array & slice will only result in sized types, hence no metadata
                ProjectionElem::Index { .. } => None,
                // Ptr metadata is always sized.
                ProjectionElem::PtrMetadata => None,
                // A subslice of an array whose bounds are known at compile-time.
                // FIXME: track that distinction in `ProjectionElem::Subslice` instead.
                ProjectionElem::Subslice { .. } if place.ty.kind().is_array() => None,
                // Otherwise the subslice is a slice, whose metadata is its length `to` - `from`.
                ProjectionElem::Subslice { from, to, from_end } => {
                    let to_idx = ctx.compute_subslice_end_idx(subplace, *to.clone(), *from_end);
                    let diff_place = ctx.fresh_var(None, Ty::mk_usize());
                    ctx.insert_assn_stmt(
                        diff_place.clone(),
                        // Overflow is UB and should have been prevented by a bound check beforehand.
                        Rvalue::BinaryOp(BinOp::Sub(OverflowMode::UB), to_idx, *from.clone()),
                    );
                    Some(Operand::Read(diff_place))
                }
            }
        }
        trace!(
            "getting ptr metadata for place: {}",
            place.with_ctx(&self.to_fmt())
        );
        let metadata_ty = place.ty().get_ptr_metadata(self.get_crate()).into_type();
        if metadata_ty.is_unit()
            || matches!(metadata_ty.kind(), TyKind::PtrMetadata(ty) if self.is_sized_type_var(ty))
        {
            // If the type var is known to be `Sized`, then no metadata is needed
            return Operand::mk_const_unit();
        }
        trace!(
            "computed metadata type: {}",
            metadata_ty.with_ctx(&self.to_fmt())
        );
        compute_place_metadata_inner(self, place, &metadata_ty)
            .unwrap_or_else(Operand::mk_const_unit)
    }

    /// The projection to the place of type `output_ty` located `count * size_of::<ty>()` bytes
    /// after the current place, or `count` bytes if `ty` is `None` (see `ProjectionElem::Offset`).
    /// `output_is_sized` is the proof that `output_ty` is sized.
    fn offset_projection(
        &mut self,
        count: Operand,
        ty: Option<&Ty>,
        in_bounds: bool,
        output_ty: Ty,
        ty_is_sized: Option<TraitRef>,
    ) -> ProjectionElem {
        let bytes = match ty {
            None => count,
            Some(ty) => {
                let count_ty = count.ty().clone();
                let size =
                    ConstantExpr::new(ConstantExprKind::SizeOf(ty.clone()), count_ty.clone());
                let mode = if in_bounds {
                    OverflowMode::UB
                } else {
                    OverflowMode::Wrap
                };
                let rval = Rvalue::BinaryOp(BinOp::Mul(mode), count, Operand::Const(size));
                Operand::Read(self.rval_to_place(rval, count_ty))
            }
        };
        ProjectionElem::Offset {
            bytes: Box::new(bytes),
            in_bounds,
            ty: output_ty,
            ty_is_sized,
        }
    }

    /// Create a `&` borrow of the place.
    fn borrow(&mut self, place: Place, kind: BorrowKind) -> Rvalue {
        let ptr_metadata = self.compute_place_metadata(&place);
        Rvalue::Ref {
            place,
            kind,
            ptr_metadata,
        }
    }
    /// Create a `&raw` borrow of the place.
    fn raw_borrow(&mut self, place: Place, kind: RefKind) -> Rvalue {
        let ptr_metadata = self.compute_place_metadata(&place);
        Rvalue::RawPtr {
            place,
            kind,
            ptr_metadata,
        }
    }

    /// Store a `&` borrow of the place into a new place.
    fn borrow_to_new_var(&mut self, place: Place, kind: BorrowKind, name: Option<String>) -> Place {
        let ref_ty = TyKind::Ref(Region::Erased, place.ty().clone(), kind.into()).into_ty();
        let target_place = self.fresh_var(name, ref_ty);
        let rvalue = self.borrow(place, kind);
        self.insert_assn_stmt(target_place.clone(), rvalue);
        target_place
    }
    /// Store a `&raw` borrow of the place into a new place.
    fn raw_borrow_to_new_var(
        &mut self,
        place: Place,
        kind: RefKind,
        name: Option<String>,
    ) -> Place {
        let ref_ty = TyKind::RawPtr(place.ty().clone(), kind).into_ty();
        let target_place = self.fresh_var(name, ref_ty);
        let rvalue = self.raw_borrow(place, kind);
        self.insert_assn_stmt(target_place.clone(), rvalue);
        target_place
    }
}

pub struct UllbcStatementTransformCtx<'a> {
    pub ctx: &'a TransformCtx,
    pub params: &'a GenericParams,
    pub def_id: &'a FunDeclId,
    pub locals: &'a mut Locals,
    /// Span of the statement being explored
    pub span: Span,
    /// Statements to prepend to the statement currently being explored.
    pub statements: Vec<ullbc_ast::Statement>,
}

impl BodyTransformCtx for UllbcStatementTransformCtx<'_> {
    fn get_crate(&self) -> &TranslatedCrate {
        &self.ctx.translated
    }
    fn get_options(&self) -> &TranslateOptions {
        &self.ctx.options
    }
    fn get_params(&self) -> &GenericParams {
        self.params
    }
    fn get_locals_mut(&mut self) -> &mut Locals {
        self.locals
    }

    fn insert_storage_live_stmt(&mut self, local: LocalId) {
        self.statements.push(ullbc_ast::Statement::new(
            self.span,
            ullbc_ast::StatementKind::StorageLive(local),
        ));
    }

    fn insert_assn_stmt(&mut self, place: Place, rvalue: Rvalue) {
        self.statements.push(ullbc_ast::Statement::new(
            self.span,
            ullbc_ast::StatementKind::assign(place, rvalue),
        ));
    }

    fn insert_storage_dead_stmt(&mut self, local: LocalId) {
        self.statements.push(ullbc_ast::Statement::new(
            self.span,
            ullbc_ast::StatementKind::StorageDead(local),
        ));
    }
}

pub struct LlbcStatementTransformCtx<'a> {
    pub ctx: &'a TransformCtx,
    pub params: &'a GenericParams,
    pub locals: &'a mut Locals,
    /// Span of the statement being explored
    pub span: Span,
    /// Statements to prepend to the statement currently being explored.
    pub statements: Vec<llbc_ast::Statement>,
}

impl BodyTransformCtx for LlbcStatementTransformCtx<'_> {
    fn get_crate(&self) -> &TranslatedCrate {
        &self.ctx.translated
    }
    fn get_options(&self) -> &TranslateOptions {
        &self.ctx.options
    }
    fn get_params(&self) -> &GenericParams {
        self.params
    }
    fn get_locals_mut(&mut self) -> &mut Locals {
        self.locals
    }

    fn insert_storage_live_stmt(&mut self, local: LocalId) {
        self.statements.push(llbc_ast::Statement::new(
            self.span,
            llbc_ast::StatementKind::StorageLive(local),
        ));
    }

    fn insert_assn_stmt(&mut self, place: Place, rvalue: Rvalue) {
        self.statements.push(llbc_ast::Statement::new(
            self.span,
            llbc_ast::StatementKind::Assign(place, Box::new(rvalue)),
        ));
    }

    fn insert_storage_dead_stmt(&mut self, local: LocalId) {
        self.statements.push(llbc_ast::Statement::new(
            self.span,
            llbc_ast::StatementKind::StorageDead(local),
        ));
    }
}

impl FunDecl {
    pub fn transform_ullbc_statements(
        &mut self,
        ctx: &TransformCtx,
        mut f: impl FnMut(&mut UllbcStatementTransformCtx, &mut ullbc_ast::Statement),
    ) {
        if let Some(body) = self.body.as_unstructured_mut() {
            let mut ctx = UllbcStatementTransformCtx {
                ctx,
                params: &self.generics,
                def_id: &self.def_id,
                locals: &mut body.locals,
                span: self.item_meta.span,
                statements: Vec::new(),
            };
            body.body.iter_mut().for_each(|block| {
                let mut to_insert = Vec::new();
                for (i, st) in block.statements.iter_mut().enumerate() {
                    ctx.span = st.span;
                    f(&mut ctx, st);
                    if !ctx.statements.is_empty() {
                        to_insert.push((i, mem::take(&mut ctx.statements)));
                    }
                }
                insert_statements(&mut block.statements, to_insert);
            });
        }
    }

    pub fn transform_ullbc_terminators(
        &mut self,
        ctx: &TransformCtx,
        mut f: impl FnMut(&mut UllbcStatementTransformCtx, &mut ullbc_ast::Terminator),
    ) {
        if let Some(body) = self.body.as_unstructured_mut() {
            let mut ctx = UllbcStatementTransformCtx {
                ctx,
                params: &self.generics,
                def_id: &self.def_id,
                locals: &mut body.locals,
                span: self.item_meta.span,
                statements: Vec::new(),
            };
            body.body.iter_mut().for_each(|block| {
                ctx.span = block.terminator.span;
                ctx.statements = mem::take(&mut block.statements);
                f(&mut ctx, &mut block.terminator);
                block.statements = mem::take(&mut ctx.statements);
            });
        }
    }

    pub fn transform_ullbc_operands(
        &mut self,
        ctx: &TransformCtx,
        mut f: impl FnMut(&mut UllbcStatementTransformCtx, &mut Operand),
    ) {
        self.transform_ullbc_statements(ctx, |ctx, st| {
            st.kind.dyn_visit_in_body_mut(|op: &mut Operand| f(ctx, op));
        });
        self.transform_ullbc_terminators(ctx, |ctx, st| {
            st.kind.dyn_visit_in_body_mut(|op: &mut Operand| f(ctx, op));
        });
    }

    pub fn transform_llbc_statements(
        &mut self,
        ctx: &TransformCtx,
        mut f: impl FnMut(&mut LlbcStatementTransformCtx, &mut llbc_ast::Statement),
    ) {
        if let Some(body) = self.body.as_structured_mut() {
            let mut ctx = LlbcStatementTransformCtx {
                ctx,
                locals: &mut body.locals,
                statements: Vec::new(),
                span: self.item_meta.span,
                params: &self.generics,
            };
            body.body.visit_blocks_bwd(|block: &mut llbc_ast::Block| {
                let mut to_insert = Vec::new();
                for (i, st) in block.statements.iter_mut().enumerate() {
                    ctx.span = st.span;
                    f(&mut ctx, st);
                    if !ctx.statements.is_empty() {
                        to_insert.push((i, mem::take(&mut ctx.statements)));
                    }
                }
                insert_statements(&mut block.statements, to_insert);
            })
        }
    }
}
