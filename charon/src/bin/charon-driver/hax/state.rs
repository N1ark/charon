use crate::hax::prelude::*;
use annotate_snippets::Level;
use rustc_middle::ty::{self, TyCtxt};
use std::cell::RefCell;

mod base {
    use crate::hax::prelude::*;
    use itertools::Itertools;
    use rustc_hash::FxHashMap;
    use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
    use rustc_middle::ty;
    use rustc_span::symbol::Symbol;
    use rustc_trait_elaboration::{ElaborationCtx, ItemRefKey, intern::Interner};
    use std::{cell::RefCell, sync::Arc};

    /// Global caches
    #[derive(Default)]
    pub struct GlobalCache<'tcx> {
        /// Per-item cache.
        pub per_item: HashMap<DefId, Rc<RefCell<ItemCache<'tcx>>>>,
        /// The translated definitions, optionally instantiated with generic arguments.
        pub full_defs: HashMap<(DefId, Option<ty::GenericArgsRef<'tcx>>), Arc<FullDef<'tcx>>>,
        /// Cache of parameter-free values, shared by the owners that translate these the same way.
        /// See [`UnderOwnerState::with_cache_for`].
        pub shared: ItemCache<'tcx>,
        /// Map rustc def ids to their hax counterpart.
        pub def_ids: HashMap<RDefId, DefId>,
        /// Data for synthetic items. See the `synthetic_items` module.
        pub synthetic_item_data: HashMap<SyntheticItem, SyntheticItemData<'tcx>>,
        /// Anonymous allocations we turned into globals, in encounter order. Used to keep
        /// the order of globals stable across runs.
        pub anon_allocs: indexmap::IndexSet<RAllocId>,
        /// The types at which we view anonymous allocations.
        pub alloc_types: rustc_const_uneval::AllocTypes<'tcx>,
        /// Cached names and disambiguators for crate names.
        pub disambiguated_crate_names: Option<FxHashMap<CrateNum, (Symbol, u32)>>,
    }

    impl<'tcx> GlobalCache<'tcx> {
        pub fn crate_name(&mut self, tcx: ty::TyCtxt<'tcx>, krate: CrateNum) -> (Symbol, u32) {
            self.disambiguated_crate_names
                .get_or_insert_with(|| {
                    std::iter::once(LOCAL_CRATE)
                        .chain(tcx.crates(()).iter().copied())
                        .into_group_map_by(|&cnum| tcx.crate_name(cnum))
                        .into_iter()
                        .filter(|(_, crates_by_this_name)| crates_by_this_name.len() > 1)
                        .flat_map(|(name, mut crates_by_this_name)| {
                            crates_by_this_name.sort_by_key(|&cnum| {
                                // `tcx.stable_crate_id` isn't actually so stable across machines.
                                // We try our own stability here based on paths.
                                let source_file = tcx
                                    .sess
                                    .source_map()
                                    .span_to_filename(tcx.def_span(cnum.as_def_id()))
                                    .prefer_remapped_unconditionally()
                                    .to_string_lossy()
                                    .into_owned();
                                let extern_paths = if cnum == LOCAL_CRATE {
                                    Vec::new()
                                } else {
                                    tcx.crate_extern_paths(cnum)
                                        .iter()
                                        .map(|path| path.display().to_string())
                                        .collect_vec()
                                };
                                (
                                    cnum != LOCAL_CRATE,
                                    source_file,
                                    extern_paths,
                                    cnum.as_u32(),
                                )
                            });
                            crates_by_this_name.into_iter().enumerate().map(
                                move |(disambiguator, cnum)| (cnum, (name, disambiguator as u32)),
                            )
                        })
                        .collect()
                })
                .get(&krate)
                .copied()
                .unwrap_or_else(|| (tcx.crate_name(krate), 0))
        }
    }

    /// Per-item cache
    #[derive(Default)]
    pub struct ItemCache<'tcx> {
        /// Cache the `Ty` translations.
        pub tys: HashMap<ty::Ty<'tcx>, Ty<'tcx>>,
        /// Cache the `ItemRef` translations. This is fast because `GenericArgsRef` is interned.
        pub item_refs: HashMap<ItemRefKey<'tcx, DefId>, ItemRef<'tcx>>,
        /// Cache of trait refs to resolved trait proofs.
        pub trait_proofs: HashMap<ty::PolyTraitRef<'tcx>, crate::hax::traits::TraitProof<'tcx>>,
        /// Generics for this item, if it is virtual.
        pub virtual_generics: Option<&'tcx ty::Generics>,
        /// The `ParamEnv` of this item, see [`UnderOwnerState::param_env`].
        pub param_env: Option<ty::ParamEnv<'tcx>>,
        /// See [`DefId::identity_args_with_extra_regions`].
        pub identity_args: Option<(ty::GenericArgsRef<'tcx>, Vec<ty::PlaceholderRegion<'tcx>>)>,
        /// The parts of the `FullDef`s of this item that don't depend on generic arguments.
        pub def_info: Option<DefInfo<'tcx>>,
        /// Whether this item uses the shared cache for parameter-free values, see
        /// [`UnderOwnerState::with_cache_for`].
        pub uses_shared_cache: Option<bool>,
    }

    /// The parts of a `FullDef` that don't depend on generic arguments.
    #[derive(Clone, Copy)]
    pub struct DefInfo<'tcx> {
        pub source_span: Option<Span>,
        pub attributes: &'tcx [rustc_hir::Attribute],
        pub visibility: Option<bool>,
        pub lang_item: Option<Symbol>,
        pub diagnostic_item: Option<Symbol>,
    }

    #[derive(Clone)]
    pub struct Base<'tcx> {
        pub ty_interner: &'tcx Interner<'tcx, TyKind<'tcx>>,
        pub trait_proof_interner: &'tcx Interner<'tcx, TraitProofContents<'tcx>>,
        pub item_ref_interner: &'tcx Interner<'tcx, ItemRefContents<'tcx>>,
        pub options: Rc<crate::hax::options::Options>,
        pub cache: Rc<RefCell<GlobalCache<'tcx>>>,
        pub elab_ctx: crate::hax::traits::ElaborationCtx<'tcx, DefId>,
        pub tcx: ty::TyCtxt<'tcx>,
    }

    impl<'tcx> Base<'tcx> {
        pub fn new(
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
            options: crate::hax::options::Options,
            bounds_options: crate::hax::options::BoundsOptions,
        ) -> Self {
            Self {
                tcx,
                ty_interner: Box::leak(Box::default()),
                trait_proof_interner: Box::leak(Box::default()),
                item_ref_interner: Box::leak(Box::default()),
                cache: Default::default(),
                options: Rc::new(options),
                elab_ctx: ElaborationCtx::new(tcx, bounds_options),
            }
        }

        /// Free the interners and the elaboration context, which are otherwise leaked.
        ///
        /// # Safety
        /// No clone of this `Base`, nor anything it produced (types, item refs, trait proofs...),
        /// may be used afterwards.
        pub unsafe fn free(self) {
            unsafe fn free_leaked<T>(value: &T) {
                drop(unsafe { Box::from_raw(value as *const T as *mut T) })
            }
            // The caches point into the interners: drop them first.
            drop(self.cache);
            unsafe {
                free_leaked(self.ty_interner);
                free_leaked(self.trait_proof_interner);
                free_leaked(self.item_ref_interner);
                self.elab_ctx.free();
            }
        }
    }
}

pub use self::base::*;

pub trait BaseState<'tcx>: Sized {
    fn base(&self) -> &Base<'tcx>;

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.base().tcx
    }

    /// Raise an error or warning.
    fn raise(&self, level: Level, span: Span, msg: String) {
        let backtrace = std::backtrace::Backtrace::capture();
        eprintln!("{}", backtrace);
        let dcx = self.tcx().dcx();
        if level == Level::ERROR {
            dcx.span_err(span, msg);
        } else {
            dcx.span_warn(span, msg);
        }
    }

    /// Create a state with the given owner.
    fn with_hax_owner(&self, owner: &DefId) -> StateWithOwner<'tcx> {
        State {
            owner: Owner {
                def_id: owner.clone(),
                cache: self.item_cache(owner),
            },
            base: self.base().clone(),
        }
    }
    /// Create a state with the given owner.
    fn with_rustc_owner(&self, owner_id: RDefId) -> StateWithOwner<'tcx> {
        let owner = &owner_id.sinto(self);
        Self::with_hax_owner(self, owner)
    }

    /// State with only access to the global state.
    fn base_state(&self) -> StateWithBase<'tcx> {
        State {
            base: self.base().clone(),
            owner: (),
        }
    }

    /// Access the global cache. You must not call `sinto` within this function as this will likely
    /// result in `BorrowMut` panics.
    fn with_global_cache<T>(&self, f: impl FnOnce(&mut GlobalCache<'tcx>) -> T) -> T {
        f(&mut self.base().cache.borrow_mut())
    }
    /// The cache for a given item.
    fn item_cache(&self, def_id: &DefId) -> Rc<RefCell<ItemCache<'tcx>>> {
        self.with_global_cache(|cache| cache.per_item.entry(def_id.clone()).or_default().clone())
    }
    /// Access the cache for a given item. You must not call `sinto` within this function as this
    /// will likely result in `BorrowMut` panics.
    fn with_item_cache<T>(&self, def_id: &DefId, f: impl FnOnce(&mut ItemCache<'tcx>) -> T) -> T {
        f(&mut self.item_cache(def_id).borrow_mut())
    }
}

pub trait UnderOwnerState<'tcx>: BaseState<'tcx> {
    fn owner(&self) -> DefId;
    /// The cache of the current owner.
    fn owner_cache(&self) -> &Rc<RefCell<ItemCache<'tcx>>>;

    fn param_env(&self) -> ty::ParamEnv<'tcx> {
        if let Some(param_env) = self.owner_cache().borrow().param_env {
            return param_env;
        }
        let param_env = self.owner().param_env(self);
        self.with_cache(|cache| cache.param_env = Some(param_env));
        param_env
    }
    fn typing_env(&self) -> ty::TypingEnv<'tcx> {
        ty::TypingEnv::new(self.param_env(), ty::TypingMode::PostAnalysis)
    }

    fn as_state_with_owner(&self) -> StateWithOwner<'tcx> {
        State {
            base: self.base().clone(),
            owner: Owner {
                def_id: self.owner(),
                cache: self.owner_cache().clone(),
            },
        }
    }

    /// Access the cache for the current item. You must not call `sinto` within this function as
    /// this will likely result in `BorrowMut` panics.
    fn with_cache<T>(&self, f: impl FnOnce(&mut ItemCache<'tcx>) -> T) -> T {
        f(&mut self.owner_cache().borrow_mut())
    }
    /// Access the cache in which to store the translation of `value` in the current owner.
    ///
    /// The owner only influences the translation through the clauses in scope (for trait
    /// resolution and normalization). These can't apply to a value without (non-lifetime)
    /// parameters, unless they are themselves parameter-free (see
    /// `PredicateSearcher::has_concrete_clauses`). Hence parameter-free values translate the same
    /// in all the owners without such clauses, and we share a cache for them. This is the same
    /// reasoning as for the concrete caches of `rustc_trait_elaboration`.
    ///
    /// You must not call `sinto` within this function as this will likely result in `BorrowMut`
    /// panics.
    fn with_cache_for<T>(
        &self,
        value: impl ty::TypeVisitable<TyCtxt<'tcx>>,
        f: impl FnOnce(&mut ItemCache<'tcx>) -> T,
    ) -> T {
        let uses_shared_cache = match self.with_cache(|cache| cache.uses_shared_cache) {
            Some(b) => b,
            None => {
                let b =
                    self.with_predicate_searcher(|searcher, _| !searcher.has_concrete_clauses());
                self.with_cache(|cache| cache.uses_shared_cache = Some(b));
                b
            }
        };
        if uses_shared_cache && !ty::TypeVisitableExt::has_non_region_param(&value) {
            self.with_global_cache(|cache| f(&mut cache.shared))
        } else {
            self.with_cache(f)
        }
    }
    fn with_predicate_searcher<T>(
        &self,
        f: impl FnOnce(&mut PredicateSearcher<'tcx>, &StateWithBase<'tcx>) -> T,
    ) -> T {
        let base_state = self.base_state();
        let mut predicate_searcher = self
            .base()
            .elab_ctx
            .predicate_searcher_for(&base_state, self.owner());
        f(&mut predicate_searcher, &base_state)
    }
}

#[derive(Clone)]
pub struct State<'tcx, Owner> {
    pub base: Base<'tcx>,
    pub owner: Owner,
}

/// The item whose context we are in, along with its cache.
#[derive(Clone)]
pub struct Owner<'tcx> {
    def_id: DefId,
    cache: Rc<RefCell<ItemCache<'tcx>>>,
}

pub type StateWithBase<'tcx> = State<'tcx, ()>;
pub type StateWithOwner<'tcx> = State<'tcx, Owner<'tcx>>;

impl<'tcx> StateWithBase<'tcx> {
    pub fn new(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        options: crate::hax::options::Options,
        bounds_options: crate::hax::options::BoundsOptions,
    ) -> Self {
        Self {
            base: Base::new(tcx, options, bounds_options),
            owner: (),
        }
    }
}
impl<'tcx, O> BaseState<'tcx> for State<'tcx, O> {
    fn base(&self) -> &Base<'tcx> {
        &self.base
    }
}
impl<'tcx> UnderOwnerState<'tcx> for StateWithOwner<'tcx> {
    fn owner(&self) -> DefId {
        self.owner.def_id.clone()
    }
    fn owner_cache(&self) -> &Rc<RefCell<ItemCache<'tcx>>> {
        &self.owner.cache
    }
}

impl<'tcx, A: BaseState<'tcx>, B> BaseState<'tcx> for (A, B) {
    fn base(&self) -> &Base<'tcx> {
        self.0.base()
    }
}
impl<'tcx, A: UnderOwnerState<'tcx>, B> UnderOwnerState<'tcx> for (A, B) {
    fn owner(&self) -> DefId {
        self.0.owner()
    }
    fn owner_cache(&self) -> &Rc<RefCell<ItemCache<'tcx>>> {
        self.0.owner_cache()
    }
}
