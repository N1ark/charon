use rustc_data_structures::sharded::ShardedHashMap;
use rustc_data_structures::sync::{Lock, LockGuard};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::traits::CodegenObligationError;
use rustc_middle::ty::{self, TypeVisitableExt};
use rustc_trait_selection::traits::{BuiltinImplSource, ImplSource, ImplSourceUserDefinedData};
use rustc_type_ir::Interner;

use crate::{
    AssocItemResolution, BoundsOptions, ItemId, ItemPredicates, ItemRef, PredicateSearcher,
    SearcherKey, ToPolyTraitRef, TraitProof, TraitProofContents, erase_free_regions,
    has_unnormalized_aliases, impl_may_apply, matching_impls, normalize_bound_val,
    shallow_resolve_trait_ref, trait_ref_holds,
};

pub mod intern {
    use rustc_data_structures::intern::Interned;
    use rustc_data_structures::sharded::{IntoPointer, ShardedHashMap};
    use std::borrow::Borrow;
    use std::hash::{Hash, Hasher};

    /// Storage for deduplicated values. The values handed out are compared by address.
    pub struct Interner<'tcx, T: Eq + Hash> {
        values: ShardedHashMap<InternedValue<'tcx, T>, ()>,
    }

    impl<'tcx, T: Eq + Hash> Default for Interner<'tcx, T> {
        fn default() -> Self {
            Self {
                values: Default::default(),
            }
        }
    }

    impl<'tcx, T: Eq + Hash> Interner<'tcx, T> {
        pub fn intern(&'tcx self, value: T) -> Interned<'tcx, T> {
            let interned = self
                .values
                .intern(value, |value| InternedValue(Box::leak(Box::new(value))));
            Interned::new_unchecked(interned.0)
        }
    }

    // This mirrors rustc's `InternedInSet`: the value lives in the arena and the set stores this
    // copyable pointer wrapper. Equality and hashing still use the pointed-to contents, so
    // `ShardedHashMap::intern` can find an existing arena value if any.
    struct InternedValue<'tcx, T>(&'tcx T);

    impl<T> Clone for InternedValue<'_, T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<T> Copy for InternedValue<'_, T> {}

    impl<T> IntoPointer for InternedValue<'_, T> {
        fn into_pointer(&self) -> *const () {
            self.0 as *const T as *const ()
        }
    }

    impl<T> Borrow<T> for InternedValue<'_, T> {
        fn borrow(&self) -> &T {
            self.0
        }
    }

    impl<T: Eq> PartialEq for InternedValue<'_, T> {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl<T: Eq> Eq for InternedValue<'_, T> {}

    impl<T: Hash> Hash for InternedValue<'_, T> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.0.hash(state);
        }
    }
}

pub struct ElaborationCtx<'tcx, Id: ItemId = DefId> {
    pub tcx: ty::TyCtxt<'tcx>,
    data: &'tcx ElaborationData<'tcx, Id>,
}

impl<'tcx, Id: ItemId> Clone for ElaborationCtx<'tcx, Id> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'tcx, Id: ItemId> Copy for ElaborationCtx<'tcx, Id> {}

pub type ItemRefKey<'tcx, Id> = (Id, ty::GenericArgsRef<'tcx>, AssocItemResolution);

pub(crate) type Selection<'tcx> = Result<ImplSource<'tcx, ()>, CodegenObligationError>;

type ClausesByTrait<'tcx> = FxHashMap<DefId, Vec<Option<ty::TraitRef<'tcx>>>>;
type MatchingImpls<'tcx> = Option<&'tcx [(DefId, ty::GenericArgsRef<'tcx>)]>;

struct ElaborationData<'tcx, Id: ItemId = DefId> {
    bounds_options: BoundsOptions,
    trait_proofs: intern::Interner<'tcx, TraitProofContents<'tcx, Id>>,
    predicate_searchers: Lock<PredicateSearchers<'tcx, Id>>,
    empty_env_searchers: SearcherPool<'tcx, Id>,
    concrete_item_refs: Lock<FxHashMap<ItemRefKey<'tcx, Id>, ItemRef<'tcx, Id>>>,
    concrete_trait_proofs: Lock<FxHashMap<ty::PolyTraitRef<'tcx>, TraitProof<'tcx, Id>>>,
    /// The trait clauses of each environment, normalized and erased like the trait refs we resolve.
    caller_bound_trefs: Lock<FxHashMap<ty::ParamEnv<'tcx>, FxHashSet<ty::PolyTraitRef<'tcx>>>>,
    /// The results of rustc's trait selection.
    selections: Lock<FxHashMap<(ty::ParamEnv<'tcx>, ty::PolyTraitRef<'tcx>), Selection<'tcx>>>,
    /// The trait clauses of each environment and the ones they imply, by trait: their trait refs
    /// with regions erased, or `None` if they may unify with trait refs they aren't equal to.
    elaborated_trait_clauses: Lock<FxHashMap<ty::ParamEnv<'tcx>, &'tcx ClausesByTrait<'tcx>>>,
    /// The impls that match each trait ref, see `matching_impls`.
    matching_impls: Lock<FxHashMap<ty::PolyTraitRef<'tcx>, MatchingImpls<'tcx>>>,
    required_predicates: PredicateCache<'tcx, Id>,
    required_recursively_predicates: PredicateCache<'tcx, Id>,
    implied_predicates: PredicateCache<'tcx, Id>,
}

impl<'tcx, Id: ItemId> Default for ElaborationData<'tcx, Id> {
    fn default() -> Self {
        Self {
            bounds_options: Default::default(),
            trait_proofs: Default::default(),
            predicate_searchers: Default::default(),
            empty_env_searchers: SearcherPool::new(None),
            concrete_item_refs: Default::default(),
            concrete_trait_proofs: Default::default(),
            caller_bound_trefs: Default::default(),
            selections: Default::default(),
            elaborated_trait_clauses: Default::default(),
            matching_impls: Default::default(),
            required_predicates: Default::default(),
            required_recursively_predicates: Default::default(),
            implied_predicates: Default::default(),
        }
    }
}

/// The predicate searchers of the items we've seen. Items with the same `SearcherKey` share a
/// searcher, and thus the resolutions it caches.
struct PredicateSearchers<'tcx, Id: ItemId> {
    of_item: FxHashMap<Id, &'tcx SearcherPool<'tcx, Id>>,
    of_key: FxHashMap<SearcherKey<'tcx, Id>, &'tcx SearcherPool<'tcx, Id>>,
    /// The pools, boxed so that the references above stay valid.
    #[allow(clippy::vec_box)]
    pools: Vec<Box<SearcherPool<'tcx, Id>>>,
}

impl<'tcx, Id: ItemId> Default for PredicateSearchers<'tcx, Id> {
    fn default() -> Self {
        Self {
            of_item: Default::default(),
            of_key: Default::default(),
            pools: Default::default(),
        }
    }
}

/// The predicate searchers for a key (`None` for the empty environment), one for each thread that
/// used them at the same time. A thread doesn't wait for another's searcher: resolving runs rustc
/// queries, and a thread that waits for a query gives up its rustc thread slot and must get one
/// back afterwards, which can't happen if the threads waiting for this searcher keep theirs.
struct SearcherPool<'tcx, Id: ItemId> {
    key: Option<SearcherKey<'tcx, Id>>,
    /// Boxed so that we can lend them for `'tcx`.
    #[allow(clippy::vec_box)]
    searchers: Lock<Vec<Box<Lock<PredicateSearcher<'tcx, Id>>>>>,
}

impl<'tcx, Id: ItemId> SearcherPool<'tcx, Id> {
    fn new(key: Option<SearcherKey<'tcx, Id>>) -> Self {
        Self {
            key,
            searchers: Default::default(),
        }
    }

    /// A searcher of the pool that no other thread is using; we make one if there is none.
    fn take(
        &'tcx self,
        ctx: ElaborationCtx<'tcx, Id>,
        state: &Id::State<'tcx>,
    ) -> LockGuard<'tcx, PredicateSearcher<'tcx, Id>> {
        // SAFETY: the boxes live as long as the pool, which lives for `'tcx`.
        let lend = |searcher: &Lock<_>| -> &'tcx Lock<_> { unsafe { &*(searcher as *const _) } };
        for searcher in self.searchers.lock().iter() {
            if let Some(guard) = lend(searcher).try_lock() {
                return guard;
            }
        }
        // Making a searcher may take a while, so we don't hold the lock meanwhile.
        let searcher = Box::new(Lock::new(match &self.key {
            Some(key) => PredicateSearcher::new(ctx, state, key),
            None => PredicateSearcher::new_empty(ctx),
        }));
        let guard = lend(&searcher).lock();
        self.searchers.lock().push(searcher);
        guard
    }
}

struct PredicateCache<'tcx, Id: ItemId> {
    values: ShardedHashMap<Id, ItemPredicates<'tcx, Id>>,
}

impl<'tcx, Id: ItemId> Default for PredicateCache<'tcx, Id> {
    fn default() -> Self {
        Self {
            values: Default::default(),
        }
    }
}

impl<'tcx, Id: ItemId> PredicateCache<'tcx, Id> {
    fn get_or_insert_with(
        &'tcx self,
        def_id: Id,
        compute: impl FnOnce() -> ItemPredicates<'tcx, Id>,
    ) -> ItemPredicates<'tcx, Id> {
        if let Some(predicates) = self.values.get(&def_id) {
            return predicates;
        }
        let predicates = compute();
        self.values.insert_unique(def_id, predicates.clone());
        predicates
    }
}

impl<'tcx, Id: ItemId> ElaborationData<'tcx, Id> {
    fn intern_trait_proof(
        &'tcx self,
        contents: TraitProofContents<'tcx, Id>,
    ) -> TraitProof<'tcx, Id> {
        let interned = self.trait_proofs.intern(contents);
        TraitProof { contents: interned }
    }
}

impl<'tcx, Id: ItemId> ElaborationCtx<'tcx, Id> {
    /// Warning: only create a single one.
    pub fn new(tcx: ty::TyCtxt<'tcx>, bounds_options: BoundsOptions) -> Self {
        // `TraitProof` is a copyable `Interned<'tcx, _>` and may outlive the `PredicateSearcher`
        // that produced it. We therefore give each elaboration context session-long storage, like
        // rustc's own arenas. The interned values still contain rustc data bounded by `'tcx`.
        let data = Box::leak(Box::new(ElaborationData {
            bounds_options,
            ..ElaborationData::default()
        }));
        ElaborationCtx { tcx, data }
    }

    /// Free the storage of this context, which is otherwise leaked.
    ///
    /// # Safety
    /// Neither this context, nor its copies, nor anything they produced (e.g. `TraitProof`s) may
    /// be used afterwards.
    pub unsafe fn free(self) {
        let data = self.data as *const ElaborationData<'tcx, Id> as *mut ElaborationData<'tcx, Id>;
        drop(unsafe { Box::from_raw(data) });
    }

    pub fn bounds_options(&self) -> &BoundsOptions {
        &self.data.bounds_options
    }

    pub(crate) fn concrete_item_refs(
        &self,
    ) -> &'tcx Lock<FxHashMap<ItemRefKey<'tcx, Id>, ItemRef<'tcx, Id>>> {
        &self.data.concrete_item_refs
    }

    pub(crate) fn concrete_trait_proofs(
        &self,
    ) -> &'tcx Lock<FxHashMap<ty::PolyTraitRef<'tcx>, TraitProof<'tcx, Id>>> {
        &self.data.concrete_trait_proofs
    }

    pub fn intern_trait_proof(
        &self,
        contents: TraitProofContents<'tcx, Id>,
    ) -> TraitProof<'tcx, Id> {
        self.data.intern_trait_proof(contents)
    }

    /// Whether `tref`, normalized and erased, is one of the trait clauses of `typing_env`.
    pub(crate) fn is_caller_bound(
        &self,
        typing_env: ty::TypingEnv<'tcx>,
        tref: ty::PolyTraitRef<'tcx>,
    ) -> bool {
        let tcx = self.tcx;
        let caller_bound_trefs = &self.data.caller_bound_trefs;
        if let Some(trefs) = caller_bound_trefs.lock().get(&typing_env.param_env) {
            return trefs.contains(&tref);
        }
        // Normalizing runs rustc queries: we must not hold the lock meanwhile, as other threads
        // waiting for it would keep their rustc thread slots, which we may need to continue.
        let trefs: FxHashSet<_> = typing_env
            .param_env
            .caller_bounds()
            .filter_map(|clause| clause.as_trait_clause())
            .filter(|clause| clause.polarity() == ty::ClausePolarity::Positive)
            .map(|clause| {
                let tref = ty::set_aliases_to_non_rigid(tcx, clause.to_poly_trait_ref())
                    .skip_normalization();
                normalize_bound_val(tcx, typing_env, tref)
            })
            .collect();
        let found = trefs.contains(&tref);
        caller_bound_trefs
            .lock()
            .entry(typing_env.param_env)
            .or_insert(trefs);
        found
    }

    /// Whether a where-clause of the environment, or one it implies, could prove `tref`, which is
    /// normalized and erased. Without aliases or bound variables, a clause unifies with `tref`
    /// exactly when they are equal modulo regions.
    fn where_clause_may_apply(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        tref: ty::PolyTraitRef<'tcx>,
    ) -> bool {
        let tcx = self.tcx;
        let found = self
            .data
            .elaborated_trait_clauses
            .lock()
            .get(&param_env)
            .copied();
        // Elaborating runs rustc queries, so we don't hold the lock meanwhile.
        let clauses = found.unwrap_or_else(|| {
            let mut clauses = ClausesByTrait::default();
            for clause in rustc_type_ir::elaborate::elaborate(tcx, param_env.caller_bounds()) {
                if let Some(clause) = clause.as_trait_clause() {
                    let tref = (clause.polarity() == ty::ClausePolarity::Positive
                        && clause.bound_vars().is_empty()
                        && !clause.has_aliases())
                    .then(|| erase_free_regions(tcx, clause.skip_binder().trait_ref));
                    clauses.entry(clause.def_id()).or_default().push(tref);
                }
            }
            let clauses = &*Box::leak(Box::new(clauses));
            *self
                .data
                .elaborated_trait_clauses
                .lock()
                .entry(param_env)
                .or_insert(clauses)
        });
        clauses.get(&tref.def_id()).is_some_and(|clauses| {
            clauses
                .iter()
                .any(|clause| clause.is_none_or(|clause| clause == tref.skip_binder()))
        })
    }

    fn matching_impls(&self, tref: ty::PolyTraitRef<'tcx>) -> MatchingImpls<'tcx> {
        if let Some(found) = self.data.matching_impls.lock().get(&tref) {
            return *found;
        }
        let found = matching_impls(self.tcx, tref).map(|impls| &*impls.leak());
        self.data.matching_impls.lock().insert(tref, found);
        found
    }

    /// Rustc's selection for a normalized and erased `tref` when a single candidate can prove it,
    /// which we find without building the solver's proof tree: no where-clause or alias bound
    /// applies, and either no impl applies, leaving builtin impls, or one impl applies and the trait
    /// has no builtin impls.
    fn select_single_candidate(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        tref: ty::PolyTraitRef<'tcx>,
    ) -> Option<ImplSource<'tcx, ()>> {
        let tcx = self.tcx;
        let trait_def_id = tref.def_id();
        if !tcx.next_trait_solver_globally()
            || matches!(
                tref.self_ty().skip_binder().kind(),
                ty::Dynamic(..) | ty::Alias(..)
            )
            || tref.has_infer()
            || tref.references_error()
            || has_unnormalized_aliases(tref)
            || tcx.trait_is_alias(trait_def_id)
            || self.where_clause_may_apply(param_env, tref)
        {
            return None;
        }
        let impls = self.matching_impls(tref)?;
        let mut applicable = impls.iter().filter(|(impl_def_id, impl_args)| {
            impls.len() == 1 || impl_may_apply(tcx, param_env, *impl_def_id, impl_args)
        });
        let selection = match (applicable.next(), applicable.next()) {
            (None, _) => ImplSource::Builtin(BuiltinImplSource::Misc, Default::default()),
            (Some(&(impl_def_id, args)), None)
                if tcx.as_trait_lang_item(trait_def_id).is_none()
                    && !tcx.trait_is_auto(trait_def_id) =>
            {
                ImplSource::UserDefined(ImplSourceUserDefinedData {
                    impl_def_id,
                    args,
                    nested: Default::default(),
                })
            }
            _ => return None,
        };
        trait_ref_holds(tcx, param_env, tref).then_some(selection)
    }

    /// Rustc's trait selection, cached.
    pub(crate) fn select(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        tref: ty::PolyTraitRef<'tcx>,
    ) -> Selection<'tcx> {
        if let Some(selection) = self.data.selections.lock().get(&(param_env, tref)) {
            return selection.clone();
        }
        let selection = match self.select_single_candidate(param_env, tref) {
            Some(selection) => Ok(selection),
            None => shallow_resolve_trait_ref(self.tcx, param_env, tref),
        };
        self.data
            .selections
            .lock()
            .insert((param_env, tref), selection.clone());
        selection
    }

    pub fn predicate_searcher_for(
        &self,
        state: &Id::State<'tcx>,
        def_id: Id,
    ) -> LockGuard<'tcx, PredicateSearcher<'tcx, Id>> {
        let searchers = &self.data.predicate_searchers;
        let found = searchers.lock().of_item.get(&def_id).copied();
        let pool = match found {
            Some(pool) => pool,
            None => {
                // Computing the key may take a while, so we don't hold the lock meanwhile.
                let key = SearcherKey::for_owner(*self, state, &def_id);
                let mut searchers = searchers.lock();
                let pool = match searchers.of_key.get(&key) {
                    Some(pool) => *pool,
                    None => {
                        let new = Box::new(SearcherPool::new(Some(key.clone())));
                        // SAFETY: the box lives as long as `self.data`.
                        let pool: &'tcx SearcherPool<'tcx, Id> = unsafe { &*(&*new as *const _) };
                        searchers.pools.push(new);
                        searchers.of_key.insert(key, pool);
                        pool
                    }
                };
                searchers.of_item.insert(def_id.clone(), pool);
                pool
            }
        };
        pool.take(*self, state)
    }

    /// Resolve the trait proofs of an item reference that left them unresolved. Since they don't
    /// depend on the context, we resolve them in the empty environment.
    pub fn resolve_lazy_trait_proofs(
        &self,
        state: &Id::State<'tcx>,
        item: &ItemRef<'tcx, Id>,
    ) -> Vec<TraitProof<'tcx, Id>> {
        match &item.trait_proofs {
            Some(trait_proofs) => trait_proofs.clone(),
            None => self.resolve_empty_env_trait_proofs(state, &item.def_id, item.generic_args),
        }
    }

    pub(crate) fn resolve_empty_env_trait_proofs(
        &self,
        state: &Id::State<'tcx>,
        def_id: &Id,
        generics: ty::GenericArgsRef<'tcx>,
    ) -> Vec<TraitProof<'tcx, Id>> {
        self.data
            .empty_env_searchers
            .take(*self, state)
            .resolve_item_required_predicates(state, def_id.clone(), generics)
    }

    pub(crate) fn cached_required_predicates(
        &self,
        def_id: Id,
        compute: impl FnOnce() -> ItemPredicates<'tcx, Id>,
    ) -> ItemPredicates<'tcx, Id> {
        self.data
            .required_predicates
            .get_or_insert_with(def_id, compute)
    }

    pub(crate) fn cached_required_recursively_predicates(
        &self,
        def_id: Id,
        compute: impl FnOnce() -> ItemPredicates<'tcx, Id>,
    ) -> ItemPredicates<'tcx, Id> {
        self.data
            .required_recursively_predicates
            .get_or_insert_with(def_id, compute)
    }

    pub(crate) fn cached_implied_predicates(
        &self,
        def_id: Id,
        compute: impl FnOnce() -> ItemPredicates<'tcx, Id>,
    ) -> ItemPredicates<'tcx, Id> {
        self.data
            .implied_predicates
            .get_or_insert_with(def_id, compute)
    }
}
