use rustc_data_structures::sharded::ShardedHashMap;
use rustc_data_structures::sync::{Lock, LockGuard};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::traits::CodegenObligationError;
use rustc_middle::ty;
use rustc_trait_selection::traits::ImplSource;

use crate::{
    AssocItemResolution, BoundsOptions, ItemId, ItemPredicates, ItemRef, PredicateSearcher,
    SearcherKey, ToPolyTraitRef, TraitProof, TraitProofContents, normalize_bound_val,
    shallow_resolve_trait_ref,
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

struct ElaborationData<'tcx, Id: ItemId = DefId> {
    bounds_options: BoundsOptions,
    trait_proofs: intern::Interner<'tcx, TraitProofContents<'tcx, Id>>,
    predicate_searchers: Lock<PredicateSearchers<'tcx, Id>>,
    empty_env_searcher: Lock<Option<PredicateSearcher<'tcx, Id>>>,
    concrete_item_refs: Lock<FxHashMap<ItemRefKey<'tcx, Id>, ItemRef<'tcx, Id>>>,
    concrete_trait_proofs: Lock<FxHashMap<ty::PolyTraitRef<'tcx>, TraitProof<'tcx, Id>>>,
    /// The trait clauses of each environment, normalized and erased like the trait refs we resolve.
    caller_bound_trefs: Lock<FxHashMap<ty::ParamEnv<'tcx>, FxHashSet<ty::PolyTraitRef<'tcx>>>>,
    /// The results of rustc's trait selection.
    selections: Lock<FxHashMap<(ty::ParamEnv<'tcx>, ty::PolyTraitRef<'tcx>), Selection<'tcx>>>,
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
            empty_env_searcher: Default::default(),
            concrete_item_refs: Default::default(),
            concrete_trait_proofs: Default::default(),
            caller_bound_trefs: Default::default(),
            selections: Default::default(),
            required_predicates: Default::default(),
            required_recursively_predicates: Default::default(),
            implied_predicates: Default::default(),
        }
    }
}

/// The predicate searchers of the items we've seen. Items with the same `SearcherKey` share a
/// searcher, and thus the resolutions it caches.
struct PredicateSearchers<'tcx, Id: ItemId> {
    of_item: FxHashMap<Id, &'tcx Lock<PredicateSearcher<'tcx, Id>>>,
    of_key: FxHashMap<SearcherKey<'tcx, Id>, &'tcx Lock<PredicateSearcher<'tcx, Id>>>,
    /// The searchers, boxed so that the references above stay valid.
    #[allow(clippy::vec_box)]
    searchers: Vec<Box<Lock<PredicateSearcher<'tcx, Id>>>>,
}

impl<'tcx, Id: ItemId> Default for PredicateSearchers<'tcx, Id> {
    fn default() -> Self {
        Self {
            of_item: Default::default(),
            of_key: Default::default(),
            searchers: Default::default(),
        }
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
        let mut caller_bound_trefs = self.data.caller_bound_trefs.lock();
        caller_bound_trefs
            .entry(typing_env.param_env)
            .or_insert_with(|| {
                typing_env
                    .param_env
                    .caller_bounds()
                    .filter_map(|clause| clause.as_trait_clause())
                    .filter(|clause| clause.polarity() == ty::ClausePolarity::Positive)
                    .map(|clause| {
                        let tref = ty::set_aliases_to_non_rigid(tcx, clause.to_poly_trait_ref())
                            .skip_normalization();
                        normalize_bound_val(tcx, typing_env, tref)
                    })
                    .collect()
            })
            .contains(&tref)
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
        let selection = shallow_resolve_trait_ref(self.tcx, param_env, tref);
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
        let searcher = match found {
            Some(searcher) => searcher,
            None => {
                // We build searchers without holding the lock: this may take a while.
                let key = SearcherKey::for_owner(*self, state, &def_id);
                let found = searchers.lock().of_key.get(&key).copied();
                let searcher = match found {
                    Some(searcher) => searcher,
                    None => {
                        let new = Box::new(Lock::new(PredicateSearcher::new(*self, state, &key)));
                        let mut searchers = searchers.lock();
                        match searchers.of_key.get(&key) {
                            Some(searcher) => *searcher,
                            None => {
                                // SAFETY: the box lives as long as `self.data`.
                                let searcher: &'tcx Lock<_> = unsafe { &*(&*new as *const _) };
                                searchers.searchers.push(new);
                                searchers.of_key.insert(key, searcher);
                                searcher
                            }
                        }
                    }
                };
                searchers.lock().of_item.insert(def_id, searcher);
                searcher
            }
        };
        searcher.lock()
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
        let mut searcher = self.data.empty_env_searcher.lock();
        searcher
            .get_or_insert_with(|| PredicateSearcher::new_empty(*self))
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
