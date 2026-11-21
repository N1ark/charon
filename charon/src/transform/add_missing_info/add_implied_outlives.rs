//! Make explicit the outlives predicates implied by the well-formedness of a type.
use derive_generic_visitor::*;
use itertools::Itertools;
use rayon::prelude::*;
use std::mem;

use crate::ast::*;
use crate::transform::{TransformCtx, ctx::TransformPass};
use crate::utils::CycleDetector;
use rustc_hash::FxHashSet as HashSet;

#[derive(Default)]
struct OutlivesAtBinder {
    outlives: SeqHashSet<PolyOutlivesPred>,
    /// The lifetime of the innermost reference we're inside of. When going under a binder, we keep
    /// it there.
    ///
    /// E.g. in `&'a for<'b> fn(&'b u32, &'c u32)`, the `'a` stays on the outer binder, and we use
    /// that to add `'c: 'a` but we don't add `'b: 'a` since `'b` is not visible from where `'a`
    /// is.
    shorter_region: Option<Region>,
}

impl OutlivesAtBinder {
    fn finish(self, outlives: &mut Vec<PolyOutlivesPred>) {
        debug_assert!(self.shorter_region.is_none());
        let mut predicates: SeqHashSet<_> = mem::take(outlives).into_iter().collect();
        predicates.extend(self.outlives);
        outlives.extend(predicates.into_iter().filter(|pred| {
            let OutlivesPred(longer, shorter) = &pred.skip_binder;
            longer != shorter && !longer.is_erased() && !shorter.is_erased()
        }));
    }
}

/// Explore a type and accumulate the outlives predicates it implies.
#[derive(Visitor)]
struct OutlivesGatherer<'a> {
    type_decls: &'a IndexMap<TypeDeclId, TypeDecl>,
    trait_decls: &'a IndexMap<TraitDeclId, TraitDecl>,
    item_params: &'a mut GenericParams,
    binders: BindingStack<OutlivesAtBinder>,
    /// Whether the predicates that reach the outermost level are discarded, as is the case for
    /// bodies.
    discard_outermost: bool,
    /// How many of the binders we're under (excluding the outermost level) bind variables or
    /// have predicates.
    non_empty_binders: usize,
    /// Types without non-empty binders that we explored under empty binders only, without
    /// shorter regions, with the number of binders. Exploring them again in the same situation
    /// would add nothing.
    explored: HashSet<(Ty, usize)>,
}

impl<'a> OutlivesGatherer<'a> {
    fn new(
        item_params: &'a mut GenericParams,
        type_decls: &'a IndexMap<TypeDeclId, TypeDecl>,
        trait_decls: &'a IndexMap<TraitDeclId, TraitDecl>,
    ) -> Self {
        Self {
            type_decls,
            trait_decls,
            item_params,
            binders: BindingStack::new(OutlivesAtBinder::default()),
            discard_outermost: false,
            non_empty_binders: 0,
            explored: HashSet::default(),
        }
    }

    /// Whether we can skip visiting a value with that type info. Under empty binders only, all the
    /// predicates implied by a value without non-empty binders reach the outermost level. If these
    /// are discarded, visiting the value has no effect. This is checked before visiting to avoid
    /// cloning and re-interning hash-consed values.
    fn can_skip(&self, info: TypeInfo) -> bool {
        self.discard_outermost && self.non_empty_binders == 0 && !info.has_non_empty_binder()
    }

    fn finish(mut self) {
        let outlives = self.binders.pop().unwrap();
        debug_assert!(self.binders.is_empty());
        outlives.finish(&mut self.item_params.outlives);
    }

    fn add_outlives(&mut self, pred: PolyOutlivesPred) {
        let (pred, level) = self.binders.place_at_outermost(&pred);
        level.outlives.insert(pred);
    }
    fn add_outliving_region(&mut self, longer: &Region) {
        // Find the innermost region that affects `longer`: it needs to be bound at a level where
        // `longer` can be moved to.
        let Some((bound_depth, pred)) =
            self.binders.iter_enumerated().find_map(|(depth, binder)| {
                let shorter = binder.shorter_region.clone()?;
                let longer = longer.clone().move_from_under_binders(depth)?;
                let pred = RegionBinder::empty(OutlivesPred(longer, shorter));
                Some((depth, pred))
            })
        else {
            return;
        };
        // Place the predicate at the outermost level.
        let (pred, level) = self.binders[bound_depth..].place_at_outermost(&pred);
        level.outlives.insert(pred);
    }

    fn with_shorter_region(
        &mut self,
        region: Region,
        f: impl FnOnce(&mut Self) -> ControlFlow<Infallible>,
    ) -> ControlFlow<Infallible> {
        self.add_outliving_region(&region);
        let previous = self.binders.innermost_mut().shorter_region.replace(region);
        let result = f(self);
        self.binders.innermost_mut().shorter_region = previous;
        result
    }

    /// Add the predicates implied by the outer layer of a type, and return how to visit its
    /// contents.
    fn enter_ty(&mut self, ty: &Ty) -> TyContents {
        if let TyKind::TraitType(proof, type_id, args) = ty.kind()
            && let Some(decl) = self.trait_decls.get(proof.trait_id())
            && let Some(assoc) = decl.types.get(*type_id)
        {
            // Instantiate the trait parameters under the GAT binder, then the GAT parameters.
            let assoc = assoc.clone().substitute_with_tref(proof);
            for pred in assoc.params.outlives.substitute_inner_binder(args) {
                self.add_outlives(pred);
            }
        }
        match ty.kind() {
            TyKind::TypeVar(_) | TyKind::TraitType(..) => {
                self.add_outliving_region(&Region::Lub(ty.clone()));
                return TyContents::Opaque;
            }
            TyKind::Adt(type_ref) => {
                if let Some(decl) = self.type_decls.get(type_ref.id) {
                    let outlives = decl
                        .generics
                        .outlives
                        .iter()
                        .cloned()
                        .map(|pred| pred.substitute(&type_ref.generics))
                        .collect_vec();
                    for pred in outlives {
                        self.add_outlives(pred);
                    }
                }
            }
            _ => {}
        }
        match ty.kind() {
            TyKind::Ref(region @ (Region::Static | Region::Var(_) | Region::Lub(_)), _, _) => {
                TyContents::UnderRef(region.clone())
            }
            _ => TyContents::Plain,
        }
    }

    /// Visit the contents of a type using `visit_inner`, as instructed by `enter_ty`.
    fn visit_ty_contents(
        &mut self,
        contents: TyContents,
        visit_inner: impl FnOnce(&mut Self) -> ControlFlow<Infallible>,
    ) -> ControlFlow<Infallible> {
        match contents {
            TyContents::Plain => visit_inner(self),
            TyContents::Opaque => {
                // `T::Assoc: 'a` does not imply `T: 'a`. We temporarily remove `shorter_region`
                // from all binders while we visit the type.
                let shorter_regions = self
                    .binders
                    .iter_mut()
                    .map(|binder| binder.shorter_region.take())
                    .collect_vec();
                let result = visit_inner(self);
                for (binder, shorter) in self.binders.iter_mut().zip(shorter_regions) {
                    binder.shorter_region = shorter;
                }
                result
            }
            TyContents::UnderRef(region) => self.with_shorter_region(region, visit_inner),
        }
    }

    fn add_region_outlives(&mut self, region: &Region) {
        if matches!(region, Region::Var(_) | Region::Lub(_)) {
            self.add_outliving_region(region);
        }
    }
}

/// How to visit the contents of a type, see [`OutlivesGatherer::enter_ty`].
enum TyContents {
    Plain,
    /// The contents of a type variable or associated type don't outlive the regions it outlives.
    Opaque,
    /// The contents of a reference outlive its region.
    UnderRef(Region),
}

/// Gathers the predicates implied by a value that contains no non-empty binders: since these are
/// the only places where we add predicates, the value can be explored without cloning and
/// re-interning it. Its empty binders only matter to track the binding depth.
#[derive(Visitor)]
struct GatherOnly<'b, 'a>(&'b mut OutlivesGatherer<'a>);

impl VisitAst for GatherOnly<'_, '_> {
    fn visit_binder<T: AstVisitable>(&mut self, binder: &Binder<T>) -> ControlFlow<Self::Break> {
        self.0.binders.push(OutlivesAtBinder::default());
        let result = self.visit_inner(binder);
        let binder_outlives = self.0.binders.pop().unwrap().outlives;
        debug_assert!(binder_outlives.is_empty());
        result
    }

    fn visit_region_binder<T: AstVisitable>(
        &mut self,
        binder: &RegionBinder<T>,
    ) -> ControlFlow<Self::Break> {
        self.0.binders.push(OutlivesAtBinder::default());
        let result = self.visit_inner(binder);
        let binder_outlives = self.0.binders.pop().unwrap().outlives;
        debug_assert!(binder_outlives.is_empty());
        result
    }

    fn visit_with_cached_type_info<T: AstVisitable + HashConsable>(
        &mut self,
        value: &HashConsed<WithCachedTypeInfo<T>>,
    ) -> ControlFlow<Self::Break> {
        if self.0.can_skip(value.type_info()) {
            return Continue(());
        }
        self.visit_inner(value)
    }

    fn visit_ty(&mut self, ty: &Ty) -> ControlFlow<Self::Break> {
        if self.0.can_skip(ty.type_info()) {
            return Continue(());
        }
        if self.0.non_empty_binders == 0
            && self.0.binders.iter().all(|b| b.shorter_region.is_none())
            && !self.0.explored.insert((ty.clone(), self.0.binders.len()))
        {
            return Continue(());
        }
        let contents = self.0.enter_ty(ty);
        self.0
            .visit_ty_contents(contents, |this| GatherOnly(this).visit_inner(ty))
    }

    fn enter_region(&mut self, region: &Region) {
        self.0.add_region_outlives(region);
    }
}

impl VisitAstMut for OutlivesGatherer<'_> {
    fn visit_binder<T: AstVisitable>(
        &mut self,
        binder: &mut Binder<T>,
    ) -> ControlFlow<Self::Break> {
        let non_empty = !binder.params.is_empty();
        self.non_empty_binders += non_empty as usize;
        self.binders.push(OutlivesAtBinder::default());
        let result = self.visit_inner(binder);
        self.non_empty_binders -= non_empty as usize;
        self.binders
            .pop()
            .unwrap()
            .finish(&mut binder.params.outlives);
        result
    }

    fn visit_region_binder<T: AstVisitable>(
        &mut self,
        binder: &mut RegionBinder<T>,
    ) -> ControlFlow<Self::Break> {
        let non_empty = !binder.regions.is_empty() || !binder.outlives.is_empty();
        self.non_empty_binders += non_empty as usize;
        self.binders.push(OutlivesAtBinder::default());
        let result = self.visit_inner(binder);
        self.non_empty_binders -= non_empty as usize;
        self.binders.pop().unwrap().finish(&mut binder.outlives);
        result
    }

    fn visit_with_cached_type_info<T: AstVisitable + HashConsable>(
        &mut self,
        value: &mut HashConsed<WithCachedTypeInfo<T>>,
    ) -> ControlFlow<Self::Break> {
        if self.can_skip(value.type_info()) {
            return Continue(());
        }
        if !value.type_info().has_non_empty_binder() {
            return GatherOnly(self).visit(&*value);
        }
        self.visit_inner(value)
    }

    fn visit_ty(&mut self, ty: &mut Ty) -> ControlFlow<Self::Break> {
        if self.can_skip(ty.type_info()) {
            return Continue(());
        }
        if !ty.type_info().has_non_empty_binder() {
            return GatherOnly(self).visit(&*ty);
        }
        let contents = self.enter_ty(ty);
        self.visit_ty_contents(contents, |this| this.visit_inner(ty))
    }

    fn enter_region(&mut self, region: &mut Region) {
        self.add_region_outlives(region);
    }
}

struct ClosureOutlivesComputer<'a> {
    type_decls: &'a mut IndexMap<TypeDeclId, TypeDecl>,
    trait_decls: &'a IndexMap<TraitDeclId, TraitDecl>,
    /// Map of types we want to process.
    closure_tys: SeqHashMap<TypeDeclId, CycleDetector<()>>,
}

impl<'a> ClosureOutlivesComputer<'a> {
    fn new(
        type_decls: &'a mut IndexMap<TypeDeclId, TypeDecl>,
        trait_decls: &'a IndexMap<TraitDeclId, TraitDecl>,
    ) -> Self {
        let closure_tys = type_decls
            .iter()
            .filter(|decl| matches!(decl.src, TypeSource::Closure { .. }))
            .map(|decl| (decl.def_id, CycleDetector::Unprocessed))
            .collect();
        Self {
            type_decls,
            trait_decls,
            closure_tys,
        }
    }

    fn compute_all(mut self) {
        for type_id in self.closure_tys.keys().cloned().collect_vec() {
            self.compute(type_id);
        }
    }

    fn compute(&mut self, type_id: TypeDeclId) {
        if self.closure_tys[&type_id].start_processing() {
            let mut dependencies = Vec::new();
            self.type_decls[type_id]
                .kind
                .dyn_visit(|type_ref: &TypeDeclRef| {
                    if self.closure_tys.get(&type_ref.id).is_some() {
                        dependencies.push(type_ref.id);
                    }
                });
            for dependency in dependencies {
                self.compute(dependency);
            }

            // Move the kind out so that the crate can inspect the rest of the decls.
            let mut kind = mem::replace(&mut self.type_decls[type_id].kind, TypeDeclKind::Opaque);
            let mut params = mem::take(&mut self.type_decls[type_id].generics);
            let mut visitor = OutlivesGatherer::new(&mut params, self.type_decls, self.trait_decls);
            visitor.visit(&mut kind);
            visitor.finish();
            self.type_decls[type_id].generics = params;
            self.type_decls[type_id].kind = kind;
            self.closure_tys[&type_id].done_processing(());
        }
        assert!(
            matches!(self.closure_tys[&type_id], CycleDetector::Processed(_)),
            "closure type declarations unexpectedly form a cycle"
        );
    }
}

pub struct Transform;

impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let type_decls = &mut ctx.translated.type_decls;
        let trait_decls = &mut ctx.translated.trait_decls;

        // Rustc gives us explicit outlives for ADTs, but we make fake ADTs for closures, so we
        // infer their outlives predicates here. Thankfully they can't be recursive, which makes
        // the implementation much easier than having to deal with all ADTs.
        ClosureOutlivesComputer::new(type_decls, trait_decls).compute_all();

        // The items only read the type and trait declarations, whose relevant parts (the outlives
        // predicates of types and associated types) don't change from now on, so we can process
        // them in parallel.
        let type_decls = &ctx.translated.type_decls;
        let trait_decls = &ctx.translated.trait_decls;
        ctx.translated
            .fun_decls
            .iter_mut()
            .collect_vec()
            .into_par_iter()
            .for_each(|fun_decl| {
                let mut visitor =
                    OutlivesGatherer::new(&mut fun_decl.generics, type_decls, trait_decls);
                visitor.visit(&mut fun_decl.signature);
                // The impl header contributes to the implied bounds even if its types are
                // not mentioned in the signature.
                match &mut fun_decl.src {
                    FunSource::InherentImpl { self_ty } => {
                        visitor.visit(self_ty);
                    }
                    FunSource::TraitImpl { trait_ref, .. } => {
                        visitor.visit(trait_ref);
                    }
                    _ => {}
                }
                visitor.finish();

                // Also add implied bounds to the inner binders inside bodies. Implied bounds
                // involving only body or signature lifetimes must not be kept; they must be checked
                // by borrow-checking.
                OutlivesGatherer {
                    discard_outermost: true,
                    ..OutlivesGatherer::new(&mut GenericParams::default(), type_decls, trait_decls)
                }
                .visit(&mut fun_decl.body);
            });

        ctx.translated
            .trait_impls
            .iter_mut()
            .collect_vec()
            .into_par_iter()
            .for_each(|timpl| {
                let mut visitor =
                    OutlivesGatherer::new(&mut timpl.generics, type_decls, trait_decls);
                visitor.visit(&mut timpl.impl_trait);
                visitor.finish();
            });

        // Keep the associated type declarations available while visiting method signatures.
        let mut methods: Vec<(TraitDeclId, IndexMap<_, _>)> = ctx
            .translated
            .trait_decls
            .iter_mut()
            .map(|decl| (decl.def_id, mem::take(&mut decl.methods)))
            .collect();
        let trait_decls = &ctx.translated.trait_decls;
        methods
            .par_iter_mut()
            .flat_map_iter(|(_, methods)| methods.iter_mut())
            .for_each(|method| {
                let mut visitor =
                    OutlivesGatherer::new(&mut method.params, type_decls, trait_decls);
                visitor.visit(&mut method.skip_binder.signature);
                visitor.finish();
            });
        for (trait_id, methods) in methods {
            ctx.translated.trait_decls[trait_id].methods = methods;
        }
    }
}
