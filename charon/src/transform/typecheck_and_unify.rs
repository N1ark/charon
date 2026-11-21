// Check that types are consistent and unify body lifetimes (best-effort).
use derive_generic_visitor::*;
use index_vec::Idx;
use itertools::Itertools;
use petgraph::{graph::IndexType, unionfind::UnionFind};
use rayon::prelude::*;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::{borrow::Cow, cell::Cell, fmt::Display, mem};

use crate::{
    ast::*,
    errors::Level,
    formatter::{AstFormatter, FmtCtx, IntoFormatter},
    ids::IndexVec,
    pretty::FmtWithCtx,
    transform::utils::GenericsSource,
};

use crate::transform::{
    TransformCtx,
    ctx::{PerThread, TransformPass},
};

unsafe impl IndexType for RegionId {
    fn new(x: usize) -> Self {
        RegionId::new(x)
    }
    fn index(&self) -> usize {
        <RegionId as Idx>::index(*self)
    }
    fn max() -> Self {
        RegionId::new(RegionId::MAX_INDEX)
    }
}

#[derive(Visitor)]
struct TypeCheckVisitor<'a> {
    ctx: &'a TransformCtx,
    /// The item being checked. We don't look at it through `ctx`: an item isn't checked against
    /// itself.
    item_id: ItemId,
    phase: Check,
    /// Tracks an enclosing span for error reporting.
    span: Span,
    /// Track the binders seen so far.
    // We can't keep the params by reference because the visitors don't tell us that everything
    // we're visiting has lifetime `'a`.
    binder_stack: BindingStack<GenericParams>,
    /// Remember the names of the types visited up to here.
    visit_stack: Vec<&'static str>,
    body_lt_unifier: Option<UnionFind<RegionId>>,
    /// Whether `body_lt_unifier` merged anything, i.e. whether the body needs rewriting.
    did_unify_lifetimes: bool,
    /// If set, the lifetime unifications to apply later instead of right away.
    pending_unifications: Option<Vec<(RegionId, RegionId)>>,
    /// Set when matching a value hits something that requires substituting it first.
    needs_substitution: bool,
    /// Set while we check a value without substituting it first, see `assert_matches_trait_item`.
    /// Records whether that check ran into anything, in which case we redo it normally.
    dry_run: Option<Cell<bool>>,
    /// Whether substituting a given value with arguments of the given lengths succeeds, see
    /// `substitution_succeeds`.
    substitution_cache: &'a mut HashMap<(SubstitutedValue, [usize; 4]), bool>,
    /// Defaulted methods may have contradictory premises like `Self::Item = bool` and
    /// `Self::Item = u32` which may equate entirely different types. We don't try to reason about
    /// this and instead accept this fact. It's fine because the original methods will be
    /// type-checked.
    /// Some tests where this matters: default-method-with-item-bound.6.rs,
    /// issue-1403-default-method-with-item-constraint
    accept_type_errors: bool,
    /// Identifies the binders we're under, innermost last. Empty binders bind nothing so they're
    /// interchangeable: they get an id shared by all the empty binders with the same parent.
    binder_ctx: Vec<u32>,
    empty_binder_ctx: HashMap<u32, u32>,
    last_binder_ctx: u32,
    /// The types, trait refs and constants (by address) we checked without errors under a given
    /// binder context and `accept_type_errors` mode: checking them again would do nothing.
    checked: &'a mut HashSet<(usize, u32, bool)>,
    /// The number of errors reported so far.
    error_count: Cell<usize>,
}

impl VisitorWithSpan for TypeCheckVisitor<'_> {
    fn current_span(&mut self) -> &mut Span {
        &mut self.span
    }
}
impl VisitorWithBinderStack for TypeCheckVisitor<'_> {
    fn binder_stack_mut(&mut self) -> &mut BindingStack<GenericParams> {
        &mut self.binder_stack
    }
}

struct TypeError;

/// A value of the crate that we substitute: an item of a trait or impl, or a clause of a trait.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum SubstitutedValue {
    Method(TraitDeclId, TraitMethodId),
    AssocTy(TraitDeclId, AssocTypeId),
    ParentClause(TraitDeclId, TraitClauseId),
    ImplTrait(TraitImplId),
}

fn arg_counts(args: &GenericArgs) -> [usize; 4] {
    [
        args.regions.len(),
        args.types.len(),
        args.const_generics.len(),
        args.trait_refs.len(),
    ]
}

/// How to read the variables of a value we match: `args` and `outer`, if set, are the arguments for
/// the variables bound at `depth` and `depth + 1` respectively, which haven't been substituted. The
/// other variables don't matter since matching ignores them.
#[derive(Clone, Copy)]
struct Env<'a> {
    args: Option<&'a GenericArgs>,
    outer: Option<&'a GenericArgs>,
    depth: DeBruijnId,
}

impl<'a> Env<'a> {
    const NONE: Self = Env {
        args: None,
        outer: None,
        depth: DeBruijnId::ZERO,
    };
    fn new(args: &'a GenericArgs) -> Self {
        Env {
            args: Some(args),
            ..Self::NONE
        }
    }
    fn under_binder(self) -> Self {
        Env {
            depth: self.depth.incr(),
            ..self
        }
    }
}

impl<'a> TypeCheckVisitor<'a> {
    fn get_item(&self, id: ItemId) -> Option<ItemRef<'a>> {
        if id == self.item_id {
            return None;
        }
        self.ctx.translated.get_item(id)
    }
    fn trait_decl(&self, id: TraitDeclId) -> Option<&'a TraitDecl> {
        self.get_item(id.into())?.as_trait_decl().copied()
    }
    fn trait_impl(&self, id: TraitImplId) -> Option<&'a TraitImpl> {
        self.get_item(id.into())?.as_trait_impl().copied()
    }

    fn error(&self, message: impl Display) {
        if let Some(failed) = &self.dry_run {
            failed.set(true);
            return;
        }
        let msg = format!(
            "Type error {}:\n{message}\n\
            Visitor stack:\n  {}\n\
            Binding stack (depth {}):\n  {}",
            self.phase.name(),
            self.visit_stack.iter().rev().join("\n  "),
            self.binder_stack.len(),
            self.binder_stack
                .iter_enumerated()
                .map(|(i, params)| format!("{i}: {params}"))
                .join("\n  "),
        );
        // This is a fatal error: the output llbc is inconsistent and should not be used.
        self.ctx.span_err(self.span, &msg, Level::ERROR);
        self.error_count.set(self.error_count.get() + 1);
    }

    /// Visit under a binder, tracking `binder_ctx`.
    fn with_binder_ctx(
        &mut self,
        is_empty: bool,
        f: impl FnOnce(&mut Self) -> ControlFlow<Infallible>,
    ) -> ControlFlow<Infallible> {
        let parent = *self.binder_ctx.last().unwrap();
        let ctx = if is_empty && let Some(&ctx) = self.empty_binder_ctx.get(&parent) {
            ctx
        } else {
            self.last_binder_ctx += 1;
            if is_empty {
                self.empty_binder_ctx.insert(parent, self.last_binder_ctx);
            }
            self.last_binder_ctx
        };
        self.binder_ctx.push(ctx);
        let result = f(self);
        self.binder_ctx.pop();
        result
    }

    /// Check the hash-consed value at `addr` using `check`, unless it was already checked without
    /// errors in the same context. The visitor explores trees, so values shared in a DAG (e.g.
    /// deep trait proofs) would otherwise be checked once per occurrence.
    fn check_once(
        &mut self,
        addr: *const (),
        check: impl FnOnce(&mut Self) -> ControlFlow<Infallible>,
    ) -> ControlFlow<Infallible> {
        let key = (
            addr as usize,
            *self.binder_ctx.last().unwrap(),
            self.accept_type_errors,
        );
        // A value doesn't contain itself, so we can mark it as checked while we check it.
        if !self.checked.insert(key) {
            return Continue(());
        }
        let errors_before = self.error_count.get();
        check(self)?;
        if self.error_count.get() != errors_before {
            self.checked.remove(&key);
        }
        Continue(())
    }

    /// The value of `var` in `env`, if `env` substitutes it.
    fn lookup_var<'e, Id: Idx, T>(
        &mut self,
        var: DeBruijnVar<Id>,
        env: Env<'e>,
        args: impl FnOnce(&'e GenericArgs) -> &'e IndexVec<Id, T>,
    ) -> Result<Option<&'e T>, TypeError> {
        let DeBruijnVar::Bound(dbid, id) = var else {
            return Ok(None);
        };
        let all_args = if dbid == env.depth {
            env.args
        } else if dbid == env.depth.incr() {
            env.outer
        } else {
            None
        };
        if let Some(all_args) = all_args {
            match args(all_args).get(id) {
                Some(arg) => Ok(Some(arg)),
                None => {
                    // Substitution would fail.
                    self.needs_substitution = true;
                    Err(TypeError)
                }
            }
        } else {
            Ok(None)
        }
    }

    fn match_regions(
        &mut self,
        a: &Region,
        ea: Env<'_>,
        b: &Region,
        eb: Env<'_>,
    ) -> Result<(), TypeError> {
        if let Region::Var(var) = a
            && let Some(a) = self.lookup_var(*var, ea, |args| &args.regions)?
        {
            return self.match_regions(a, Env::NONE, b, eb);
        }
        if let Region::Var(var) = b
            && let Some(b) = self.lookup_var(*var, eb, |args| &args.regions)?
        {
            return self.match_regions(a, ea, b, Env::NONE);
        }
        if let (Region::Lub(a), Region::Lub(b)) = (a, b) {
            return self.match_tys(a, ea, b, eb);
        }
        if let (Region::Body(a), Region::Body(b)) = (a, b) {
            self.unify_regions(*a, *b);
        }
        Ok(())
    }

    fn unify_regions(&mut self, a: RegionId, b: RegionId) {
        if let Some(unifier) = &mut self.body_lt_unifier {
            match &mut self.pending_unifications {
                Some(pending) => pending.push((a, b)),
                None => self.did_unify_lifetimes |= unifier.union(a, b),
            }
        }
    }

    /// Run `f`, holding back the lifetime unifications it does. Returns them.
    fn with_pending_unifications<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> R,
    ) -> (R, Vec<(RegionId, RegionId)>) {
        let outer = self.pending_unifications.replace(Vec::new());
        let result = f(self);
        let pending = mem::replace(&mut self.pending_unifications, outer).unwrap();
        (result, pending)
    }

    /// Whether substituting `value` with arguments of these lengths succeeds. This only depends on
    /// the lengths: substitution fails on variables with no corresponding argument, or on size
    /// metadata.
    fn substitution_succeeds(
        &mut self,
        value: SubstitutedValue,
        args: &GenericArgs,
        substitute: impl FnOnce() -> bool,
    ) -> bool {
        *self
            .substitution_cache
            .entry((value, arg_counts(args)))
            .or_insert_with(substitute)
    }

    /// Compare two types for equality. Because we can't use the full power of rustc's type
    /// equality, we err on the side of accepting.
    fn match_tys(&mut self, a: &Ty, ea: Env<'_>, b: &Ty, eb: Env<'_>) -> Result<(), TypeError> {
        // Equal types match (this compares addresses), without side effects, when we don't
        // substitute their variables.
        if a == b && ea.args.is_none() && eb.args.is_none() {
            return Ok(());
        }
        if let TyKind::TypeVar(var) = a.kind()
            && let Some(a) = self.lookup_var(*var, ea, |args| &args.types)?
        {
            return self.match_tys(a, Env::NONE, b, eb);
        }
        if let TyKind::TypeVar(var) = b.kind()
            && let Some(b) = self.lookup_var(*var, eb, |args| &args.types)?
        {
            return self.match_tys(a, ea, b, Env::NONE);
        }
        match (a.kind(), b.kind()) {
            (TyKind::Adt(a), TyKind::Adt(b)) if a.id == b.id => {
                self.match_generics(&a.generics, ea, &b.generics, eb)?
            }
            (TyKind::Adt(a), TyKind::Adt(b))
                if self.ctx.options.monomorphize_with_hax
                    && self.ctx.translated.item_name(a.id).mono_args().is_some()
                        != self.ctx.translated.item_name(b.id).mono_args().is_some() =>
            {
                // FIXME(#856): We translate traits polymorphiclaly, which can give rise to having
                // both the polymorphic and monomophized version of a same type, see e.g.
                // supertrait-with-generic-type-args.rs. We ignore that for now.
            }
            (TyKind::Scalar(a), TyKind::Scalar(b)) if a == b => {}
            (TyKind::Never, TyKind::Never) => {}
            (TyKind::Array(aty, ..), TyKind::Array(bty, ..)) => {
                self.match_tys(aty, ea, bty, eb)?;
            }
            // Comparing the patterns requires their substituted values.
            (TyKind::Pattern(..), TyKind::Pattern(..))
                if (ea.args.is_some() && !a.type_info().is_closed())
                    || (eb.args.is_some() && !b.type_info().is_closed()) =>
            {
                self.needs_substitution = true;
                return Err(TypeError);
            }
            (TyKind::Pattern(aty, apat), TyKind::Pattern(bty, bpat)) if apat == bpat => {
                self.match_tys(aty, ea, bty, eb)?;
            }
            (TyKind::Slice(aty, _), TyKind::Slice(bty, _)) => {
                self.match_tys(aty, ea, bty, eb)?;
            }
            (TyKind::Ref(aregion, aty, akind), TyKind::Ref(bregion, bty, bkind))
                if akind == bkind =>
            {
                self.match_regions(aregion, ea, bregion, eb)?;
                self.match_tys(aty, ea, bty, eb)?;
            }
            (TyKind::RawPtr(aty, akind), TyKind::RawPtr(bty, bkind)) if akind == bkind => {
                self.match_tys(aty, ea, bty, eb)?
            }
            (TyKind::DynTrait(..), TyKind::DynTrait(..)) => {}
            (TyKind::FnPtr(..), TyKind::FnPtr(..)) => {}
            (TyKind::FnDef(..), TyKind::FnDef(..)) => {}
            // We can't decide type equality, so we avoid false positives here.
            (TyKind::TypeVar(_), _) | (_, TyKind::TypeVar(_)) => {}
            (TyKind::TraitType(..), _) | (_, TyKind::TraitType(..)) => {}
            (TyKind::PtrMetadata(..), _) | (_, TyKind::PtrMetadata(..)) => {}
            (TyKind::Error(_), _) | (_, TyKind::Error(_)) => {}
            _ if self.accept_type_errors => {}
            _ => return Err(TypeError),
        }
        Ok(())
    }

    fn match_trait_decl_refs(
        &mut self,
        a: &TraitDeclRef,
        ea: Env<'_>,
        b: &TraitDeclRef,
        eb: Env<'_>,
    ) -> Result<(), TypeError> {
        if a.id != b.id {
            return Err(TypeError);
        }
        self.match_generics(&a.generics, ea, &b.generics, eb)?;
        Ok(())
    }

    fn match_poly_trait_decl_refs(
        &mut self,
        a: &PolyTraitDeclRef,
        ea: Env<'_>,
        b: &PolyTraitDeclRef,
        eb: Env<'_>,
    ) -> Result<(), TypeError> {
        if a == b && ea.args.is_none() && eb.args.is_none() {
            return Ok(());
        }
        // Matching never looks at variables, so we can match under the binders instead of
        // instantiating them.
        self.match_trait_decl_refs(
            &a.skip_binder,
            ea.under_binder(),
            &b.skip_binder,
            eb.under_binder(),
        )
    }

    fn apply_poly_predicate(
        pred: PolyTraitDeclRef,
        args: &RegionArgs,
    ) -> Result<TraitDeclRef, TypeError> {
        if pred.regions.len() != args.regions.len() {
            return Err(TypeError);
        }
        // Matching only looks at body regions and lubs, so if the args have none we can skip
        // instantiating the binder.
        if args
            .regions
            .iter()
            .any(|r| matches!(r, Region::Body(_) | Region::Lub(_)))
        {
            Ok(pred.apply(args.clone()))
        } else {
            Ok(pred.skip_binder)
        }
    }

    fn match_trait_ref_against_itself(&mut self, tref: &TraitRef) -> Result<(), TypeError> {
        let target_pred = match &tref.kind {
            TraitRefKind::Clause(var, args)
                if let Some(clause) = self.binder_stack.get_var(*var) =>
            {
                // We don't move the predicate under the binders between here and the clause:
                // that only changes variables, which matching ignores.
                Self::apply_poly_predicate(clause.trait_.clone(), args)?
            }
            TraitRefKind::ParentClause(parent, clause_id, args)
                if let Some(tdecl) = self.trait_decl(parent.trait_id())
                    && let Some(clause) = tdecl.implied_clauses.get(*clause_id) =>
            {
                let parent_args = &parent.trait_decl_ref.generics;
                let substituted = || {
                    let pred = clause.trait_.clone().try_substitute_with_tref(parent);
                    Self::apply_poly_predicate(pred.map_err(|_| TypeError)?, args)
                };
                // Like `apply_poly_predicate`, we only need to apply the region arguments if they
                // have body regions or lubs.
                let value = SubstitutedValue::ParentClause(parent.trait_id(), *clause_id);
                if clause.trait_.regions.len() == args.regions.len()
                    && !args
                        .regions
                        .iter()
                        .any(|r| matches!(r, Region::Body(_) | Region::Lub(_)))
                    && self.substitution_succeeds(value, parent_args, || substituted().is_ok())
                {
                    let env = Env::new(parent_args).under_binder();
                    let clause_tref = &clause.trait_.skip_binder;
                    return self.match_in_env(&tref.trait_decl_ref, clause_tref, env, substituted);
                }
                substituted()?
            }
            TraitRefKind::ItemClause {
                trait_ref,
                type_id,
                generics,
                clause_id,
                clause_args,
            } if let Some(tdecl) = self.trait_decl(trait_ref.trait_id())
                && let Some(assoc_ty) = tdecl.types.get(*type_id) =>
            {
                if !generics.matches(&assoc_ty.params) {
                    return Err(TypeError);
                }
                // Substitute the type with the trait generics.
                let assoc_ty = assoc_ty
                    .clone()
                    .try_substitute_with_tref(trait_ref)
                    .map_err(|_| TypeError)?;
                // Get the clause from the type and apply the GAT arguments to it.
                let pred = assoc_ty
                    .skip_binder
                    .implied_clauses
                    .get(*clause_id)
                    .ok_or(TypeError)?
                    .trait_
                    .clone()
                    .try_substitute_with_self(generics, &trait_ref.kind.clone().move_under_binder())
                    .map_err(|_| TypeError)?;
                Self::apply_poly_predicate(pred, clause_args)?
            }
            TraitRefKind::TraitImpl(trait_impl_ref)
                if let Some(timpl) = self.trait_impl(trait_impl_ref.id) =>
            {
                let impl_args = &trait_impl_ref.generics;
                let substituted = || {
                    let impl_trait = timpl.impl_trait.clone().try_substitute(impl_args);
                    impl_trait.map_err(|_| TypeError)
                };
                let value = SubstitutedValue::ImplTrait(trait_impl_ref.id);
                if self.substitution_succeeds(value, impl_args, || substituted().is_ok()) {
                    let env = Env::new(impl_args);
                    return self.match_in_env(
                        &tref.trait_decl_ref,
                        &timpl.impl_trait,
                        env,
                        substituted,
                    );
                }
                substituted()?
            }
            _ => return Ok(()),
        };
        self.match_trait_decl_refs(&tref.trait_decl_ref, Env::NONE, &target_pred, Env::NONE)
    }

    /// Match `a` against `b` read in `env`, without substituting it. If that turns out to require
    /// the substituted `b`, we get it from `substituted` instead.
    fn match_in_env(
        &mut self,
        a: &TraitDeclRef,
        b: &TraitDeclRef,
        env: Env<'_>,
        substituted: impl FnOnce() -> Result<TraitDeclRef, TypeError>,
    ) -> Result<(), TypeError> {
        let (result, unifications) =
            self.with_pending_unifications(|this| this.match_trait_decl_refs(a, Env::NONE, b, env));
        if !mem::take(&mut self.needs_substitution) {
            for (x, y) in unifications {
                self.unify_regions(x, y);
            }
            return result;
        }
        self.match_trait_decl_refs(a, Env::NONE, &substituted()?, Env::NONE)
    }

    fn match_poly_trait_ref_against_itself(
        &mut self,
        tref: &PolyTraitRef,
    ) -> Result<(), TypeError> {
        // Like in `match_poly_trait_decl_refs`, we work under the binder instead of instantiating it.
        self.binder_stack.push(tref.0.to_params());
        let result = self.match_trait_ref_against_itself(&tref.0.skip_binder);
        self.binder_stack.pop();
        result
    }

    fn match_poly_trait_refs(
        &mut self,
        a: &PolyTraitRef,
        ea: Env<'_>,
        b: &PolyTraitRef,
        eb: Env<'_>,
    ) -> Result<(), TypeError> {
        self.match_trait_decl_refs(
            &a.0.skip_binder.trait_decl_ref,
            ea.under_binder(),
            &b.0.skip_binder.trait_decl_ref,
            eb.under_binder(),
        )
    }

    fn match_generics(
        &mut self,
        a: &GenericArgs,
        ea: Env<'_>,
        b: &GenericArgs,
        eb: Env<'_>,
    ) -> Result<(), TypeError> {
        if a == b && ea.args.is_none() && eb.args.is_none() {
            return Ok(());
        }
        if a.regions.len() != b.regions.len()
            || a.types.len() != b.types.len()
            || a.const_generics.len() != b.const_generics.len()
            || a.trait_refs.len() != b.trait_refs.len()
        {
            return Err(TypeError);
        }
        for (a, b) in a.regions.iter().zip(b.regions.iter()) {
            self.match_regions(a, ea, b, eb)?;
        }
        for (a, b) in a.types.iter().zip(b.types.iter()) {
            self.match_tys(a, ea, b, eb)?;
        }
        for (a, b) in a.trait_refs.iter().zip(b.trait_refs.iter()) {
            self.match_poly_trait_refs(a, ea, b, eb)?;
        }
        Ok(())
    }
}

impl TypeCheckVisitor<'_> {
    fn check_concretization_ty_match(&self, src_ty: &Ty, tar_ty: &Ty) {
        match (src_ty.kind(), tar_ty.kind()) {
            (TyKind::Ref(.., src_kind), TyKind::Ref(.., tar_kind)) => {
                assert_eq!(src_kind, tar_kind);
            }
            (TyKind::RawPtr(.., src_kind), TyKind::RawPtr(.., tar_kind)) => {
                assert_eq!(src_kind, tar_kind);
            }
            (TyKind::Adt(src), TyKind::Adt(tar)) => {
                if !self.ctx.options.monomorphize_with_hax {
                    assert_eq!(src.id, tar.id);
                } else {
                    // In mono `Box<dyn Trait> -> Box<T>`, have different declarations,
                    // so we compare names instead.
                    let instantiated_from =
                        |id| self.ctx.translated.item_name(id).as_slice_uninstantiated();
                    assert_eq!(instantiated_from(src.id), instantiated_from(tar.id));
                }
            }
            _ => {
                let fmt = &self.ctx.into_fmt();
                self.error(format!(
                    "Invalid concretization targets: from \"{}\" to \"{}\"",
                    src_ty.with_ctx(fmt),
                    tar_ty.with_ctx(fmt)
                ));
            }
        }
    }

    /// For pretty error printing. This can print values that we encounter because we track binders
    /// properly. This doesn't have the right binders to print values we get from somewhere else
    /// (namely the `GenericParam`s we get from elsewhere in the crate).
    fn val_fmt_ctx(&self) -> FmtCtx<'_> {
        let mut fmt = self.ctx.into_fmt();
        fmt.generics = self.binder_stack.map_ref(Cow::Borrowed);
        fmt
    }

    /// For pretty error printing of values that live under the given binders (outermost first).
    /// We only build it on errors, as it's not free.
    fn binders_fmt_ctx<'b>(&'b self, binders: &[&'b GenericParams]) -> FmtCtx<'b> {
        let mut fmt = self.ctx.into_fmt();
        for params in binders {
            fmt.generics.push(Cow::Borrowed(*params));
        }
        fmt
    }

    fn zip_assert_match<'a, I, A, B>(
        &'a mut self,
        a: &'a IndexVec<I, A>,
        b: &IndexVec<I, B>,
        a_binders: &[&'a GenericParams],
        kind: &str,
        target: &GenericsSource,
        check_inner: impl Fn(&mut Self, &A, &B),
    ) -> ControlFlow<()>
    where
        I: Idx,
        A: FmtWithCtx<FmtCtx<'a>>,
        B: FmtWithCtx<FmtCtx<'a>>,
    {
        if a.len() == b.len() {
            a.iter()
                .zip(b.iter())
                .for_each(|(x, y)| check_inner(self, x, y));
            ControlFlow::Continue(())
        } else if let Some(failed) = &self.dry_run {
            failed.set(true);
            ControlFlow::Break(())
        } else {
            let a_fmt = &self.binders_fmt_ctx(a_binders);
            let b_fmt = &self.val_fmt_ctx();
            let a = a.iter().map(|x| x.with_ctx(a_fmt)).join(", ");
            let b = b.iter().map(|x| x.with_ctx(b_fmt)).join(", ");
            let target = target.with_ctx(a_fmt);
            self.error(format!(
                "Mismatched {kind}:\
                \ntarget: {target}\
                \nexpected: [{a}]\
                \n     got: [{b}]"
            ));
            ControlFlow::Break(())
        }
    }

    /// Check that `tref` proves `tclause`. If set, `outer` are the arguments for the binder outside
    /// the one of `tclause`, which haven't been substituted yet; in that case we're in a dry run.
    fn assert_clause_matches(
        &mut self,
        tclause: Substituted<'_, TraitParam>,
        outer: Option<&GenericArgs>,
        tref: &PolyTraitRef,
    ) {
        let expected_regions = tclause.val.trait_.regions.len();
        let actual_regions = tref.0.regions.len();
        if expected_regions != actual_regions {
            let args_fmt = &self.val_fmt_ctx();
            let tref = tref.with_ctx(args_fmt);
            self.error(format!(
                "Mismatched bound regions in trait proof:\
                \nexpected: {expected_regions}\
                \n     got: {actual_regions} in {tref}"
            ));
        }
        // Substituting the clause is costly, so we match it with its arguments on the side when we
        // can. We hold back the lifetime unifications this does, to apply them only if the
        // substitution would succeed.
        let tref_pred = tref.pred();
        let mut matched = None;
        if !tclause.val.type_info().uses_size_metadata() {
            let env = Env {
                outer,
                ..Env::new(tclause.generics)
            };
            let (result, unifications) = self.with_pending_unifications(|this| {
                this.match_poly_trait_decl_refs(&tclause.val.trait_, env, &tref_pred, Env::NONE)
            });
            if !mem::take(&mut self.needs_substitution) {
                matched = Some((result.is_ok(), unifications));
            }
        }
        if outer.is_some() && !matches!(matched, Some((true, _))) {
            // We can't substitute the clause without its outer arguments: let the caller redo the
            // check normally.
            self.dry_run.as_ref().unwrap().set(true);
            return;
        }
        let (clause_matches, unifications) = match matched {
            Some(matched) => matched,
            None => {
                let Ok(clause) = tclause.try_substitute() else {
                    return;
                };
                let result = self.match_poly_trait_decl_refs(
                    &clause.trait_,
                    Env::NONE,
                    &tref_pred,
                    Env::NONE,
                );
                (result.is_ok(), Vec::new())
            }
        };
        let mismatched_clause = if clause_matches {
            None
        } else {
            // If the substitution fails there's nothing to check.
            let Ok(clause) = tclause.try_substitute() else {
                return;
            };
            Some(clause)
        };
        for (a, b) in unifications {
            self.unify_regions(a, b);
        }
        if let Some(clause) = mismatched_clause {
            let args_fmt = &self.val_fmt_ctx();
            let clause = clause.with_ctx(args_fmt);
            let tref_pred = tref_pred.with_ctx(args_fmt);
            let tref = tref.with_ctx(args_fmt);
            self.error(format!(
                "Mismatched trait clause:\
                \nexpected: {clause}\
                \n     got: {tref}: {tref_pred}"
            ));
        } else if self.match_poly_trait_ref_against_itself(tref).is_err() {
            let args_fmt = &self.val_fmt_ctx();
            let tref_pred = tref_pred.with_ctx(args_fmt);
            let tref = tref.with_ctx(args_fmt);
            self.error(format!(
                "Incoherent trait reference:\
                \n     got: {tref}: {tref_pred}"
            ));
        }
    }

    fn assert_clauses_match(
        &mut self,
        params_binders: &[&GenericParams],
        clauses: Substituted<'_, IndexVec<TraitClauseId, TraitParam>>,
        outer: Option<&GenericArgs>,
        trefs: &IndexVec<TraitClauseId, PolyTraitRef>,
        kind: &str,
        target: &GenericsSource,
    ) {
        let _ = self.zip_assert_match(
            clauses.val,
            trefs,
            params_binders,
            kind,
            target,
            |this, tclause, tref| this.assert_clause_matches(clauses.rebind(tclause), outer, tref),
        );
    }

    /// Check `args` against `params`. If set, `outer` are the arguments for the binder outside
    /// `params`, which haven't been substituted yet; in that case we're in a dry run.
    fn assert_matches(
        &mut self,
        params_binders: &[&GenericParams],
        params: &GenericParams,
        outer: Option<&GenericArgs>,
        args: &GenericArgs,
        target: &GenericsSource,
    ) -> ControlFlow<()> {
        self.zip_assert_match(
            &params.regions,
            &args.regions,
            params_binders,
            "regions",
            target,
            |_, _, _| {},
        )?;
        self.zip_assert_match(
            &params.types,
            &args.types,
            params_binders,
            "type generics",
            target,
            |_, _, _| {},
        )?;
        self.zip_assert_match(
            &params.const_generics,
            &args.const_generics,
            params_binders,
            "const generics",
            target,
            |_, _, _| {},
        )?;
        self.assert_clauses_match(
            params_binders,
            Substituted::new(&params.trait_clauses, args),
            outer,
            &args.trait_refs,
            "trait clauses",
            target,
        );
        ControlFlow::Continue(())
    }

    fn assert_matches_item(&mut self, id: impl Into<ItemId>, args: &GenericArgs) {
        let id = id.into();
        let Some(item) = self.get_item(id) else {
            return;
        };
        let params = item.generic_params();
        let _ = self.assert_matches(&[params], params, None, args, &GenericsSource::item(id));
    }

    fn assert_matches_method(
        &mut self,
        trait_ref: &TraitRef,
        method_id: TraitMethodId,
        args: &GenericArgs,
    ) {
        let trait_id = trait_ref.trait_decl_ref.id;
        let target = &GenericsSource::Method(trait_id, method_id);
        let Some(trait_decl) = self.trait_decl(trait_id) else {
            return;
        };
        let Some(bound_fn) = trait_decl.methods.get(method_id) else {
            return;
        };
        let value = SubstitutedValue::Method(trait_id, method_id);
        self.assert_matches_trait_item(trait_ref, trait_decl, bound_fn, value, args, target);
    }

    fn assert_matches_trait_type(
        &mut self,
        trait_ref: &TraitRef,
        type_id: AssocTypeId,
        args: &GenericArgs,
    ) {
        let trait_id = trait_ref.trait_id();
        let target = &GenericsSource::TraitType(trait_id, type_id);
        let Some(trait_decl) = self.trait_decl(trait_id) else {
            return;
        };
        let Some(bound_ty) = trait_decl.types.get(type_id) else {
            return;
        };
        let value = SubstitutedValue::AssocTy(trait_id, type_id);
        self.assert_matches_trait_item(trait_ref, trait_decl, bound_ty, value, args, target);
    }

    /// Check `args` against the params of `bound`, an item of the trait `trait_ref` refers to.
    fn assert_matches_trait_item<T>(
        &mut self,
        trait_ref: &TraitRef,
        trait_decl: &TraitDecl,
        bound: &Binder<T>,
        value: SubstitutedValue,
        args: &GenericArgs,
        target: &GenericsSource,
    ) where
        Binder<T>: TyVisitable + Clone,
    {
        let trait_args = &trait_ref.trait_decl_ref.generics;
        let substituted = || Substituted::new_for_trait_ref(bound, trait_ref).try_substitute();
        // If the substitution fails there's nothing to check.
        if !self.substitution_succeeds(value, trait_args, || substituted().is_ok()) {
            return;
        }
        // Substituting the trait arguments into the item is costly, so we first check its params
        // with them on the side. If that runs into anything, we redo the check normally, which
        // reports the errors.
        if self.dry_run.is_none() {
            self.dry_run = Some(Cell::new(false));
            let (_, unifications) = self.with_pending_unifications(|this| {
                this.assert_matches(&[], &bound.params, Some(trait_args), args, target)
            });
            let failed = self.dry_run.take().unwrap().into_inner();
            if !failed {
                for (a, b) in unifications {
                    self.unify_regions(a, b);
                }
                return;
            }
        }
        let bound = substituted().unwrap();
        let binders = [&trait_decl.generics, &bound.params];
        let _ = self.assert_matches(&binders, &bound.params, None, args, target);
    }
}

impl VisitAst for TypeCheckVisitor<'_> {
    fn visit<T: AstVisitable>(&mut self, x: &T) -> ControlFlow<Self::Break> {
        self.visit_stack.push(x.name());
        VisitWithSpan::new(VisitWithBinderStack::new(self)).visit(x)?;
        self.visit_stack.pop();
        Continue(())
    }

    fn visit_binder<T: AstVisitable>(&mut self, binder: &Binder<T>) -> ControlFlow<Self::Break> {
        let old_accept_type_errors = self.accept_type_errors;
        // Default methods with unapplicable type constraints can give rise to type mismatches;
        // seems to happen mostly when lifting associated types, so we skip typechecking in that
        // case.
        self.accept_type_errors |= matches!(&binder.kind, BinderKind::TraitMethod(..))
            && !self.ctx.options.lift_associated_types.is_empty()
            && !binder.params.trait_type_constraints.is_empty();
        let result =
            self.with_binder_ctx(binder.params.is_empty(), |this| this.visit_inner(binder));
        self.accept_type_errors = old_accept_type_errors;
        result
    }

    fn visit_region_binder<T: AstVisitable>(
        &mut self,
        binder: &RegionBinder<T>,
    ) -> ControlFlow<Self::Break> {
        self.with_binder_ctx(binder.regions.is_empty(), |this| this.visit_inner(binder))
    }

    fn visit_ty(&mut self, x: &Ty) -> ControlFlow<Self::Break> {
        self.check_once(x.0.inner() as *const _ as *const (), |this| {
            this.visit_inner(x)
        })
    }
    fn visit_trait_ref(&mut self, x: &TraitRef) -> ControlFlow<Self::Break> {
        self.check_once(x.0.inner() as *const _ as *const (), |this| {
            this.enter_trait_ref(x);
            this.visit_inner(x)
        })
    }
    fn visit_constant_expr(&mut self, x: &ConstantExpr) -> ControlFlow<Self::Break> {
        self.check_once(x.0.inner() as *const _ as *const (), |this| {
            this.enter_constant_expr(x);
            this.visit_inner(x)
        })
    }

    // Check that generics are correctly bound.
    fn enter_region(&mut self, x: &Region) {
        if let Region::Var(var) = x
            && self.binder_stack.get_var(*var).is_none()
        {
            self.error(format!("Found incorrect region var: {var}"));
        }
    }
    fn enter_ty_kind(&mut self, x: &TyKind) {
        match x {
            TyKind::TypeVar(var) if self.binder_stack.get_var(*var).is_none() => {
                self.error(format!("Found incorrect type var: {var}"));
            }
            TyKind::TraitType(trait_ref, type_id, args) => {
                self.assert_matches_trait_type(trait_ref, *type_id, args);
            }
            _ => {}
        }
    }
    fn enter_constant_expr(&mut self, x: &ConstantExpr) {
        if let ConstantExprKind::Var(var) = x.kind()
            && self.binder_stack.get_var(*var).is_none()
        {
            self.error(format!("Found incorrect const-generic var: {var}"));
        }
    }
    fn enter_trait_ref(&mut self, x: &TraitRef) {
        match &x.kind {
            TraitRefKind::Clause(var, args) => match self.binder_stack.get_var(*var) {
                None => self.error(format!("Found incorrect clause var: {var}")),
                Some(clause) if args.regions.len() != clause.trait_.regions.len() => {
                    self.error(format!(
                        "Clause {var} expects {} region args, got {}",
                        clause.trait_.regions.len(),
                        args.regions.len()
                    ))
                }
                Some(_) => {}
            },
            TraitRefKind::ParentClause(parent, clause_id, args) => {
                if let Some(clause) = self
                    .trait_decl(parent.trait_id())
                    .and_then(|decl| decl.implied_clauses.get(*clause_id))
                    && args.regions.len() != clause.trait_.regions.len()
                {
                    self.error(format!(
                        "Parent clause {clause_id} expects {} region args, got {}",
                        clause.trait_.regions.len(),
                        args.regions.len()
                    ));
                }
            }
            TraitRefKind::ItemClause {
                trait_ref,
                type_id,
                generics,
                clause_id,
                clause_args,
            } => {
                self.assert_matches_trait_type(trait_ref, *type_id, generics);
                if let Some(clause) = self
                    .trait_decl(trait_ref.trait_id())
                    .and_then(|decl| decl.types.get(*type_id))
                    .and_then(|assoc_ty| assoc_ty.skip_binder.implied_clauses.get(*clause_id))
                    && clause_args.regions.len() != clause.trait_.regions.len()
                {
                    self.error(format!(
                        "Item clause {clause_id} expects {} region args, got {}",
                        clause.trait_.regions.len(),
                        clause_args.regions.len()
                    ));
                }
            }
            TraitRefKind::BuiltinOrAuto {
                parent_trait_refs,
                types,
                ..
            } => {
                let trait_id = x.trait_decl_ref.id;
                let target = GenericsSource::item(trait_id);
                let Some(tdecl) = self.trait_decl(trait_id) else {
                    return;
                };
                if tdecl.item_meta.lang_item.as_ref().is_some_and(|item| {
                    matches!(
                        item,
                        from_rustc::LangItem::PointeeTrait | from_rustc::LangItem::DiscriminantKind
                    )
                }) {
                    // These traits have builtin assoc types that we can't resolve.
                    return;
                }

                let substituted_clauses = Substituted::new_for_trait_ref(&tdecl.implied_clauses, x);
                self.assert_clauses_match(
                    &[],
                    substituted_clauses,
                    None,
                    parent_trait_refs,
                    "builtin trait parent clauses",
                    &target,
                );

                let types_match = types.elem_count() == tdecl.types.elem_count();
                if !types_match {
                    let args_fmt = &self.val_fmt_ctx();
                    let target = target.with_ctx(args_fmt);
                    let a = tdecl.types.iter().map(|t| t.name()).format(", ");
                    let b = types
                        .iter()
                        .map(|assoc_ty| assoc_ty.value.with_ctx(args_fmt))
                        .format(", ");
                    self.error(format!(
                        "Mismatched types in builtin trait ref:\
                        \ntarget: {target}\
                        \nexpected: [{a}]\
                        \n     got: [{b}]"
                    ));
                }
            }
            _ => {}
        }
    }

    // Check that generics match the parameters of the target item.
    fn enter_type_decl_ref(&mut self, x: &TypeDeclRef) {
        // With `--no-gen-tuple-structs`, a tuple stores its field types in its generics while
        // pointing to the parameter-less opaque unit declaration, so the two don't match.
        if x.is_tuple() && self.ctx.options.no_gen_tuple_structs {
            return;
        }
        self.assert_matches_item(x.id, &x.generics)
    }
    fn enter_fun_decl_ref(&mut self, x: &FunDeclRef) {
        self.assert_matches_item(x.id, &x.generics);
    }
    fn enter_fn_ptr(&mut self, x: &FnPtr) {
        match x.kind.as_ref() {
            FnPtrKind::Fun(id) => self.assert_matches_item(*id, &x.generics),
            FnPtrKind::Trait(trait_ref, method_id) => {
                self.assert_matches_method(trait_ref, *method_id, &x.generics);
            }
        }
    }
    fn visit_rvalue(&mut self, x: &Rvalue) -> ::std::ops::ControlFlow<Self::Break> {
        if let Rvalue::UnaryOp(UnOp::Cast(CastKind::Concretize(tar, _)), operand) = x {
            self.check_concretization_ty_match(operand.ty(), tar);
        }
        Continue(())
    }
    fn enter_global_decl_ref(&mut self, x: &GlobalDeclRef) {
        self.assert_matches_item(x.id, &x.generics);
    }
    fn enter_trait_decl_ref(&mut self, x: &TraitDeclRef) {
        // TODO: don't we need to pass the trait_self for correctness here?
        self.assert_matches_item(x.id, &x.generics);
    }
    fn enter_trait_impl_ref(&mut self, x: &TraitImplRef) {
        self.assert_matches_item(x.id, &x.generics);
    }
    fn enter_trait_impl(&mut self, timpl: &TraitImpl) {
        let Some(tdecl) = self.trait_decl(timpl.impl_trait.id) else {
            return;
        };

        let impl_tref_kind = TraitRefKind::TraitImpl(TraitImplRef {
            id: timpl.def_id,
            generics: BoxedArgs::new(timpl.generics.identity_args()),
        });
        let implied_clauses = Substituted::new_for_trait(
            &tdecl.implied_clauses,
            &timpl.impl_trait.generics,
            &impl_tref_kind,
        );
        self.assert_clauses_match(
            &[&tdecl.generics],
            implied_clauses,
            None,
            &timpl.implied_trait_refs,
            "trait parent clauses",
            &GenericsSource::item(timpl.impl_trait.id),
        );
        let types_match = timpl.types.elem_count() == tdecl.types.elem_count();
        if !types_match {
            self.error(
                "The associated types supplied by the trait impl don't match the trait decl.",
            )
        }
        for (type_id, impl_ty) in timpl.types.iter_indexed() {
            let Some(decl_ty) = tdecl.types.get(type_id) else {
                continue;
            };
            let Ok(decl_ty) =
                Substituted::new_for_trait(decl_ty, &timpl.impl_trait.generics, &impl_tref_kind)
                    .try_substitute()
            else {
                continue;
            };
            let item_args = impl_ty.params.identity_args();
            let clauses = Substituted::new(&decl_ty.skip_binder.implied_clauses, &item_args);
            self.assert_clauses_match(
                &[&tdecl.generics, &decl_ty.params],
                clauses,
                None,
                &impl_ty.skip_binder.implied_trait_refs,
                "associated type clauses",
                &GenericsSource::TraitType(tdecl.def_id, type_id),
            );
        }
        let consts_match = timpl.consts.elem_count() == tdecl.consts.elem_count();
        if !consts_match {
            self.error(
                "The associated consts supplied by the trait impl don't match the trait decl.",
            )
        }
        let methods_match = timpl.methods.elem_count() == tdecl.methods.elem_count();
        if !methods_match && self.phase != Check::PostTranslation {
            let fmt1 = &self.ctx.into_fmt();
            let decl_methods = tdecl
                .methods()
                .map(|m| format!("- {}", m.name()))
                .join("\n");
            let impl_methods = timpl
                .methods
                .iter_enumerated()
                .map(|(id, _)| {
                    std::fmt::from_fn(move |f| {
                        write!(f, "- ")?;
                        fmt1.format_method_name(f, tdecl.def_id, id)
                    })
                })
                .join("\n");
            self.error(format!(
                "The methods supplied by the trait impl don't match the trait decl.\n\
                Trait methods:\n{decl_methods}\n\
                Impl methods:\n{impl_methods}"
            ))
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Check {
    /// Check that generics match and unify body lifetimes on a best-effort basis.
    PostTranslation,
    /// Check that generics match.
    PostTransformation,
}

impl Check {
    fn name(&self) -> &'static str {
        match self {
            Check::PostTranslation => "after translation",
            Check::PostTransformation => "after transformations",
        }
    }
}

impl TransformPass for Check {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        !options.no_typecheck
    }
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Whether a substitution succeeds doesn't depend on the item being checked, so each thread
        // can keep its own cache.
        let substitution_caches = PerThread::<HashMap<(SubstitutedValue, [usize; 4]), bool>>::new();
        // The `checked` sets are per item; we reuse their allocations.
        let checked_sets = PerThread::<HashSet<(usize, u32, bool)>>::new();
        // Check the items in parallel, then apply the lifetime unifications we computed.
        let unifications = ctx.par_for_each_item(|ctx, item| {
            if item.item_meta().has_errors {
                return None;
            }
            // Accept type errors within copies of default methods. See docs for
            // `accept_type_errors` for why.
            let accept_type_errors = matches!(
                item,
                ItemRef::Fun(FunDecl {
                    src: FunSource::TraitImpl {
                        reuses_default: true,
                        ..
                    },
                    ..
                })
            );
            let body_lt_unifier = if let ItemRef::Fun(fun_decl) = item
                && let Body::Unstructured(GExprBody {
                    bound_body_regions, ..
                })
                | Body::Structured(GExprBody {
                    bound_body_regions, ..
                }) = &fun_decl.body
            {
                Some(UnionFind::new(*bound_body_regions))
            } else {
                None
            };
            let mut checked = checked_sets.get();
            // Don't keep the large table of an exceptionally large item for all later items.
            if checked.capacity() > 1 << 12 {
                *checked = HashSet::default();
            } else {
                checked.clear();
            }
            let mut visitor = TypeCheckVisitor {
                ctx,
                item_id: item.id(),
                phase: *self,
                span: Span::dummy(),
                binder_stack: BindingStack::empty(),
                visit_stack: Default::default(),
                body_lt_unifier,
                did_unify_lifetimes: false,
                pending_unifications: None,
                needs_substitution: false,
                dry_run: None,
                substitution_cache: &mut substitution_caches.get(),
                accept_type_errors,
                binder_ctx: vec![0],
                empty_binder_ctx: HashMap::default(),
                last_binder_ctx: 0,
                checked: &mut checked,
                error_count: Cell::new(0),
            };
            // Typecheck the item, and accumulate needed lifetime unifications.
            let _ = item.drive(&mut visitor);
            if visitor.did_unify_lifetimes {
                visitor.body_lt_unifier
            } else {
                None
            }
        });
        #[derive(Visitor)]
        struct UnifyBodyRegions(UnionFind<RegionId>);
        impl VisitAstMut for UnifyBodyRegions {
            fn visit_with_cached_type_info<T: AstVisitable + HashConsable>(
                &mut self,
                value: &mut HashConsed<WithCachedTypeInfo<T>>,
            ) -> ControlFlow<Self::Break> {
                // Avoid cloning and re-interning values without body regions.
                if !value.type_info().has_erased_or_body_regions() {
                    return Continue(());
                }
                self.visit_inner(value)
            }
            fn enter_region(&mut self, r: &mut Region) {
                if let Region::Body(body_id) = r {
                    *body_id = self.0.find_mut(*body_id);
                }
            }
        }
        let mut unifiers: HashMap<FunDeclId, UnionFind<RegionId>> = unifications
            .into_iter()
            .filter_map(|(id, unifier)| Some((*id.as_fun()?, unifier??)))
            .collect();
        ctx.translated
            .fun_decls
            .iter_mut()
            .filter_map(|decl| Some((unifiers.remove(&decl.def_id)?, &mut decl.body)))
            .collect_vec()
            .into_par_iter()
            .for_each(|(unifier, body)| {
                let _ = UnifyBodyRegions(unifier).visit(body);
            });
    }
}
