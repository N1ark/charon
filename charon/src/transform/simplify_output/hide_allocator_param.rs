use derive_generic_visitor::*;
use itertools::Itertools;
use rustc_hash::FxHashSet as HashSet;

use crate::{ast::*, name_matcher::NamePattern};

use crate::transform::{
    TransformCtx,
    ctx::{PerThread, TransformPass},
};

#[derive(Visitor)]
struct RemoveLastParamVisitor<'a> {
    types: &'a HashSet<TypeDeclId>,
    /// The bloom filter of `types`, to skip values that can't mention them.
    types_bloom: ItemBloom,
    memo: HashConsMemo<()>,
}

// The rewrite only depends on `types`, so it can be reused for every occurrence of a value.
impl VisitorWithMemo for RemoveLastParamVisitor<'_> {
    type MemoContext = ();
    fn memo(&mut self) -> &mut HashConsMemo<()> {
        &mut self.memo
    }
    fn memo_context(&self) -> Option<()> {
        Some(())
    }
}

impl VisitAstMut for RemoveLastParamVisitor<'_> {
    fn visit_with_cached_type_info<T: AstVisitable + HashConsable>(
        &mut self,
        x: &mut HashConsed<WithCachedTypeInfo<T>>,
    ) -> ControlFlow<Self::Break> {
        if !x.type_info().items.intersects(self.types_bloom) {
            return Continue(());
        }
        self.visit_memoized(x)
    }

    fn enter_type_decl_ref(&mut self, x: &mut TypeDeclRef) {
        if self.types.contains(&x.id) {
            // Remove the last param.
            x.generics.with_mut(|args| args.types.pop());
        }
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        if !ctx.options.hide_allocator {
            return;
        }
        let types = &[
            "alloc::boxed::Box",
            "alloc::vec::Vec",
            "alloc::rc::Rc",
            "alloc::sync::Arc",
        ];

        let types: Vec<NamePattern> = types
            .iter()
            .map(|s| NamePattern::parse(s).unwrap())
            .collect_vec();
        let types: HashSet<TypeDeclId> = ctx
            .translated
            .item_names
            .iter()
            .filter(|(_, name)| types.iter().any(|p| p.matches(&ctx.translated, name)))
            .filter_map(|(id, _)| id.as_type())
            .copied()
            .collect();

        for &id in &types {
            if let Some(tdecl) = ctx.translated.type_decls.get_mut(id) {
                if tdecl.generics.types.is_empty() {
                    // We monomorpohized this type.
                    let args = tdecl.item_meta.name.mono_args_mut().unwrap();
                    args.types.pop().unwrap();
                } else {
                    struct SubstWithErrorVisitor(TypeVarId);
                    impl VarsVisitor for SubstWithErrorVisitor {
                        fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
                            if let DeBruijnVar::Bound(DeBruijnId::ZERO, var_id) = v
                                && var_id == self.0
                            {
                                Some(
                                    TyKind::Error("removed allocator parameter".to_owned())
                                        .into_ty(),
                                )
                            } else {
                                None
                            }
                        }
                    }
                    let tvar = tdecl.generics.types.pop().unwrap();
                    tdecl.visit_vars(&mut SubstWithErrorVisitor(tvar.index));
                }
            }
        }

        let types_bloom = types.iter().map(|&id| ItemBloom::of(id)).collect();
        ctx.par_drive_mut(&PerThread::new_with(|| RemoveLastParamVisitor {
            types_bloom,
            types: &types,
            memo: Default::default(),
        }));
    }
}
