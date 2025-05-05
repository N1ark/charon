use std::{
    collections::HashMap,
    ops::ControlFlow::{self, Continue},
};

use derive_generic_visitor::Visitor;

use super::{ctx::UllbcPass, TransformCtx};

use crate::ullbc_ast::*;

#[derive(Visitor)]
struct InsertRegions<'a> {
    regions: &'a mut Vector<RegionId, RegionVar>,
    // The number of region groups we dived into (we don't count the regions
    // at the declaration level). We use this for the DeBruijn indices.
    depth: usize,
}

impl VisitAstMut for InsertRegions<'_> {
    fn exit_region(&mut self, r: &mut Region) {
        if r == &Region::Erased {
            // Insert a fresh region
            let index = self
                .regions
                .push_with(|index| RegionVar { index, name: None });
            *r = Region::Var(DeBruijnVar::bound(DeBruijnId::new(self.depth), index));
        }
    }

    fn visit_region_binder<T: AstVisitable>(
        &mut self,
        x: &mut RegionBinder<T>,
    ) -> ControlFlow<Self::Break> {
        self.depth += 1;
        self.visit_inner(x)?;
        self.depth -= 1;
        Continue(())
    }
}

fn adt_of_closure(krate: &mut TranslatedCrate, closure: &FunDeclId) -> TypeDeclId {
    let FunDecl {
        item_meta,
        signature: FunSig {
            closure_info: Some(closure_info),
            ..
        },
        ..
    } = krate.fun_decls.get(*closure).unwrap()
    else {
        unreachable!("closure info is missing");
    };

    let mut generics = GenericParams::empty();

    let mut state: Vector<FieldId, Field> = closure_info
        .state
        .iter()
        .map(|ty| Field {
            span: item_meta.span,
            attr_info: AttrInfo {
                attributes: vec![],
                inline: None,
                rename: None,
                public: true,
            },
            name: None,
            ty: ty.clone(),
        })
        .collect();

    let mut region_visitor = InsertRegions {
        regions: &mut generics.regions,
        depth: 0,
    };
    let _ = region_visitor.visit(&mut state);

    let closure_path = PathElem::Ident("state".into(), Disambiguator::ZERO);
    let mut item_meta = item_meta.clone();
    item_meta.name.name.push(closure_path);

    krate.type_decls.push_with(|i| TypeDecl {
        def_id: i,
        item_meta,
        generics,
        kind: TypeDeclKind::Struct(state),
    })
}

#[derive(Visitor)]
struct ClosureVisitor<'ctx> {
    subst: &'ctx HashMap<FunDeclId, TypeDeclId>,
}

impl<'ctx> ClosureVisitor<'ctx> {
    fn new(subst: &'ctx HashMap<FunDeclId, TypeDeclId>) -> Self {
        Self { subst }
    }
}

impl<'ctx> VisitAstMut for ClosureVisitor<'ctx> {
    fn visit_ty(&mut self, ty: &mut Ty) -> ControlFlow<Self::Break> {
        ty.with_kind_mut(|ty_kind| match ty_kind {
            TyKind::Closure { fun_id, .. } => {
                if let Some(adt_id) = self.subst.get(fun_id) {
                    *ty_kind = TyKind::Adt(
                        TypeId::Adt(*adt_id),
                        GenericArgs::empty(GenericsSource::Item(AnyTransId::Fun(*fun_id))),
                    )
                };
                Continue(())
            }
            ty_k => self.visit_inner(ty_k),
        })
    }

    fn visit_aggregate_kind(&mut self, ak: &mut AggregateKind) -> ControlFlow<Self::Break> {
        let AggregateKind::Closure(fid, args) = ak else {
            return Continue(());
        };
        let adt_id = self.subst.get(fid).unwrap();
        *ak = AggregateKind::Adt(TypeId::Adt(*adt_id), None, None, args.clone());
        Continue(())
    }
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Get the trait declarations for FnOnce, FnMut and Fn
        // If closures are mentioned, these must exist in the translated crate, since calling
        // the closure uses them.
        let lang_items = ctx
            .translated
            .trait_decls
            .iter()
            .filter_map(|t| {
                t.item_meta
                    .lang_item
                    .as_ref()
                    .map(|l| (l.clone(), t.clone()))
            })
            .collect::<HashMap<_, _>>();
        let fn_once_trait = lang_items.get("fn_once".into());
        let fn_mut_trait = lang_items.get("fn_mut".into());
        let fn_trait = lang_items.get("r#fn".into());

        // 1. Generate the new type declarations
        let closures = ctx
            .translated
            .fun_decls
            .iter()
            .filter(|f| f.signature.is_closure)
            .map(|f| f.def_id)
            .collect::<Vec<_>>();
        let closure_map = closures
            .iter()
            .map(|f| {
                let adt_id = adt_of_closure(&mut ctx.translated, f);
                (*f, adt_id)
            })
            .collect::<HashMap<_, _>>();

        // 2. Implement the Fn.. traits
        closures.iter().for_each(|fid| {
            let adt_id = closure_map.get(fid).unwrap();
            let fun = ctx.translated.fun_decls.get(*fid).unwrap();
            let kind = fun.signature.closure_info.as_ref().unwrap().kind;

            let item_meta = fun.item_meta.clone();
            let generics_source = GenericsSource::Item(AnyTransId::Fun(*fid));
            let fn_generics = vec![
                TyKind::Adt(
                    TypeId::Adt(*adt_id),
                    GenericArgs::empty(generics_source.clone()),
                )
                .into_ty(),
                TyKind::Adt(
                    TypeId::Tuple,
                    GenericArgs::new(
                        Vector::new(),
                        fun.signature.inputs.clone().into(),
                        Vector::new(),
                        Vector::new(),
                        generics_source.clone(),
                    ),
                )
                .into_ty(),
            ]
            .into();
            let generics = GenericArgs::new(
                Vector::new(),
                fn_generics,
                Vector::new(),
                Vector::new(),
                generics_source.clone(),
            );

            // The inheritance order is FnOnce -> FnMut -> Fn
            if matches!(kind, ClosureKind::Fn) {
                let fn_trait = (*fn_trait.unwrap()).clone();
                let id = ctx.translated.trait_impls.push_with(|def_id| TraitImpl {
                    def_id,
                    impl_trait: TraitDeclRef {
                        trait_id: fn_trait.def_id,
                        generics,
                    },
                    item_meta,
                    generics: fun.signature.generics.clone(),
                    parent_trait_refs: Vector::new(),
                    consts: vec![],
                    types: vec![(TraitItemName("Output".into()), fun.signature.output.clone())],
                    type_clauses: vec![],
                    methods: vec![(
                        TraitItemName("call".into()),
                        Binder::new(
                            BinderKind::TraitMethod(fn_trait.def_id, TraitItemName("call".into())),
                            fun.signature.generics.clone(),
                            FunDeclRef {
                                id: *fid,
                                generics: GenericArgs::empty(generics_source.clone()),
                            },
                        ),
                    )],
                });
            }
            if matches!(kind, ClosureKind::Fn | ClosureKind::FnMut) {
                //todo
            }
        });

        // 3. Substitute their uses:
        let mut closure_visitor = ClosureVisitor::new(&closure_map);
        ctx.for_each_fun_decl(|_ctx, fun| {
            let _ = fun.drive_mut(&mut closure_visitor);
        });
    }
}
