//! Virtual impls are trait impls that rustc provides without source code, e.g. `impl Destruct for
//! T` for every type. We generate a trait impl whose required methods are methods of our own, with
//! bodies we get from rustc; the other methods of the trait use their default. For `Destruct` we
//! instead generate a single `drop_glue` method. The per-kind specifics are in the `match`es on
//! [`VirtualImplKind`] below.
use super::translate_ctx::*;
use crate::hax;
use crate::translate::translate_crate::{TransItemSourceKind, VirtualImplKind};
use charon_lib::ast::*;

impl VirtualImplKind {
    pub fn virtual_trait(self) -> hax::VirtualTrait {
        match self {
            VirtualImplKind::Destruct => hax::VirtualTrait::Destruct,
            VirtualImplKind::Callable(ClosureKind::FnOnce) => hax::VirtualTrait::FnOnce,
            VirtualImplKind::Callable(ClosureKind::FnMut) => hax::VirtualTrait::FnMut,
            VirtualImplKind::Callable(ClosureKind::Fn) => hax::VirtualTrait::Fn,
            VirtualImplKind::Clone => hax::VirtualTrait::Clone,
            VirtualImplKind::FnPtr => hax::VirtualTrait::FnPtr,
        }
    }

    /// Whether the methods we generate take `self` by reference. If so, they take an extra
    /// lifetime parameter for that borrow. This must hold of all the methods we generate for this
    /// kind of impl.
    pub fn has_self_borrow(self) -> bool {
        !matches!(
            self,
            VirtualImplKind::Callable(ClosureKind::FnOnce) | VirtualImplKind::FnPtr
        )
    }
}

impl<'tcx> ItemTransCtx<'tcx, '_> {
    /// The id of the method we generate, within the implemented trait.
    fn virtual_method_id(
        &mut self,
        kind: VirtualImplKind,
        vimpl: &hax::VirtualTraitImpl<'tcx>,
        trait_id: TraitDeclId,
        method_idx: usize,
    ) -> Result<TraitMethodId, Error> {
        match kind {
            VirtualImplKind::Destruct => {
                self.translate_drop_glue_method_id(&vimpl.trait_pred.trait_ref.def_id, trait_id)
            }
            VirtualImplKind::Callable(_) | VirtualImplKind::Clone | VirtualImplKind::FnPtr => {
                self.translate_trait_method_id(trait_id, &vimpl.methods[method_idx].def_id)
            }
        }
    }

    fn virtual_method_sig(
        &mut self,
        kind: VirtualImplKind,
        span: Span,
        vimpl: &hax::VirtualTraitImpl<'tcx>,
        method_idx: usize,
        self_ty: Ty,
    ) -> Result<FunSig, Error> {
        let self_borrow_region = self
            .the_only_binder()
            .self_borrow_region
            .map(|rid| Region::Var(DeBruijnVar::new_at_zero(rid)));
        Ok(match kind {
            VirtualImplKind::Destruct => {
                self.drop_glue_method_sig(self_ty, self_borrow_region.unwrap())
            }
            VirtualImplKind::Callable(_) | VirtualImplKind::Clone | VirtualImplKind::FnPtr => self
                .translate_poly_fun_sig(span, &vimpl.methods[method_idx].sig)?
                .apply(self_borrow_region.into_iter().collect()),
        })
    }

    fn virtual_method_body(
        &mut self,
        kind: VirtualImplKind,
        span: Span,
        def: &hax::FullDef<'tcx>,
        vimpl: &hax::VirtualTraitImpl<'tcx>,
        method_idx: usize,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        match kind {
            VirtualImplKind::Destruct => self.translate_drop_glue_method_body(span, def),
            VirtualImplKind::Callable(target_kind) => {
                self.translate_callable_method_body(span, def, target_kind, signature)
            }
            VirtualImplKind::Clone | VirtualImplKind::FnPtr => {
                let body = vimpl
                    .method_shim(self.hax_state(), &vimpl.methods[method_idx].def_id)
                    .expect("required methods of built-in impls are implemented by a shim");
                Ok(self.translate_body(span, body, &def.source_text))
            }
        }
    }

    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_virtual_impl(
        mut self,
        impl_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
        kind: VirtualImplKind,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;
        let vimpl = def.virtual_impl(self.hax_state(), kind.virtual_trait());
        let mut timpl = self.translate_virtual_trait_impl(
            impl_id,
            item_meta,
            def.this(),
            TransImplSource::Virtual(kind),
            vimpl,
        )?;

        // In mono mode, trait decls have no methods (except for the `drop_glue` we add to
        // `Destruct`). Calls are resolved directly to the method, see
        // `translate_bound_fn_ptr_maybe_enqueue`.
        if self.monomorphize() && kind != VirtualImplKind::Destruct {
            return Ok(timpl);
        }

        // Add the methods we generate: `drop_glue` for `Destruct`, the required methods of the
        // trait otherwise. They take the impl generics, plus a lifetime for the borrow of `self` if
        // they take `self` by reference.
        let trait_id = timpl.impl_trait.id;
        let generated_methods: Vec<usize> = match kind {
            VirtualImplKind::Destruct => vec![0],
            _ => (0..vimpl.methods.len())
                .filter(|&i| !vimpl.methods[i].has_default)
                .collect(),
        };
        for method_idx in generated_methods {
            let method_id = self.virtual_method_id(kind, vimpl, trait_id, method_idx)?;
            let fun_id = self.register_item(
                span,
                def.this(),
                TransItemSourceKind::VirtualMethod(kind, method_idx),
            );
            let method_params = if kind.has_self_borrow() {
                Self::self_borrow_params()
            } else {
                GenericParams::empty()
            };
            let generics = self
                .outermost_binder()
                .params
                .identity_args_at_depth(DeBruijnId::one())
                .concat(&method_params.identity_args());
            let method_binder = Binder::new(
                BinderKind::TraitMethod(trait_id, method_id),
                method_params,
                FunDeclRef {
                    id: fun_id,
                    generics: Box::new(generics),
                },
            );
            timpl.methods.set_slot_extend(method_id, method_binder);
        }

        // The other methods reuse the default method from the trait declaration, like in
        // `translate_trait_impl`.
        let self_predicate = TraitRef::new(
            TraitRefKind::TraitImpl(TraitImplRef {
                id: impl_id,
                generics: Box::new(self.the_only_binder().params.identity_args()),
            }),
            timpl.impl_trait.clone(),
        );
        if let Ok(ItemRef::TraitDecl(tdecl)) = self.get_or_translate(trait_id.into()) {
            let default_methods = tdecl
                .methods
                .iter_indexed()
                .filter(|(id, _)| timpl.methods.get(*id).is_none())
                .map(|(id, bound_method)| {
                    let bound_fn_ref = bound_method
                        .clone()
                        .substitute_with_tref(&self_predicate)
                        .map(|method| method.default.expect("missing default method"));
                    (id, bound_fn_ref)
                })
                .collect::<Vec<_>>();
            for (id, bound_fn_ref) in default_methods {
                self.register_method_impl(trait_id, id, bound_fn_ref.skip_binder.id);
                timpl.methods.set_slot_extend(id, bound_fn_ref);
            }
        }

        Ok(timpl)
    }

    /// Translate a method we generate for a virtual impl.
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_virtual_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
        kind: VirtualImplKind,
        method_idx: usize,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let vimpl = def.virtual_impl(self.hax_state(), kind.virtual_trait());
        let trait_pred = &vimpl.trait_pred;
        let implemented_trait = self.translate_trait_predicate(span, trait_pred)?;
        let item_id = self.virtual_method_id(kind, vimpl, implemented_trait.id, method_idx)?;
        let self_ty = implemented_trait
            .self_ty(&self.t_ctx.translated)
            .unwrap()
            .clone();
        let signature = self.virtual_method_sig(kind, span, vimpl, method_idx, self_ty)?;

        let src = {
            let mut impl_generics = self.the_only_binder().params.identity_args();
            if kind.has_self_borrow() {
                impl_generics.regions.pop();
            }
            let impl_id = self.register_item(
                span,
                def.this(),
                TransItemSourceKind::TraitImpl(TransImplSource::Virtual(kind)),
            );
            FunSource::TraitImpl {
                impl_ref: TraitImplRef {
                    id: impl_id,
                    generics: Box::new(impl_generics),
                },
                trait_ref: implemented_trait,
                item_id,
                reuses_default: false,
            }
        };

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            self.virtual_method_body(kind, span, def, vimpl, method_idx, &signature)?
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            signature: Box::new(signature),
            src,
            body,
        })
    }
}
