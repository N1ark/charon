//! Virtual impls are trait impls that rustc provides without source code, e.g. `impl Destruct for
//! T` for every type. We generate a trait impl with a single method of our own, whose body we
//! get from rustc; the other methods of the trait use their default. The per-kind specifics are in
//! the `match`es on [`VirtualImplKind`] below.
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
        }
    }

    /// Whether the method we generate takes `self` by reference. If so, it takes an extra lifetime
    /// parameter for that borrow.
    pub fn has_self_borrow(self) -> bool {
        !matches!(self, VirtualImplKind::Callable(ClosureKind::FnOnce))
    }

    /// The name of the method we generate.
    pub fn method_path_elem(self) -> PathElem {
        match self {
            VirtualImplKind::Destruct => {
                PathElem::Builtin(BuiltinPathElem::DropGlue, Disambiguator::ZERO)
            }
            VirtualImplKind::Callable(kind) => {
                PathElem::Ident(kind.method_name().to_string(), Disambiguator::ZERO)
            }
            VirtualImplKind::Clone => PathElem::Ident("clone".to_string(), Disambiguator::ZERO),
        }
    }
}

impl<'tcx> ItemTransCtx<'tcx, '_> {
    /// The id of the method we generate, within the implemented trait.
    fn virtual_method_id(
        &mut self,
        kind: VirtualImplKind,
        vimpl: &hax::VirtualTraitImpl<'tcx>,
        trait_id: TraitDeclId,
    ) -> Result<TraitMethodId, Error> {
        match kind {
            VirtualImplKind::Destruct => {
                self.translate_drop_glue_method_id(&vimpl.trait_pred.trait_ref.def_id, trait_id)
            }
            // For `Clone`, `methods` are in definition order and `clone` comes first.
            VirtualImplKind::Callable(_) | VirtualImplKind::Clone => {
                self.translate_trait_method_id(trait_id, &vimpl.methods[0].def_id)
            }
        }
    }

    fn virtual_method_sig(
        &mut self,
        kind: VirtualImplKind,
        span: Span,
        vimpl: &hax::VirtualTraitImpl<'tcx>,
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
            VirtualImplKind::Callable(_) | VirtualImplKind::Clone => self
                .translate_poly_fun_sig(span, &vimpl.methods[0].sig)?
                .apply(self_borrow_region.into_iter().collect()),
        })
    }

    fn virtual_method_body(
        &mut self,
        kind: VirtualImplKind,
        span: Span,
        def: &hax::FullDef<'tcx>,
        vimpl: &hax::VirtualTraitImpl<'tcx>,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        match kind {
            VirtualImplKind::Destruct => self.translate_drop_glue_method_body(span, def),
            VirtualImplKind::Callable(target_kind) => {
                self.translate_callable_method_body(span, def, target_kind, signature)
            }
            VirtualImplKind::Clone => {
                let body = vimpl
                    .method_shim(self.hax_state(), &vimpl.methods[0].def_id)
                    .expect("built-in `Clone` impls are implemented by a shim");
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

        // Add the method we generate. It takes the impl generics, plus a lifetime for the borrow
        // of `self` if it takes `self` by reference.
        let trait_id = timpl.impl_trait.id;
        let method_id = self.virtual_method_id(kind, vimpl, trait_id)?;
        let method_binder = {
            let fun_id =
                self.register_item(span, def.this(), TransItemSourceKind::VirtualMethod(kind));
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
            Binder::new(
                BinderKind::TraitMethod(trait_id, method_id),
                method_params,
                FunDeclRef {
                    id: fun_id,
                    generics: Box::new(generics),
                },
            )
        };
        timpl.methods.set_slot_extend(method_id, method_binder);

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
                .filter(|(id, _)| *id != method_id)
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

    /// Translate the method we generate for a virtual impl.
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_virtual_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
        kind: VirtualImplKind,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let vimpl = def.virtual_impl(self.hax_state(), kind.virtual_trait());
        let trait_pred = &vimpl.trait_pred;
        let implemented_trait = self.translate_trait_predicate(span, trait_pred)?;
        let item_id = self.virtual_method_id(kind, vimpl, implemented_trait.id)?;
        let self_ty = implemented_trait
            .self_ty(&self.t_ctx.translated)
            .unwrap()
            .clone();
        let signature = self.virtual_method_sig(kind, span, vimpl, self_ty)?;

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
            self.virtual_method_body(kind, span, def, vimpl, &signature)?
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
