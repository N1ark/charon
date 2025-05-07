//! In MIR, closures are special cased, and have their own type; calling a closure then uses
//! builtins, requiring consumers to special case them.
//! Here we convert closures to a struct containing the closure's state (upvars), along with
//! matching trait impls and fun decls (e.g. a Fn closure will have a trait impl for Fn, FnMut
//! and FnOnce, along with 3 matching functions for call, call_mut and call_once).
//!
//! For example, given the following Rust code:
//! ```rust
//! pub fn test_closure_capture(x: u32, y: u32) -> u32 {
//!   let f = &|z| x + y + z;
//!   (f)(0)
//! }
//! ```
//!
//! We generate the equivalent desugared code:
//! ```rust
//! struct {test_closure_capture::closure#0} (
//!     u32,
//!     u32,
//! )
//!
//! impl Fn<(u32,)> for {test_closure_capture::closure#0} {
//!     type Output = u32;
//!     fn call(&self, arg: (u32,)) -> u32 {
//!         self.0 + self.1 + arg.0
//!     }
//! }
//!
//! impl FnMut<(u32,)> for {test_closure_capture::closure#0} { ... }
//! impl FnOnce<(u32,)> for {test_closure_capture::closure#0} { ... }
//!
//! pub fn test_closure_capture(x: u32, y: u32) -> u32 {
//!     let state = {test_closure_capture::closure#0} ( x, y );
//!     state.call((0,))
//! }
//! ```

use crate::translate::translate_bodies::BodyTransCtx;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::common::*;
use charon_lib::formatter::{Formatter, IntoFormatter};
use charon_lib::ids::Vector;
use hax_frontend_exporter as hax;
use itertools::Itertools;

impl ItemTransCtx<'_, '_> {
    pub fn translate_closure_ty(
        &mut self,
        _trans_id: TypeDeclId,
        span: Span,
        args: &hax::ClosureArgs,
    ) -> Result<TypeDeclKind, Error> {
        // FIXME: @N1ark this is wrong
        let fields: Vector<FieldId, Field> = args
            .upvar_tys
            .iter()
            .map(|ty| {
                let ty = self.translate_ty(span, ty)?;
                Ok(Field {
                    span,
                    attr_info: AttrInfo {
                        attributes: vec![],
                        inline: None,
                        rename: None,
                        public: true,
                    },
                    name: None,
                    ty: ty.clone(),
                })
            })
            .try_collect()?;

        let signature = self.translate_region_binder(span, &args.untupled_sig, |ctx, sig| {
            let inputs = sig
                .inputs
                .iter()
                .map(|x| ctx.translate_ty(span, x))
                .try_collect()?;
            let output = ctx.translate_ty(span, &sig.output)?;
            Ok((inputs, output))
        })?;
        let upvar_tys = args
            .upvar_tys
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        let kind = match args.kind {
            hax::ClosureKind::Fn => ClosureKind::Fn,
            hax::ClosureKind::FnMut => ClosureKind::FnMut,
            hax::ClosureKind::FnOnce => ClosureKind::FnOnce,
        };

        Ok(TypeDeclKind::Struct(
            fields,
            Some(ClosureInfo {
                kind,
                signature,
                upvar_tys,
            }),
        ))
    }

    fn translate_closure_signature(
        &mut self,
        def: &hax::FullDef,
        item_meta: &ItemMeta,
        args: &hax::ClosureArgs,
    ) -> Result<FunSig, Error> {
        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        let signature = &args.tupled_sig;

        // Translate the signature
        trace!(
            "signature of closure {:?}:\n{:?}",
            def.def_id,
            signature.value
        );
        let mut inputs: Vec<Ty> = signature
            .value
            .inputs
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        let output = self.translate_ty(span, &signature.value.output)?;

        let fmt_ctx = self.into_fmt();
        trace!(
            "# Input variables types:\n{}",
            pretty_display_list(|x| fmt_ctx.format_object(x), &inputs)
        );
        trace!(
            "# Output variable type:\n{}",
            fmt_ctx.format_object(&output)
        );

        let is_unsafe = match signature.value.safety {
            hax::Safety::Unsafe => true,
            hax::Safety::Safe => false,
        };

        assert_eq!(inputs.len(), 1);
        let tuple_arg = inputs.pop().unwrap();

        let state_ty = {
            let state_ty_id = self.register_type_decl_id(span, &def.def_id);
            // FIXME: @N1ark wrong generic args
            let state_ty = TyKind::Adt(
                TypeId::Adt(state_ty_id),
                GenericArgs::empty(GenericsSource::Builtin),
            )
            .into_ty();
            // Depending on the kind of the closure, add a reference
            match args.kind {
                hax::ClosureKind::FnOnce => state_ty,
                hax::ClosureKind::Fn | hax::ClosureKind::FnMut => {
                    let rid = self
                        .innermost_generics_mut()
                        .regions
                        .push_with(|index| RegionVar { index, name: None });
                    let r = Region::Var(DeBruijnVar::new_at_zero(rid));
                    let mutability = if args.kind == hax::ClosureKind::Fn {
                        RefKind::Shared
                    } else {
                        RefKind::Mut
                    };
                    TyKind::Ref(r, state_ty, mutability).into_ty()
                }
            }
        };
        inputs.push(state_ty);

        // Unpack the tupled arguments to match the body locals.
        let TyKind::Adt(TypeId::Tuple, tuple_args) = tuple_arg.kind() else {
            raise_error!(self, span, "Closure argument is not a tuple")
        };
        inputs.extend(tuple_args.types.iter().cloned());

        Ok(FunSig {
            generics: self.the_only_binder().params.clone(),
            is_unsafe,
            is_closure: true,
            inputs,
            output,
        })
    }

    /// Translate the function for the implementation of a closure
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_closure_fun(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
        target_kind: &hax::ClosureKind,
    ) -> Result<FunDecl, Error> {
        let hax::FullDefKind::Closure { args, .. } = &def.kind else {
            unreachable!()
        };

        trace!("About to translate closure:\n{:?}", def.def_id);
        let span = item_meta.span;

        // Translate the function signature
        trace!("Translating closure signature");
        let signature = self.translate_closure_signature(def, &item_meta, args)?;

        let kind = self.get_item_kind(span, def)?;

        let body_id = if item_meta.opacity.with_private_contents().is_opaque() {
            Err(Opaque)
        } else {
            use hax::ClosureKind::*;
            match (target_kind, &args.kind) {
                (Fn, Fn) | (FnMut, FnMut) | (FnOnce, FnOnce) => {
                    // Translate the function's body normally
                    let mut bt_ctx = BodyTransCtx::new(&mut self);
                    match bt_ctx.translate_body(item_meta.span, def) {
                        Ok(Ok(body)) => Ok(body),
                        Ok(Err(Opaque)) => Err(Opaque),
                        Err(_) => Err(Opaque),
                    }
                    // FIXME: @N1ark here we need to unstructure the arguments (provided in a
                    // N-tuple) into a list of N locals at the very start
                }
                (_, _) => {
                    todo!()
                }
            }
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            kind,
            is_global_initializer: None,
            body: body_id,
        })
    }

    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_closure_trait_impl(
        mut self,
        def_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
        target_kind: &hax::ClosureKind,
    ) -> Result<TraitImpl, Error> {
        trace!("About to translate closure trait impl:\n{:?}", def.def_id);
        trace!("Trait impl id:\n{:?}", def_id);

        let span = item_meta.span;
        self.translate_def_generics(span, def)?;

        let hax::FullDefKind::Closure { args, .. } = &def.kind else {
            unreachable!()
        };

        let fn_trait = match target_kind {
            hax::ClosureKind::FnOnce => self.get_lang_item(rustc_hir::LangItem::FnOnce),
            hax::ClosureKind::FnMut => self.get_lang_item(rustc_hir::LangItem::FnMut),
            hax::ClosureKind::Fn => self.get_lang_item(rustc_hir::LangItem::Fn),
        };
        let fn_trait = self.register_trait_decl_id(span, &fn_trait);

        let call_fn = self.register_closure_fun_decl_id(span, &def.def_id, &args.kind);
        let call_fn_name = match target_kind {
            hax::ClosureKind::FnOnce => "call_once".to_string(),
            hax::ClosureKind::FnMut => "call_mut".to_string(),
            hax::ClosureKind::Fn => "call".to_string(),
        };
        let call_fn_name = TraitItemName(call_fn_name);
        let mut call_fn_params = GenericParams::empty();
        match target_kind {
            hax::ClosureKind::FnOnce => {}
            hax::ClosureKind::FnMut | hax::ClosureKind::Fn => {
                call_fn_params
                    .regions
                    .push_with(|index| RegionVar { index, name: None });
            }
        };
        let fn_ref_args = match target_kind {
            hax::ClosureKind::FnOnce => {
                GenericArgs::empty(GenericsSource::Method(fn_trait, call_fn_name.clone()))
            }
            hax::ClosureKind::FnMut | hax::ClosureKind::Fn => GenericArgs {
                regions: vec![Region::Erased].into(),
                types: Vector::new(),
                const_generics: Vector::new(),
                trait_refs: Vector::new(),
                target: GenericsSource::item(call_fn),
            },
        };
        let call_fn_binder = Binder::new(
            BinderKind::TraitMethod(fn_trait, call_fn_name.clone()), //fix
            call_fn_params,
            FunDeclRef {
                id: call_fn,
                // TODO: @N1ark this is wrong -- we need to concat the args of the impl and of the method
                generics: fn_ref_args,
            },
        );

        let parent_args = self.translate_generic_args(
            span,
            &args.parent_args,
            &args.parent_trait_refs,
            None,
            // We don't know the item these generics apply to.
            GenericsSource::Builtin,
        )?;

        let sig_binder = self.translate_region_binder(span, &args.tupled_sig, |ctx, fnsig| {
            let inputs: Vec<Ty> = fnsig
                .inputs
                .iter()
                .map(|ty| ctx.translate_ty(span, ty))
                .try_collect()?;
            let inputs = Ty::mk_tuple(inputs);
            let output = ctx.translate_ty(span, &fnsig.output)?;
            Ok((inputs, output))
        })?;
        let (inputs, output) = sig_binder.erase();
        let types = vec![(TraitItemName("Output".into()), output.clone())];

        let closure_state_id = self.register_type_decl_id(span, def.def_id());
        let closure_state = TyKind::Adt(
            TypeId::Adt(closure_state_id),
            GenericArgs::empty(GenericsSource::Item(AnyTransId::Type(closure_state_id))),
        )
        .into_ty();

        let sized_trait = self.get_lang_item(rustc_hir::LangItem::Sized);
        let sized_trait = self.register_trait_decl_id(span, &sized_trait);

        let tuple_trait = self.get_lang_item(rustc_hir::LangItem::Tuple);
        let tuple_trait = self.register_trait_decl_id(span, &tuple_trait);

        let mk_tref = |trait_id, ty| {
            let generics = GenericArgs {
                regions: Vector::new(),
                const_generics: Vector::new(),
                trait_refs: Vector::new(),
                types: vec![ty].into(),
                target: GenericsSource::Item(AnyTransId::TraitDecl(trait_id)),
            };
            let tdeclref = TraitDeclRef {
                trait_id,
                generics: generics.clone(),
            };
            TraitRef {
                kind: TraitRefKind::BuiltinOrAuto {
                    trait_decl_ref: RegionBinder::empty(tdeclref.clone()),
                    parent_trait_refs: Vector::new(),
                    types: vec![],
                },
                trait_decl_ref: RegionBinder::empty(tdeclref),
            }
        };

        let fn_trait_arguments = GenericArgs {
            regions: Vector::new(),
            types: vec![closure_state.clone(), inputs.clone()].into(),
            const_generics: Vector::new(),
            trait_refs: Vector::new(),
            target: GenericsSource::item(fn_trait),
        };

        let (parent_trait_refs, types) = match target_kind {
            hax::ClosureKind::FnOnce => {
                let trait_refs = vec![
                    mk_tref(sized_trait, inputs.clone()),
                    mk_tref(tuple_trait, inputs),
                    mk_tref(sized_trait, output),
                ];
                (trait_refs.into(), types)
            }
            hax::ClosureKind::FnMut | hax::ClosureKind::Fn => {
                let parent_kind = match target_kind {
                    hax::ClosureKind::FnOnce => unreachable!(),
                    hax::ClosureKind::FnMut => hax::ClosureKind::FnOnce,
                    hax::ClosureKind::Fn => hax::ClosureKind::FnMut,
                };
                let parent_impl =
                    self.register_closure_trait_impl_id(span, def.def_id(), &parent_kind);
                let parent_decl = match parent_kind {
                    hax::ClosureKind::FnOnce => self.get_lang_item(rustc_hir::LangItem::FnOnce),
                    hax::ClosureKind::FnMut => self.get_lang_item(rustc_hir::LangItem::FnMut),
                    _ => unreachable!(),
                };
                let parent_decl = self.register_trait_decl_id(span, &parent_decl);
                let parent_trait_ref = TraitRef {
                    kind: TraitRefKind::TraitImpl(
                        parent_impl,
                        parent_args
                            .clone()
                            .with_target(GenericsSource::item(parent_impl)),
                    ),
                    trait_decl_ref: RegionBinder::empty(TraitDeclRef {
                        trait_id: parent_decl,
                        generics: fn_trait_arguments
                            .clone()
                            .with_target(GenericsSource::item(parent_decl)),
                    }),
                };
                let trait_refs = vec![
                    parent_trait_ref,
                    mk_tref(sized_trait, inputs.clone()),
                    mk_tref(tuple_trait, inputs),
                ];
                (trait_refs.into(), vec![])
            }
        };

        Ok(TraitImpl {
            def_id,
            item_meta,
            impl_trait: TraitDeclRef {
                trait_id: fn_trait,
                generics: fn_trait_arguments,
            },
            generics: self.into_generics(),
            parent_trait_refs,
            type_clauses: vec![],
            consts: vec![],
            types,
            methods: vec![(call_fn_name, call_fn_binder)],
        })
    }
}
