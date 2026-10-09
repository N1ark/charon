//! Functions to translate constants to LLBC.
use crate::hax;
use rustc_middle::ty;

use super::translate_ctx::*;
use charon_lib::ast::*;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    fn translate_constant_literal_to_constant_expr_kind(
        &mut self,
        span: Span,
        v: &hax::ConstantLiteral,
    ) -> Result<ConstantExprKind, Error> {
        Ok(match v {
            hax::ConstantLiteral::ByteStr(bs) => ConstantExprKind::ByteStr(bs.clone()),
            // A `str` value not behind a reference, e.g. the tail of a `str`-tailed DST
            hax::ConstantLiteral::Str(str) => {
                let ty_is_sized = self.translate_sized_proof(span, self.tcx.types.u8)?;
                let bytes = str
                    .bytes()
                    .map(|b| IntegerValue::Unsigned(UIntTy::U8, b.into()).to_constant())
                    .collect();
                let slice_ty = Ty::mk_slice(Ty::mk_u8(), ty_is_sized);
                let bytes = ConstantExpr::new(ConstantExprKind::Array(bytes), slice_ty);
                // we encode `str` as `struct { [u8] }`
                ConstantExprKind::Adt(None, [bytes].into())
            }
            hax::ConstantLiteral::Char(c) => ConstantExprKind::Char(*c),
            hax::ConstantLiteral::Bool(b) => ConstantExprKind::Bool(*b),
            hax::ConstantLiteral::Int(i) => {
                use crate::hax::ConstantInt;
                let scalar = match i {
                    ConstantInt::Int(v, int_type) => {
                        let ty = Self::translate_hax_int_ty(int_type);
                        IntegerValue::Signed(ty, *v)
                    }
                    ConstantInt::Uint(v, uint_type) => {
                        let ty = Self::translate_hax_uint_ty(uint_type);
                        IntegerValue::Unsigned(ty, *v)
                    }
                };
                ConstantExprKind::Integer(scalar)
            }
            hax::ConstantLiteral::Float(value, float_type) => {
                let value = value.clone();
                let ty = match float_type {
                    hax::FloatTy::F16 => FloatTy::F16,
                    hax::FloatTy::F32 => FloatTy::F32,
                    hax::FloatTy::F64 => FloatTy::F64,
                    hax::FloatTy::F128 => FloatTy::F128,
                };
                ConstantExprKind::Float(FloatValue { value, ty })
            }
            hax::ConstantLiteral::PtrNoProvenance(v) => {
                return Ok(ConstantExprKind::PtrNoProvenance(*v));
            }
        })
    }

    fn translate_provenance(
        &mut self,
        span: Span,
        prov: &hax::ConstantByteProvenance,
    ) -> Result<Provenance, Error> {
        Ok(match prov {
            hax::ConstantByteProvenance::Global(item) => {
                Provenance::Global(self.translate_global_decl_ref(span, item)?)
            }
            hax::ConstantByteProvenance::Function(target) => {
                Provenance::Function(self.translate_fn_ptr_target(span, target)?)
            }
            hax::ConstantByteProvenance::VTable(proof) => {
                match self.translate_vtable_instance_const(span, proof)?.kind() {
                    ConstantExprKind::Ref(vtable, None)
                        if let GlobalPlaceKind::Global(gref) = &vtable.kind =>
                    {
                        Provenance::Global(gref.clone())
                    }
                    _ => raise_error!(self, span, "vtable without a global"),
                }
            }
            hax::ConstantByteProvenance::TypeId(ty) => {
                Provenance::TypeId(self.translate_ty(span, ty)?)
            }
        })
    }

    /// The function pointed to by a function pointer.
    fn translate_fn_ptr_target(
        &mut self,
        span: Span,
        target: &hax::FnPtrTarget,
    ) -> Result<FnPtr, Error> {
        Ok(match target {
            hax::FnPtrTarget::Fn(item) => {
                self.translate_fn_ptr(span, item, TransItemSourceKind::Fun)?
            }
            hax::FnPtrTarget::ClosureAsFn(closure) => {
                let fn_ref = self.translate_stateless_closure_as_fn_ref(span, closure)?;
                self.erase_region_binder(fn_ref).into()
            }
        })
    }

    /// Remark: [hax::ConstantExpr] contains span information, but it is often
    /// the default span (i.e., it is useless), hence the additional span argument.
    /// TODO: the user_ty might be None because hax doesn't extract it (because
    /// we are translating a [ConstantExpr] instead of a Constant. We need to
    /// update hax.
    pub(crate) fn translate_constant_expr(
        &mut self,
        span: Span,
        v: &hax::ConstantExpr,
    ) -> Result<ConstantExpr, Error> {
        let ty = self.translate_ty(span, &v.ty)?;
        let kind = match v.contents.as_ref() {
            hax::ConstantExprKind::Literal(lit) => {
                self.translate_constant_literal_to_constant_expr_kind(span, lit)?
            }
            hax::ConstantExprKind::Adt { kind, fields } => {
                let fields: IndexVec<FieldId, ConstantExpr> = fields
                    .iter()
                    .map(|f| self.translate_constant_expr(span, &f.value))
                    .try_collect()?;
                use crate::hax::VariantKind;
                let vid = if let VariantKind::Enum { index, .. } = *kind {
                    Some(self.translate_variant_id(index))
                } else {
                    None
                };
                ConstantExprKind::Adt(vid, fields)
            }
            hax::ConstantExprKind::Array { fields } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    .map(|x| self.translate_constant_expr(span, x))
                    .try_collect()?;

                ConstantExprKind::Array(fields)
            }
            hax::ConstantExprKind::Tuple { fields } => {
                let fields: IndexVec<FieldId, ConstantExpr> = fields
                    .iter()
                    // TODO: the user_ty is not always None
                    .map(|f| self.translate_constant_expr(span, f))
                    .try_collect()?;
                ConstantExprKind::Adt(None, fields)
            }
            hax::ConstantExprKind::NamedGlobal(item) => match &item.in_trait {
                Some(trait_proof) => {
                    let trait_ref = self.translate_trait_proof(span, trait_proof)?;
                    // Trait consts can't have their own generics.
                    assert!(item.generic_args.is_empty());
                    let const_id =
                        self.translate_assoc_const_id(trait_ref.trait_id(), &item.def_id)?;
                    ConstantExprKind::TraitConst(trait_ref, const_id)
                }
                None => {
                    let global_ref = self.translate_global_decl_ref(span, item)?;
                    ConstantExprKind::Global(global_ref)
                }
            },
            hax::ConstantExprKind::Ptr { arg, .. }
                if ty.is_ref()
                    && let hax::ConstantExprKind::Literal(hax::ConstantLiteral::Str(s)) =
                        arg.contents.as_ref() =>
            {
                ConstantExprKind::Str(s.clone())
            }
            hax::ConstantExprKind::Ptr {
                arg,
                projections,
                metadata,
            } => {
                let val = self.translate_constant_expr(span, arg)?;
                let mut place = match val.kind() {
                    ConstantExprKind::Global(global_ref) => {
                        GlobalPlace::new_global(global_ref.clone(), val.ty().clone())
                    }
                    _ => GlobalPlace::new_value(val),
                };
                for (proj, proj_ty) in projections {
                    let proj = match *proj {
                        hax::ConstantProjectionElem::Field(variant, field) => {
                            ConstProjectionElem::Field(
                                variant.map(|v| self.translate_variant_id(v)),
                                self.translate_field_id(field),
                            )
                        }
                        hax::ConstantProjectionElem::Index(i) => {
                            ConstProjectionElem::Index(IntegerValue::mk_usize(i as u128))
                        }
                        hax::ConstantProjectionElem::Subslice { from, to } => {
                            ConstProjectionElem::Subslice {
                                from: IntegerValue::mk_usize(from as u128),
                                to: IntegerValue::mk_usize(to as u128),
                            }
                        }
                        hax::ConstantProjectionElem::Offset {
                            count,
                            ref ty,
                            in_bounds,
                        } => ConstProjectionElem::Offset {
                            count: IntegerValue::Signed(IntTy::Isize, count as i128),
                            ty: ty
                                .as_ref()
                                .map(|ty| self.translate_ty(span, ty))
                                .transpose()?,
                            in_bounds,
                        },
                    };
                    place = place.project(proj, self.translate_ty(span, proj_ty)?);
                }
                let metadata = metadata
                    .as_ref()
                    .map(|metadata| self.translate_unsizing_metadata(span, metadata))
                    .transpose()?;
                match ty.kind() {
                    TyKind::RawPtr(_, rk) => ConstantExprKind::Ptr(*rk, place, metadata),
                    _ => ConstantExprKind::Ref(place, metadata),
                }
            }
            hax::ConstantExprKind::PtrCast(ptr, metadata) => {
                let ptr = self.translate_constant_expr(span, ptr)?;
                let src = ptr.ty().clone();
                let kind = if let Some(metadata) = metadata {
                    let metadata = self.translate_unsizing_metadata(span, metadata)?;
                    CastKind::Unsize(src, ty.clone(), metadata)
                } else if src.is_fn_ptr() {
                    CastKind::FnPtr(src, ty.clone())
                } else {
                    CastKind::RawPtr(src, ty.clone())
                };
                ConstantExprKind::Cast(ptr, kind)
            }
            hax::ConstantExprKind::ConstRef { id } => {
                match self.lookup_const_generic_var(span, id) {
                    Ok(var) => ConstantExprKind::Var(var),
                    Err(err) => ConstantExprKind::Opaque(err.msg),
                }
            }
            hax::ConstantExprKind::FnDef(item) => {
                let fn_ptr = self.translate_fn_ptr(span, item, TransItemSourceKind::Fun)?;
                ConstantExprKind::FnDef(fn_ptr)
            }
            hax::ConstantExprKind::FnPtr(target) => {
                ConstantExprKind::FnPtr(self.translate_fn_ptr_target(span, target)?)
            }
            hax::ConstantExprKind::TypeId(ty) => {
                ConstantExprKind::TypeId(self.translate_ty(span, ty)?)
            }
            hax::ConstantExprKind::Memory(memory) => {
                let mut bytes: Vec<Byte> = memory
                    .bytes
                    .iter()
                    .map(|b| b.map_or(Byte::Uninit, Byte::Value))
                    .collect();
                for ptr in &memory.ptrs {
                    let provenance = self.translate_provenance(span, &ptr.provenance)?;
                    // The pointer may straddle the bounds of the bytes; we keep the bytes inside.
                    for index in 0..ptr.size {
                        if let Ok(pos) = usize::try_from(ptr.start + index as i64)
                            && let Some(byte) = bytes.get_mut(pos)
                        {
                            *byte = Byte::Provenance {
                                provenance: provenance.clone(),
                                offset: ptr.offset,
                                index,
                            };
                        }
                    }
                }
                ConstantExprKind::RawMemory(bytes)
            }
            hax::ConstantExprKind::Todo(msg) => {
                register_error!(self, span, "Unsupported constant: {:?}", msg);
                ConstantExprKind::Opaque(msg.into())
            }
        };

        Ok(ConstantExpr::new(kind, ty))
    }

    pub(crate) fn translate_ty_constant_expr(
        &mut self,
        span: Span,
        c: &ty::Const<'tcx>,
    ) -> Result<ConstantExpr, Error> {
        let c = self.catch_sinto(span, c)?;
        self.translate_constant_expr(span, &c)
    }
}
