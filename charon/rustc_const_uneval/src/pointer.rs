//! Reading pointers out of const-eval memory.
use crate::*;
use interpret::GlobalAlloc;
use rustc_abi::{FieldIdx, FieldsShape, Size};
use rustc_const_eval::const_eval::CompileTimeInterpCx;
use rustc_const_eval::interpret::{InterpResult, MPlaceTy, OpTy, Projectable, interp_ok};

impl<'tcx> ConstReader<'tcx> {
    /// Read a reference or raw pointer.
    pub(crate) fn read_pointer(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        op: &OpTy<'tcx>,
    ) -> InterpResult<'tcx, Const<'tcx>> {
        let tcx = self.tcx;
        let ptr_ty = op.layout.ty;
        let place = ecx.deref_pointer(op)?;
        // A pointer to a function, cast to another pointer type: we read it as a cast of a
        // function pointer.
        if let (Some(prov), offset) = place.ptr().into_raw_parts()
            && let AllocTarget::Fn(target) = self.alloc_target(prov.alloc_id())
        {
            // We can only express a thin raw pointer to the start of the function.
            if offset != Size::ZERO || !ptr_ty.is_raw_ptr() || place.meta().has_meta() {
                let kind = ConstKind::Unsupported("unsupported pointer to a function");
                return interp_ok(Const { ty: ptr_ty, kind });
            }
            let sig = match target {
                FnTarget::Instance(instance) => instance.ty(tcx, self.typing_env).fn_sig(tcx),
                FnTarget::ClosureAsFn(_, args) => {
                    tcx.signature_unclosure(args.as_closure().sig(), rustc_hir::Safety::Safe)
                }
            };
            let fn_ptr = Const {
                ty: Ty::new_fn_ptr(tcx, sig),
                kind: ConstKind::FnPtr(target),
            };
            let kind = ConstKind::PtrCast {
                ptr: Box::new(fn_ptr),
                unsize: None,
            };
            return interp_ok(Const { ty: ptr_ty, kind });
        }
        let ty = place.layout.ty;
        let unsize = if place.meta().has_meta() {
            let tail = tcx.struct_tail_for_codegen(ty, self.typing_env);
            let from = self.sized_tail(ecx, &place, tail)?;
            Some(Unsize { from, to: tail })
        } else {
            None
        };
        let view_ty = self.sized_view(ty, unsize);
        let kind = match place.ptr().into_raw_parts() {
            // Rustc rejects dangling pointers in final values, so a pointer with provenance
            // points to a live allocation.
            (Some(_), _) => self.read_pointer_into_alloc(ecx, place, ptr_ty, unsize, view_ty)?,
            // A pointer without provenance, e.g. null or the pointer of an empty slice.
            (None, addr) => {
                let addr = ConstKind::PtrNoProvenance(addr.bytes().into());
                match (unsize, view_ty) {
                    // An address is a raw pointer, which we cast to a reference (e.g. a dangling
                    // reference to a ZST).
                    (None, _) if ptr_ty.is_ref() => ConstKind::PtrCast {
                        ptr: Box::new(Const {
                            ty: Ty::new_ptr(tcx, ty, pointer_mutability(ptr_ty)),
                            kind: addr,
                        }),
                        unsize: None,
                    },
                    (None, _) => addr,
                    // Unsize the thin pointer with the metadata.
                    (Some(unsize), Some(view_ty)) => ConstKind::PtrCast {
                        ptr: Box::new(Const {
                            ty: Ty::new_ptr(tcx, view_ty, pointer_mutability(ptr_ty)),
                            kind: addr,
                        }),
                        unsize: Some(unsize),
                    },
                    // Other unsized pointees have no sized type to unsize from, so we keep the
                    // address and metadata as bytes.
                    (Some(_), None) => ConstKind::Memory(self.read_raw_bytes(ecx, op)?),
                }
            }
        };
        interp_ok(Const { ty: ptr_ty, kind })
    }

    /// Read a pointer to `place`, which has provenance. Pointers to globals that we name are kept
    /// as pointers to these globals, and we fall back to reading the pointee for other cases.
    fn read_pointer_into_alloc(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        place: MPlaceTy<'tcx>,
        ptr_ty: Ty<'tcx>,
        unsize: Option<Unsize<'tcx>>,
        view_ty: Option<Ty<'tcx>>,
    ) -> InterpResult<'tcx, ConstKind<'tcx>> {
        let tcx = self.tcx;
        let ty = place.layout.ty;
        let mutability = pointer_mutability(ptr_ty);
        let (alloc_id, offset, _) = ecx.ptr_get_alloc_id(place.ptr(), 0)?;
        let alloc_target = self.alloc_target(alloc_id);
        let size = ecx.size_and_align_of_val(&place)?.map(|(size, _)| size);
        let global_ty = match view_ty {
            Some(view_ty) => Some(view_ty),
            // We keep a string literal as a `str` literal.
            None if ty.is_str()
                && let GlobalAlloc::Memory(alloc) = tcx.global_alloc(alloc_id)
                && offset == Size::ZERO
                && Some(alloc.inner().size()) == size =>
            {
                None
            }
            // We view other unsized values (e.g. a `CStr`, or a `str` that points into other
            // memory) as bytes. An extern type has no known size, so we view it as an empty array.
            None => {
                let size = size.map_or(0, |size| size.bytes());
                Some(Ty::new_array(tcx, tcx.types.u8, size))
            }
        };
        // A pointer outside of its allocation (one-past-the-end is fine) needs a wrapping offset.
        let in_bounds = offset <= ecx.get_alloc_info(alloc_id).size;
        interp_ok(
            if let Some(global_ty) = global_ty
                && let AllocTarget::Global(global) = alloc_target
                // We refer to statics by name, and to other globals if requested. We can't
                // read the pointee of a pointer outside of its allocation, so we always name
                // the allocation then.
                && (matches!(global, GlobalRef::Static(_))
                    || self.config.anon_allocs_as_globals
                    || !in_bounds)
                && let Some((decl_ty, projections, end_ty)) =
                    self.place_in_global(ecx, &place, global, offset, in_bounds, global_ty)
            {
                let target = PtrTarget::Global {
                    global,
                    ty: decl_ty,
                    projections,
                };
                // We can't take a `*mut` to an immutable global, so we take a `*const` and cast it.
                let borrow_mutability = global_mutability(tcx, global).min(mutability);
                if end_ty == tcx.erase_and_anonymize_regions(global_ty)
                    && borrow_mutability == mutability
                {
                    ConstKind::Ptr { target, unsize }
                } else {
                    // Point to the place we reached, then cast the pointer to the right type.
                    let cast = |ptr, unsize| ConstKind::PtrCast {
                        ptr: Box::new(ptr),
                        unsize,
                    };
                    let inner = Const {
                        ty: Ty::new_ptr(tcx, end_ty, borrow_mutability),
                        kind: ConstKind::Ptr {
                            target,
                            unsize: None,
                        },
                    };
                    match unsize {
                        None => cast(inner, None),
                        // Cast to the sized type first, then unsize.
                        Some(unsize) => {
                            let sized = Const {
                                ty: Ty::new_ptr(tcx, global_ty, mutability),
                                kind: cast(inner, None),
                            };
                            cast(sized, Some(unsize))
                        }
                    }
                }
            } else if !in_bounds {
                ConstKind::Unsupported("pointer outside of its allocation")
            } else if let AllocTarget::VTable(..) = alloc_target {
                // A vtable has no global we can point into, and const-eval can't read its contents.
                ConstKind::Unsupported("pointer into a vtable")
            } else {
                // HACK: fallback to reading the value of the pointee, at type `global_ty` for
                // slices, `str` and `dyn`. Other unsized pointees stay unsized, so that they are put
                // in a global instead of a local when the constant is used in a body.
                let place = match global_ty {
                    Some(global_ty)
                        if global_ty != ty
                            && matches!(ty.kind(), ty::Slice(_) | ty::Str | ty::Dynamic(..)) =>
                    {
                        place.offset(Size::ZERO, ecx.layout_of(global_ty)?, ecx)?
                    }
                    _ => place,
                };
                let target = PtrTarget::Inline(Box::new(self.read_op(ecx, place.into())?));
                ConstKind::Ptr { target, unsize }
            },
        )
    }

    /// The sized type at which we view a pointee of type `ty`, whose unsized tail (if any) was
    /// unsized according to `unsize`. A slice or `dyn Trait` value is viewed at the sized type it
    /// was unsized from, and so is a `str` with `unsized_strings` and a generic struct whose tail is
    /// such a type parameter. Other unsized values (e.g. a `CStr`) have no such type.
    fn sized_view(&self, ty: Ty<'tcx>, unsize: Option<Unsize<'tcx>>) -> Option<Ty<'tcx>> {
        let tcx = self.tcx;
        match unsize {
            // Pointers to sized types and to extern types are thin.
            None => ty.is_sized(tcx, self.typing_env).then_some(ty),
            Some(unsize) => self.with_sized_tail(ty, unsize),
        }
    }

    /// `ty` with its unsized tail replaced by the sized type it was unsized from (see
    /// `sized_view`).
    fn with_sized_tail(&self, ty: Ty<'tcx>, unsize: Unsize<'tcx>) -> Option<Ty<'tcx>> {
        let tcx = self.tcx;
        match ty.kind() {
            _ if ty == unsize.to => self.is_viewed_unsized_from(ty).then_some(unsize.from),
            // The tail of a generic struct is unsized because of one of its type parameters: we
            // replace that parameter.
            ty::Adt(adt_def, args) if let Some(index) = self.tail_param(*adt_def) => {
                let tail = self.with_sized_tail(args.type_at(index), unsize)?;
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| if i == index { tail.into() } else { arg });
                Some(Ty::new_adt(tcx, *adt_def, tcx.mk_args_from_iter(args)))
            }
            _ => None,
        }
    }

    /// The index of the type parameter of `adt_def` that its tail is made of, if it is a struct
    /// whose last field is that parameter, or a struct whose tail is that parameter.
    fn tail_param(&self, adt_def: ty::AdtDef<'tcx>) -> Option<usize> {
        if !adt_def.is_struct() {
            return None;
        }
        let field = adt_def.non_enum_variant().fields.iter().last()?;
        let mut ty = self
            .tcx
            .type_of(field.did)
            .instantiate_identity()
            .skip_normalization();
        loop {
            match *ty.kind() {
                ty::Param(param) => return Some(param.index as usize),
                ty::Adt(inner, args) => ty = args.type_at(self.tail_param(inner)?),
                _ => return None,
            }
        }
    }

    /// Whether we view a value of the unsized type `ty` at the sized type it was unsized from: a
    /// slice or `dyn Trait` value is, and so is a `str` with `unsized_strings`. Other unsized
    /// values (e.g. a `CStr`) aren't.
    pub(crate) fn is_viewed_unsized_from(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            ty::Slice(_) | ty::Dynamic(..) => true,
            ty::Str => self.config.unsized_strings,
            _ => false,
        }
    }

    /// Express the place of type `ty` located `offset` bytes into `global` (whose allocation
    /// `place` points into) as projections from the global. `in_bounds` tells whether that place
    /// is inside the global (or one past its end). Returns the type of the global, the projections
    /// and the type of the place they reach, which is `ty` unless the pointer must be cast.
    fn place_in_global(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        place: &MPlaceTy<'tcx>,
        global: GlobalRef,
        offset: Size,
        in_bounds: bool,
        ty: Ty<'tcx>,
    ) -> Option<(Ty<'tcx>, ProjectionPath<'tcx>, Ty<'tcx>)> {
        let tcx = self.tcx;
        let ty = tcx.erase_and_anonymize_regions(ty);
        let size = ecx.layout_of(ty).ok()?.size;
        let decl_ty = tcx.erase_and_anonymize_regions(self.global_ty(global));
        // Allocations without an item are untyped (see `global_ty`), so we only follow the
        // structure of statics. A place outside of the global has no such structure.
        let (path, end_ty) = if in_bounds && let GlobalRef::Static(_) = global {
            let (prov, _) = place.ptr().into_raw_parts();
            let ptr = interpret::Pointer::new(prov, Size::ZERO);
            let base = ecx.ptr_to_mplace(ptr, ecx.layout_of(decl_ty).ok()?);
            structural_path(ecx, base, offset, ty, size)
        } else {
            // The offset of a pointer outside of its allocation may be negative.
            let offset = tcx
                .data_layout
                .pointer_size()
                .sign_extend(offset.bytes().into());
            let proj = offset_projection(offset as i64, ty, size, in_bounds);
            (
                proj.map(|proj| (proj, decl_ty)).into_iter().collect(),
                decl_ty,
            )
        };
        Some((decl_ty, path, end_ty))
    }
}

/// The mutability of the pointer type `ty`.
fn pointer_mutability(ty: Ty<'_>) -> ty::Mutability {
    let (ty::Ref(.., mutability) | ty::RawPtr(_, mutability)) = *ty.kind() else {
        unreachable!("not a pointer type: {ty:?}")
    };
    mutability
}

/// The projection to the place located `offset` bytes after the current place, for a pointee of
/// type `ty` and size `size`, if `offset` isn't zero.
fn offset_projection<'tcx>(
    offset: i64,
    ty: Ty<'tcx>,
    size: Size,
    in_bounds: bool,
) -> Option<Projection<'tcx>> {
    if offset == 0 {
        return None;
    }
    let size = size.bytes() as i64;
    let (count, ty) = if size != 0 && offset % size == 0 {
        (offset / size, Some(ty))
    } else {
        (offset, None)
    };
    Some(Projection::Offset {
        count,
        ty,
        in_bounds,
    })
}

/// Find projections from `place` to the place of type `to_ty` and size `size` located `offset`
/// bytes after it. There may be many ways of reaching the same destination. Returns the
/// projections to use, and the type of the final place, which may not match `to_ty`, in which
/// case a cast is needed.
fn structural_path<'tcx>(
    ecx: &CompileTimeInterpCx<'tcx>,
    mut place: MPlaceTy<'tcx>,
    mut offset: Size,
    to_ty: Ty<'tcx>,
    size: Size,
) -> (ProjectionPath<'tcx>, Ty<'tcx>) {
    let mut path = vec![];
    while !(place.layout.ty == to_ty && offset == Size::ZERO) {
        let Some((proj, sub, sub_offset)) = find_subplace(ecx, &place, offset, to_ty, size)
            .discard_err()
            .flatten()
        else {
            // Give up: we couldn't find a typed path, so we offset from the place we reached.
            let proj = offset_projection(offset.bytes() as i64, to_ty, size, true);
            path.extend(proj.map(|proj| (proj, place.layout.ty)));
            return (path, place.layout.ty);
        };
        path.push((proj, sub.layout.ty));
        place = sub;
        offset = sub_offset;
    }
    (path, to_ty)
}

/// Find the subplace of `place` that contains the place of type `to_ty` and size `size` located
/// `offset` bytes after `place`. Returns the projection to that subplace, the subplace, and the
/// offset of the target within it.
fn find_subplace<'tcx>(
    ecx: &CompileTimeInterpCx<'tcx>,
    place: &MPlaceTy<'tcx>,
    offset: Size,
    to_ty: Ty<'tcx>,
    size: Size,
) -> InterpResult<'tcx, Option<(Projection<'tcx>, MPlaceTy<'tcx>, Size)>> {
    match place.layout.ty.kind() {
        ty::Array(elem, _) => {
            let len = place.len(ecx)?;
            let stride = place.layout.field(ecx, 0).size.bytes();
            let Some(i) = offset.bytes().checked_div(stride) else {
                return interp_ok(None);
            };
            // The target may be a subarray.
            if let ty::Array(target_elem, _) = to_ty.kind()
                && target_elem == elem
                && offset.bytes().is_multiple_of(stride)
                && i + size.bytes() / stride <= len
            {
                let (from, to) = (i, i + size.bytes() / stride);
                let subslice = mir::ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: false,
                };
                let sub = ecx.project(place, subslice)?;
                return interp_ok(Some((Projection::Subslice { from, to }, sub, Size::ZERO)));
            }
            // The element that contains the target, if any.
            if i < len && offset.bytes() + size.bytes() <= (i + 1) * stride {
                let sub_offset = offset - Size::from_bytes(i * stride);
                let sub = ecx.project_index(place, i)?;
                return interp_ok(Some((Projection::Index(i), sub, sub_offset)));
            }
        }
        // Any field of a union contains the target, so we take the one of the right type if any.
        ty::Adt(adt_def, _) if adt_def.is_union() => {
            if offset == Size::ZERO
                && let Some(i) = (0..place.layout.fields.count())
                    .find(|&i| place.layout.field(ecx, i).ty == to_ty)
            {
                let field = FieldIdx::from_usize(i);
                let sub = ecx.project_field(place, field)?;
                return interp_ok(Some((Projection::Field(None, field), sub, offset)));
            }
        }
        ty::Adt(..) | ty::Tuple(..) | ty::Closure(..) => {
            let (place, variant) = match place.layout.ty.kind() {
                ty::Adt(adt_def, _) if adt_def.is_enum() => {
                    let variant = ecx.read_discriminant(place)?;
                    (ecx.project_downcast(place, variant)?, Some(variant))
                }
                _ => (place.clone(), None),
            };
            let FieldsShape::Arbitrary {
                offsets,
                in_memory_order,
            } = &place.layout.fields
            else {
                return interp_ok(None);
            };
            // The field that contains the target, if any; a zero-sized target may be contained in
            // several fields, in which case we take the first one in source order. Structs can
            // have many fields, so we find the candidates by binary search: fields don't overlap,
            // so only the last fields (by increasing offset) that start at or before the target
            // can contain it.
            let candidates = in_memory_order
                .raw
                .partition_point(|&i| offsets[i] <= offset);
            let mut found = None;
            for &i in in_memory_order.raw[..candidates].iter().rev() {
                let field_offset = offsets[i];
                let field_size = place.layout.field(ecx, i.as_usize()).size;
                if offset + size <= field_offset + field_size {
                    found = Some(found.map_or(i, |found: FieldIdx| found.min(i)));
                }
                // The previous fields end at or before the start of this field, so they can only
                // contain the target if it is zero-sized and this field starts at it.
                if field_offset < offset || size != Size::ZERO {
                    break;
                }
            }
            if let Some(field) = found {
                let sub = ecx.project_field(&place, field)?;
                let proj = Projection::Field(variant, field);
                return interp_ok(Some((proj, sub, offset - offsets[field])));
            }
        }
        _ => {}
    }
    interp_ok(None)
}
