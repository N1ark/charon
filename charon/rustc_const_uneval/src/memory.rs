//! Reading values out of const-eval memory.
use crate::*;
use interpret::GlobalAlloc;
use rustc_abi::{FieldIdx, Size};
use rustc_attr_ir::LangItem;
use rustc_const_eval::const_eval::CompileTimeInterpCx;
use rustc_const_eval::interpret::{
    FnVal, ImmTy, Immediate, InterpResult, MPlaceTy, OpTy, Projectable, interp_ok,
};
use rustc_hir::def::DefKind;

impl<'tcx> ConstReader<'tcx> {
    /// Classify the given allocation.
    pub(crate) fn alloc_target(&self, alloc_id: interpret::AllocId) -> AllocTarget<'tcx> {
        let tcx = self.tcx;
        match tcx.global_alloc(alloc_id) {
            GlobalAlloc::Function { instance } => AllocTarget::Fn(FnTarget::new(instance, None)),
            GlobalAlloc::Static(def_id)
                if let DefKind::Static { nested: false, .. } = tcx.def_kind(def_id) =>
            {
                AllocTarget::Global(GlobalRef::Static(def_id))
            }
            GlobalAlloc::Static(_) | GlobalAlloc::Memory(_) => {
                AllocTarget::Global(GlobalRef::Alloc(alloc_id))
            }
            GlobalAlloc::VTable(ty, preds) => AllocTarget::VTable(ty, preds),
            GlobalAlloc::TypeId { ty } => AllocTarget::TypeId(ty),
        }
    }

    /// Whether we refer to `global` by name in pointers to it, rather than inlining its contents.
    pub fn is_named_global(&self, global: GlobalRef) -> bool {
        match global {
            GlobalRef::Static(_) => true,
            GlobalRef::Alloc(_) => self.config.anon_allocs_as_globals,
        }
    }

    /// Read the raw bytes of an evaluated operand, keeping track of uninitialized bytes and pointer
    /// provenance.
    pub(crate) fn read_raw_bytes(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        op: &OpTy<'tcx>,
    ) -> InterpResult<'tcx, Vec<Byte<'tcx>>> {
        op.as_mplace_or_imm().either(
            |mplace| self.read_mplace_bytes(ecx, &mplace),
            |imm| interp_ok(self.read_imm_bytes(&imm)),
        )
    }

    /// The bytes of an immediate, which is made of at most two scalars.
    fn read_imm_bytes(&self, imm: &ImmTy<'tcx>) -> Vec<Byte<'tcx>> {
        let mut bytes = vec![Byte::Uninit; imm.layout.size.bytes_usize()];
        let mut write = |offset: Size, scalar: interpret::Scalar| {
            match scalar {
                interpret::Scalar::Int(int) => {
                    let mut scalar = vec![0; int.size().bytes_usize()];
                    let endian = self.tcx.data_layout.endian;
                    interpret::write_target_uint(endian, &mut scalar, int.to_bits(int.size()))
                        .unwrap();
                    for (i, b) in scalar.into_iter().enumerate() {
                        bytes[offset.bytes_usize() + i] = Byte::Value(b);
                    }
                }
                interpret::Scalar::Ptr(ptr, size) => {
                    let (prov, ptr_offset) = ptr.into_raw_parts();
                    let size = Size::from_bytes(size.get());
                    for (i, byte) in self.ptr_bytes(prov, ptr_offset.bytes(), size).enumerate() {
                        bytes[offset.bytes_usize() + i] = byte;
                    }
                }
            };
        };
        match **imm {
            Immediate::Uninit => {}
            Immediate::Scalar(a) => write(Size::ZERO, a),
            Immediate::ScalarPair(a, b) => {
                let rustc_abi::BackendRepr::ScalarPair { b_offset, .. } = imm.layout.backend_repr
                else {
                    unreachable!()
                };
                write(Size::ZERO, a);
                write(b_offset, b);
            }
        }
        bytes
    }

    /// The bytes of a value in memory.
    fn read_mplace_bytes(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        mplace: &MPlaceTy<'tcx>,
    ) -> InterpResult<'tcx, Vec<Byte<'tcx>>> {
        let size = mplace.layout.size;
        if size.bytes() == 0 {
            return interp_ok(vec![]);
        }
        let (alloc_id, offset, _) = ecx.ptr_get_alloc_id(mplace.ptr(), size.bytes() as i64)?;
        let alloc = ecx.get_alloc_raw(alloc_id)?;
        let range = interpret::alloc_range(offset, size);
        let raw_bytes = alloc.get_bytes_unchecked(range);
        let mut bytes: Vec<Byte<'tcx>> = (0..size.bytes())
            .map(
                |i| match alloc.init_mask().get(offset + Size::from_bytes(i)) {
                    true => Byte::Value(raw_bytes[i as usize]),
                    false => Byte::Uninit,
                },
            )
            .collect();

        // Interned allocations have no pointer fragments, so these are all whole pointers, whose
        // bytes hold their offset into their target. A pointer may straddle the boundaries of
        // `range`.
        let endian = self.tcx.data_layout.endian;
        for (prov_range, prov) in alloc.provenance().get_range(range, ecx) {
            let raw_offset = alloc.get_bytes_unchecked(prov_range);
            let ptr_offset = interpret::read_target_uint(endian, raw_offset).unwrap() as u64;
            for (i, byte) in self
                .ptr_bytes(prov, ptr_offset, prov_range.size)
                .enumerate()
            {
                let pos = prov_range.start + Size::from_bytes(i);
                if range.start <= pos && pos < range.end() {
                    bytes[(pos - range.start).bytes_usize()] = byte;
                }
            }
        }
        interp_ok(bytes)
    }

    /// The bytes of a pointer of size `size` with provenance `prov`, located `offset` bytes after
    /// the start of its target (as an unsigned integer of that size).
    fn ptr_bytes(
        &self,
        prov: interpret::CtfeProvenance,
        offset: u64,
        size: Size,
    ) -> impl Iterator<Item = Byte<'tcx>> {
        let target = self.alloc_target(prov.alloc_id());
        // The offsets of the pointers of a `TypeId` are chunks of its type's hash, which
        // `AllocTarget::TypeId` already stands for, so we drop them. We can't tell which pointer of
        // the `TypeId` this is, so unlike when reading a `TypeId` value, we accept any chunk: a
        // forged `TypeId` whose pointers are swapped looks like a real one in raw memory.
        let offset = match target {
            AllocTarget::TypeId(ty) if type_id_offsets(self.tcx, ty).contains(&offset) => 0,
            _ => size.sign_extend(offset.into()) as i64,
        };
        (0..size.bytes()).map(move |index| Byte::Ptr {
            target,
            offset,
            index: index as u8,
        })
    }

    /// The sized type that `tail`, the unsized tail of `place`, was unsized from. This is found in
    /// the metadata of the place.
    pub(crate) fn sized_tail(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        place: &MPlaceTy<'tcx>,
        tail: Ty<'tcx>,
    ) -> InterpResult<'tcx, Ty<'tcx>> {
        let tcx = self.tcx;
        let meta = place.meta().unwrap_meta();
        interp_ok(match tail.kind() {
            ty::Slice(_) | ty::Str => {
                let len = meta.to_target_usize(ecx)?;
                Ty::new_array(tcx, tail.sequence_element_type(tcx), len)
            }
            ty::Dynamic(preds, ..) => ecx.get_ptr_vtable_ty(meta.to_pointer(ecx), Some(preds))?,
            _ => unreachable!("unexpected unsized tail type {tail:?}"),
        })
    }

    /// Read a `TypeId`. It is made of pointers into the `TypeId` allocation of its type, whose
    /// offsets are the chunks of the type's hash (see rustc's `write_type_id`). Other values (e.g.
    /// transmuted pointers) aren't the `TypeId` of any type.
    fn read_type_id(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        op: &OpTy<'tcx>,
    ) -> InterpResult<'tcx, ConstKind<'tcx>> {
        let ptrs = ecx.project_field(op, FieldIdx::ZERO)?;
        let mut parts = vec![];
        for i in 0..ptrs.len(ecx)? {
            let ptr = ecx.read_pointer(&ecx.project_index(&ptrs, i)?)?;
            parts.push(ptr.into_raw_parts());
        }
        // A `TypeId` points into the `TypeId` allocation of its type, at the chunks of its hash.
        if let Some(prov) = parts[0].0
            && let AllocTarget::TypeId(ty) = self.alloc_target(prov.alloc_id())
            && parts
                .iter()
                .zip(type_id_offsets(self.tcx, ty))
                .all(|(&(p, offset), expected)| p == Some(prov) && offset.bytes() == expected)
        {
            return interp_ok(ConstKind::TypeId(ty));
        }
        interp_ok(ConstKind::Unsupported("`TypeId` not made by `TypeId::of`"))
    }

    /// Read an evaluated operand back as a structured constant.
    pub(crate) fn read_op(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        op: OpTy<'tcx>,
    ) -> InterpResult<'tcx, Const<'tcx>> {
        // Code inspired from `try_destructure_mir_constant_for_user_output` and
        // `const_eval::eval_queries::op_to_const`.
        let ty = op.layout.ty;
        // Helper for struct-likes.
        let read_fields = |of: OpTy<'tcx>, field_count| {
            (0..field_count)
                .map(move |i| {
                    let field_op = ecx.project_field(&of, FieldIdx::from_usize(i))?;
                    self.read_op(ecx, field_op)
                })
                .collect::<InterpResult<Vec<_>>>()
        };
        let kind = match ty.kind() {
            ty::Char | ty::Bool | ty::Uint(_) | ty::Int(_) | ty::Float(_) => {
                ConstKind::Scalar(ecx.read_scalar(&op)?.to_scalar_int()?)
            }
            ty::Adt(adt_def, ..) if adt_def.is_union() => {
                ConstKind::Memory(self.read_raw_bytes(ecx, &op)?)
            }
            ty::Adt(adt_def, ..) if self.tcx.is_lang_item(adt_def.did(), LangItem::TypeId) => {
                self.read_type_id(ecx, &op)?
            }
            ty::Adt(adt_def, ..) => {
                let variant = ecx.read_discriminant(&op)?;
                let op = if adt_def.is_enum() {
                    ecx.project_downcast(&op, variant)?
                } else {
                    op
                };
                let field_count = adt_def.variants()[variant].fields.len();
                ConstKind::Aggregate {
                    variant: Some(variant),
                    fields: read_fields(op, field_count)?,
                }
            }
            // A closure is essentially an adt with funky generics and some builtin impls.
            ty::Closure(_, args) => ConstKind::Aggregate {
                variant: None,
                fields: read_fields(op, args.as_closure().upvar_tys().len())?,
            },
            ty::Tuple(args) => ConstKind::Aggregate {
                variant: None,
                fields: read_fields(op, args.len())?,
            },
            ty::Array(..) | ty::Slice(..) => {
                let mut elems = ecx.project_array_fields(&op)?;
                let mut fields = vec![];
                while let Some((_, elem)) = elems.next(ecx)? {
                    fields.push(self.read_op(ecx, elem)?);
                }
                ConstKind::Aggregate {
                    variant: None,
                    fields,
                }
            }
            ty::Str => {
                let place = op.assert_mem_place();
                let len = Size::from_bytes(place.len(ecx)?);
                let bytes = ecx.read_bytes_ptr_strip_provenance(place.ptr(), len)?;
                ConstKind::str(bytes.to_vec())
            }
            ty::FnDef(..) => ConstKind::fn_def(self.tcx, ty),
            ty::FnPtr(..) => {
                let fn_ptr = ecx.read_pointer(&op)?;
                let FnVal::Instance(instance) = ecx.get_ptr_fn(fn_ptr)?;
                ConstKind::FnPtr(FnTarget::new(instance, Some(ty)))
            }
            ty::RawPtr(..) | ty::Ref(..) => return self.read_pointer(ecx, &op),
            ty::Pat(..) => {
                let op = ecx.project_field(&op, FieldIdx::from_u16(0))?;
                self.read_op(ecx, op)?.kind
            }
            ty::Dynamic(..) => {
                let place = op.assert_mem_place();
                let concrete_ty = self.sized_tail(ecx, &place, ty)?;
                let place = place.offset(Size::ZERO, ecx.layout_of(concrete_ty)?, ecx)?;
                return self.read_op(ecx, place.into());
            }
            ty::Foreign(..)
            | ty::UnsafeBinder(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::CoroutineWitness(..) => ConstKind::Unsupported("Unhandled constant type"),
            // E.g. a trivial const read with generic arguments.
            ty::Alias(..) | ty::Param(..) => ConstKind::Unsupported("constant of generic type"),
            ty::Bound(..) | ty::Placeholder(..) | ty::Infer(..) | ty::Never | ty::Error(..) => {
                unreachable!("evaluated constant of invalid type {ty:?}")
            }
        };
        interp_ok(Const { ty, kind })
    }
}

/// The offsets of the pointers that make up the `TypeId` of `ty`: the chunks of its hash (see
/// rustc's `write_type_id`).
fn type_id_offsets<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Vec<u64> {
    let dl = &tcx.data_layout;
    let hash = tcx.type_id_hash(ty).as_u128();
    let hash = match dl.endian {
        rustc_abi::Endian::Little => hash.to_le_bytes(),
        rustc_abi::Endian::Big => hash.to_be_bytes(),
    };
    hash.chunks(dl.pointer_size().bytes_usize())
        .map(|chunk| interpret::read_target_uint(dl.endian, chunk).unwrap() as u64)
        .collect()
}
