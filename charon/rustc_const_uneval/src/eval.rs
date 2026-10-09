//! Evaluating constants with rustc's const-eval. This is the one place that knows how to get the
//! value of each kind of constant.
use crate::*;
use rustc_attr_ir::LangItem;
use rustc_const_eval::const_eval;
use rustc_span::Span;
use rustc_trait_elaboration::normalize;

/// An evaluated constant.
enum Evaluated<'tcx> {
    /// A type-system value.
    ValTree(ty::Value<'tcx>),
    /// A value in const-eval memory.
    Value(mir::ConstValue, Ty<'tcx>),
}

/// Call `f` on the MIR of the given promoted constant.
pub fn promoted_body<'tcx, R>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    promoted: mir::Promoted,
    f: impl FnOnce(&mir::Body<'tcx>) -> R,
) -> R {
    // The promoteds of a local item are stolen once its MIR is optimized.
    if let Some(local_def_id) = def_id.as_local() {
        let (_, promoteds) = tcx.mir_promoted(local_def_id);
        if !promoteds.is_stolen() {
            return f(&promoteds.borrow()[promoted]);
        }
    }
    f(&tcx.promoted_mir(def_id)[promoted])
}

impl<'tcx> ConstReader<'tcx> {
    /// Evaluate `src` and read it back. `span` is the location rustc should blame for problems
    /// with the evaluation.
    ///
    /// Fails with:
    /// - [`ReadError::NotEvaluable`] if rustc can't evaluate the constant: if it is generic (and
    ///   not trivial, i.e. its value isn't stored directly by rustc), if its evaluation fails, if
    ///   it's an extern static, or if it's a promoted read in [`ReadMode::Structured`] while we
    ///   don't name allocations (see [`Config::anon_allocs_as_globals`]);
    /// - [`ReadError::NotLoadable`] if the interpreter can't load the evaluated value;
    /// - [`ReadError::Read`] if reading the loaded value fails.
    pub fn read(
        &self,
        span: Span,
        src: ConstSource<'tcx>,
        mode: ReadMode,
    ) -> Result<Const<'tcx>, ReadError<'tcx>> {
        match self.evaluate(span, src, mode)? {
            Evaluated::ValTree(value) if mode == ReadMode::Structured => {
                self.read_valtree(span, value)
            }
            Evaluated::ValTree(value) => {
                let ty = self.normalize(value.ty);
                let val = self.tcx.valtree_to_const_val(ty::Value { ty, ..value });
                self.read_const_value(span, val, ty, mode)
            }
            Evaluated::Value(val, ty) => self.read_const_value(span, val, self.normalize(ty), mode),
        }
    }

    /// Ask rustc for the value of `src`.
    fn evaluate(
        &self,
        span: Span,
        src: ConstSource<'tcx>,
        mode: ReadMode,
    ) -> Result<Evaluated<'tcx>, ReadError<'tcx>> {
        let tcx = self.tcx;
        let instantiate = |ty, args| ty::EarlyBinder::bind(tcx, ty).instantiate(tcx, args);
        let resolve = |def, args, promoted| {
            let uv = mir::UnevaluatedConst {
                def,
                args,
                promoted,
            };
            tcx.const_eval_resolve(self.typing_env, uv, span).ok()
        };
        Ok(match src {
            ConstSource::Item { def_id, args } => {
                let evaluated = match mode {
                    ReadMode::Structured
                        if let Some(evaluated) = self.eval_to_alloc(def_id, args, None) =>
                    {
                        return Ok(evaluated);
                    }
                    ReadMode::Structured => {
                        let kind = ty::AliasConstKind::new_from_def_id(
                            tcx,
                            def_id,
                            ty::AliasConstInherentArgsKind::Impl,
                        );
                        let uv = ty::AliasConst::new(tcx, kind, args);
                        if let Some(value) = self.eval_to_valtree(span, uv) {
                            return Ok(Evaluated::ValTree(value));
                        }
                        None
                    }
                    ReadMode::Bytes => resolve(def_id, args, None).map(|val| {
                        let ty = tcx.type_of(def_id).instantiate_identity();
                        (val, ty.skip_normalization())
                    }),
                };
                // Rustc can't evaluate a generic const, evaluation may fail, and a structured read
                // through a valtree fails for types without a valtree representation (e.g. raw
                // pointers or unions). We can still read the value of "trivial" consts, which
                // rustc stores directly.
                let (val, ty) = evaluated
                    .or_else(|| tcx.trivial_const(def_id))
                    .ok_or(ReadError::NotEvaluable)?;
                Evaluated::Value(val, instantiate(ty, args).skip_normalization())
            }
            ConstSource::Promoted {
                def_id,
                args,
                promoted,
            } => match mode {
                // We can't go through valtrees for promoteds as we can't name them as type-level
                // constants, so when we don't name allocations we only read them as bytes.
                ReadMode::Structured => self
                    .eval_to_alloc(def_id, args, Some(promoted))
                    .ok_or(ReadError::NotEvaluable)?,
                ReadMode::Bytes => {
                    let val =
                        resolve(def_id, args, Some(promoted)).ok_or(ReadError::NotEvaluable)?;
                    // Promoteds aren't items so `type_of` doesn't work for them; instead we read
                    // their type off the return place of their MIR body.
                    let ty = promoted_body(tcx, def_id, promoted, |body| {
                        body.local_decls[mir::RETURN_PLACE].ty
                    });
                    Evaluated::Value(val, instantiate(ty, args).skip_normalization())
                }
            },
            ConstSource::Global(global) => {
                let alloc_id = match global {
                    // Statics in `extern` blocks have no initializer.
                    GlobalRef::Static(def_id) if tcx.is_foreign_item(def_id) => {
                        return Err(ReadError::NotEvaluable);
                    }
                    GlobalRef::Static(def_id) => {
                        let alloc = tcx
                            .eval_static_initializer(def_id)
                            .map_err(|_| ReadError::NotEvaluable)?;
                        // A static whose type has interior mutability gets a mutable allocation,
                        // which const-eval refuses to read. We don't care though, so we reintern
                        // it as immutable.
                        let alloc = if alloc.inner().mutability.is_mut() {
                            let mut alloc = alloc.inner().clone();
                            alloc.mutability = mir::Mutability::Not;
                            tcx.mk_const_alloc(alloc)
                        } else {
                            alloc
                        };
                        // `eval_static_initializer` returns an interned allocation without an
                        // `AllocId`; give it one so we can read it like any other allocation.
                        // This creates a fresh `AllocId` each time we read the static.
                        // FIXME: this breaks sharing.
                        tcx.reserve_and_set_memory_alloc(alloc)
                    }
                    GlobalRef::Alloc(alloc_id) => alloc_id,
                };
                let val = mir::ConstValue::Indirect {
                    alloc_id,
                    offset: rustc_abi::Size::ZERO,
                };
                Evaluated::Value(val, self.global_ty(global))
            }
            ConstSource::TyConst(uv)
                if let Some(def_id) = uv.kind.opt_def_id()
                    && let Some(evaluated) = self.eval_to_alloc(def_id, uv.args, None) =>
            {
                evaluated
            }
            ConstSource::TyConst(uv) => {
                let value = self.eval_to_valtree(span, uv);
                Evaluated::ValTree(value.ok_or(ReadError::NotEvaluable)?)
            }
            ConstSource::ValTree(value) => Evaluated::ValTree(value),
            ConstSource::Value(val, ty) => Evaluated::Value(val, ty),
        })
    }

    /// When we name allocations, evaluate a constant (or one of its promoteds) to an allocation.
    /// Unlike valtrees, this keeps track of the allocations the value points to, which can then
    /// become globals. Returns `None` if we don't name allocations, or if rustc can't evaluate the
    /// constant (e.g. if its value depends on generic parameters).
    fn eval_to_alloc(
        &self,
        def_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
        promoted: Option<mir::Promoted>,
    ) -> Option<Evaluated<'tcx>> {
        if !self.config.anon_allocs_as_globals {
            return None;
        }
        let tcx = self.tcx;
        let instance = ty::Instance::try_resolve(tcx, self.typing_env, def_id, args).ok()??;
        let cid = interpret::GlobalId { instance, promoted };
        let alloc = tcx
            .eval_to_allocation_raw(self.typing_env.as_query_input(cid))
            .ok()?;
        let val = mir::ConstValue::Indirect {
            alloc_id: alloc.alloc_id,
            offset: rustc_abi::Size::ZERO,
        };
        Some(Evaluated::Value(val, alloc.ty))
    }

    /// Evaluate a type-level constant to a valtree. Returns `None` if the constant is generic, if
    /// its evaluation fails, or if its type has no valtree representation.
    fn eval_to_valtree(&self, span: Span, uv: ty::AliasConst<'tcx>) -> Option<ty::Value<'tcx>> {
        use ty::TypeVisitableExt;
        let tcx = self.tcx;
        if uv.has_non_region_param() {
            return None;
        }
        let def = uv.kind.opt_def_id()?;
        let erased_uv = tcx.erase_and_anonymize_regions(uv);
        let valtree = tcx
            .const_eval_resolve_for_typeck(self.typing_env, erased_uv, span)
            .ok()?
            .ok()?;
        let ty = tcx
            .type_of(def)
            .instantiate(tcx, uv.args)
            .skip_normalization();
        Some(ty::Value {
            ty: self.normalize(ty),
            valtree,
        })
    }

    /// The type at which we read a global: the type of a static, or `MaybeUninit<[u8; N]>` for
    /// an allocation without a corresponding item.
    pub fn global_ty(&self, global: GlobalRef) -> Ty<'tcx> {
        let tcx = self.tcx;
        match global {
            GlobalRef::Static(def_id) => self.normalize(
                tcx.type_of(def_id)
                    .instantiate_identity()
                    .skip_normalization(),
            ),
            GlobalRef::Alloc(alloc_id) => {
                let (size, _) = tcx
                    .global_alloc(alloc_id)
                    .size_and_align(tcx, self.typing_env);
                let bytes = Ty::new_array(tcx, tcx.types.u8, size.bytes());
                let maybe_uninit =
                    tcx.require_lang_item(LangItem::MaybeUninit, rustc_span::DUMMY_SP);
                Ty::new_adt(tcx, tcx.adt_def(maybe_uninit), tcx.mk_args(&[bytes.into()]))
            }
        }
    }

    /// Read `val`, a value of type `ty` in const-eval memory.
    pub(crate) fn read_const_value(
        &self,
        span: Span,
        val: mir::ConstValue,
        ty: Ty<'tcx>,
        mode: ReadMode,
    ) -> Result<Const<'tcx>, ReadError<'tcx>> {
        let (ecx, op) =
            const_eval::mk_eval_cx_for_const_val(self.tcx.at(span), self.typing_env, val, ty)
                .ok_or(ReadError::NotLoadable)?;
        let read = match mode {
            ReadMode::Structured => self.read_op(&ecx, op),
            ReadMode::Bytes => self.read_raw_bytes(&ecx, &op).map(|bytes| Const {
                ty,
                kind: ConstKind::Memory(bytes),
            }),
        };
        Ok(read.report_err()?)
    }

    pub(crate) fn normalize(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        normalize(self.tcx, self.typing_env, ty::Unnormalized::new_wip(ty))
    }
}
