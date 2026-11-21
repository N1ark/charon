//! Evaluating constants with rustc's const-eval. This is the one place that knows how to get the
//! value of each kind of constant.
use crate::*;
use rustc_attr_ir::LangItem;
use rustc_const_eval::const_eval;
use rustc_middle::ty::TypeVisitableExt;
use rustc_span::Span;
use rustc_trait_elaboration::normalize;

/// An evaluated constant.
enum Evaluated<'tcx> {
    /// A type-system value.
    ValTree(ty::Value<'tcx>),
    /// A value in const-eval memory.
    Value(mir::ConstValue, Ty<'tcx>),
}

impl GlobalRef {
    /// The mutability of this global.
    pub fn mutability(self, tcx: TyCtxt<'_>) -> mir::Mutability {
        match self {
            GlobalRef::Static(def_id) => tcx.static_mutability(def_id).unwrap(),
            GlobalRef::Alloc(_) => self.memory(tcx).unwrap().inner().mutability,
        }
    }

    /// The memory of this global. Returns `None` for a static whose evaluation fails, or that has
    /// no initializer (in an `extern` block).
    pub fn memory<'tcx>(self, tcx: TyCtxt<'tcx>) -> Option<interpret::ConstAllocation<'tcx>> {
        let def_id = match self {
            GlobalRef::Static(def_id) if tcx.is_foreign_item(def_id) => return None,
            GlobalRef::Static(def_id) => def_id,
            GlobalRef::Alloc(alloc_id) => match tcx.global_alloc(alloc_id) {
                interpret::GlobalAlloc::Memory(alloc) => return Some(alloc),
                // A nested static.
                interpret::GlobalAlloc::Static(def_id) => def_id,
                alloc => unreachable!("unexpected GlobalRef::Alloc: {alloc:?}"),
            },
        };
        tcx.eval_static_initializer(def_id).ok()
    }
}

impl<'tcx> AllocTypes<'tcx> {
    /// The view of this allocation, deciding it with `default` if it has none yet.
    fn lookup(
        &self,
        alloc_id: interpret::AllocId,
        default: impl FnOnce() -> AllocView<'tcx>,
    ) -> AllocView<'tcx> {
        {
            let data = self.0.lock();
            if data.lookups.is_none()
                && let Some(view) = data.views.get(&alloc_id)
            {
                return *view;
            }
        }
        // `default` may run rustc queries: other threads must not wait for us meanwhile, as they
        // would keep their rustc thread slots, which we may need to continue.
        let default = default();
        let mut data = self.0.lock();
        let data = &mut *data;
        let view = *data.views.entry(alloc_id).or_insert(default);
        let Some(lookups) = &mut data.lookups else {
            return view;
        };
        let lookups = lookups.entry(std::thread::current().id()).or_default();
        lookups.push(ViewLookup {
            alloc_id,
            default,
            view,
        });
        view
    }

    /// Gets the view for this allocation; if none had been decided, it is now viewed untyped.
    pub(crate) fn get(&self, alloc_id: interpret::AllocId) -> AllocView<'tcx> {
        self.lookup(alloc_id, || AllocView::Untyped)
    }

    /// The promoted MIR of this local item as rustc built it, unless rustc's checks stole it. We
    /// read it once and keep it: const-eval steals it, which panics if another thread is reading
    /// it, so we fill this before evaluating anything of the item.
    pub(crate) fn raw_promoteds(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: rustc_hir::def_id::LocalDefId,
    ) -> Option<std::sync::Arc<rustc_index::IndexVec<mir::Promoted, mir::Body<'tcx>>>> {
        if let Some(raw) = self.0.lock().raw_promoteds.get(&def_id) {
            return raw.clone();
        }
        wait_for_rustc_checks(tcx, def_id.to_def_id());
        // We don't hold the lock across this query, see `update_if_unset`.
        let (_, promoteds) = tcx.mir_promoted(def_id);
        let mut data = self.0.lock();
        data.raw_promoteds
            .entry(def_id)
            .or_insert_with(|| {
                (!promoteds.is_stolen()).then(|| std::sync::Arc::new(promoteds.borrow().clone()))
            })
            .clone()
    }

    /// Start recording the lookups of views.
    pub fn record_lookups(&self) {
        self.0.lock().lookups.get_or_insert_default();
    }

    /// Take the lookups this thread recorded so far.
    pub fn take_lookups(&self) -> Vec<ViewLookup<'tcx>> {
        let mut data = self.0.lock();
        let lookups = data.lookups.as_mut().unwrap();
        lookups
            .remove(&std::thread::current().id())
            .unwrap_or_default()
    }

    /// Put back lookups taken with `take_lookups`, as if this thread recorded them now.
    pub fn put_back_lookups(&self, lookups: Vec<ViewLookup<'tcx>>) {
        if lookups.is_empty() {
            return;
        }
        let mut data = self.0.lock();
        let recorded = data.lookups.as_mut().unwrap();
        recorded
            .entry(std::thread::current().id())
            .or_default()
            .extend(lookups);
    }

    /// Set the view of this allocation, even if it had one.
    pub fn force_view(&self, alloc_id: interpret::AllocId, view: AllocView<'tcx>) {
        self.0.lock().views.insert(alloc_id, view);
    }

    /// The view decided for this allocation, if any: `Some(None)` if it is viewed untyped.
    pub fn decided_view(&self, alloc_id: interpret::AllocId) -> Option<Option<Ty<'tcx>>> {
        self.0.lock().views.get(&alloc_id).map(|view| match view {
            AllocView::Untyped => None,
            AllocView::Typed(ty) => Some(*ty),
        })
    }

    /// Decide the view of this allocation, unless it is already decided.
    pub fn decide_view(&self, alloc_id: interpret::AllocId, ty: Option<Ty<'tcx>>) {
        self.update_if_unset(alloc_id, || match ty {
            None => AllocView::Untyped,
            Some(ty) => AllocView::Typed(ty),
        })
    }

    pub(crate) fn update_if_unset(
        &self,
        alloc_id: interpret::AllocId,
        f: impl FnOnce() -> AllocView<'tcx>,
    ) {
        self.lookup(alloc_id, f);
    }

    pub(crate) fn is_typed(&self, alloc_id: interpret::AllocId) -> bool {
        matches!(self.get(alloc_id), AllocView::Typed(_))
    }

    /// The type at which we view the allocation `alloc_id`.
    pub fn ty(&self, tcx: TyCtxt<'tcx>, alloc_id: interpret::AllocId) -> Ty<'tcx> {
        if let AllocView::Typed(ty) = self.get(alloc_id) {
            return ty;
        }
        // if we haven't seen it with a type, then it's untyped!
        let size = GlobalRef::Alloc(alloc_id)
            .memory(tcx)
            .unwrap()
            .inner()
            .size();
        let bytes = Ty::new_array(tcx, tcx.types.u8, size.bytes());
        let maybe_uninit = tcx.require_lang_item(LangItem::MaybeUninit, rustc_span::DUMMY_SP);
        Ty::new_adt(tcx, tcx.adt_def(maybe_uninit), tcx.mk_args(&[bytes.into()]))
    }
}

impl<'tcx> AllocTarget<'tcx> {
    /// Whether this target is read as its typed value.
    pub(crate) fn is_read_typed(&self, views: &AllocTypes<'tcx>) -> bool {
        match self {
            AllocTarget::Global(GlobalRef::Static(_)) => true,
            AllocTarget::Global(GlobalRef::Alloc(alloc_id)) => views.is_typed(*alloc_id),
            AllocTarget::Fn(_) | AllocTarget::VTable(..) | AllocTarget::TypeId(_) => false,
        }
    }
}

/// Set once rustc's own checks are done. Charon may run them in parallel with the translation.
/// Since they can steal MIR bodies (const-eval steals those of the consts, statics and const fns
/// it evaluates), we wait for them before reading such a body: this way we read the same body as
/// if the checks had run first.
pub static RUSTC_CHECKS_DONE: std::sync::OnceLock<()> = std::sync::OnceLock::new();

/// Whether const-eval may use the MIR of this item.
pub fn may_be_const_evaluated(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    use rustc_hir::def::DefKind;
    match tcx.def_kind(def_id) {
        DefKind::Fn | DefKind::AssocFn | DefKind::Closure => tcx.is_const_fn(def_id),
        _ => true,
    }
}

/// Call before reading a MIR body that may get stolen, see [`RUSTC_CHECKS_DONE`].
pub fn wait_for_rustc_checks(tcx: TyCtxt<'_>, def_id: DefId) {
    if def_id.is_local() && may_be_const_evaluated(tcx, def_id) {
        use rustc_thread_pool::tlv::TLV;
        while RUSTC_CHECKS_DONE.get().is_none() {
            // Rather than blocking, help with pending work (which may be the checks themselves):
            // the other threads may not get to run, e.g. for lack of jobserver tokens. Running a
            // job sets this thread's rustc context (`tls`) to the job's, which may live on another
            // thread's stack; like `join` and `scope`, we restore ours afterwards.
            let context = TLV.with(|tlv| tlv.get());
            let yielded = rustc_thread_pool::yield_now();
            TLV.with(|tlv| tlv.set(context));
            if yielded != Some(rustc_thread_pool::Yield::Executed) {
                std::thread::sleep(std::time::Duration::from_micros(100));
            }
        }
    }
}

/// Call `f` on the MIR of the given promoted constant.
pub fn promoted_body<'tcx, R>(
    tcx: TyCtxt<'tcx>,
    alloc_types: &AllocTypes<'tcx>,
    def_id: DefId,
    promoted: mir::Promoted,
    f: impl FnOnce(&mir::Body<'tcx>) -> R,
) -> R {
    // The promoteds of a local item are stolen once its MIR is optimized.
    if let Some(local_def_id) = def_id.as_local()
        && let Some(promoteds) = alloc_types.raw_promoteds(tcx, local_def_id)
    {
        return f(&promoteds[promoted]);
    }
    f(&tcx.promoted_mir(def_id)[promoted])
}

impl<'tcx> ConstReader<'tcx> {
    /// Evaluate `src` and read it back. `span` is the location rustc should blame for problems
    /// with the evaluation.
    ///
    /// Fails with:
    /// - [`ReadError::NotEvaluable`] if rustc can't evaluate the constant: if it is generic (and
    ///   not trivial, i.e. its value isn't stored directly by rustc), if its evaluation fails, or
    ///   if it's an extern static;
    /// - [`ReadError::NotLoadable`] if the interpreter can't load the evaluated value;
    /// - [`ReadError::Read`] if reading the loaded value fails.
    pub fn read(
        &self,
        span: Span,
        src: ConstSource<'tcx>,
        mode: ReadMode,
    ) -> Result<Const<'tcx>, ReadError<'tcx>> {
        match self.evaluate(span, src)? {
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
    ) -> Result<Evaluated<'tcx>, ReadError<'tcx>> {
        let tcx = self.tcx;
        let instantiate = |ty, args| ty::EarlyBinder::bind(tcx, ty).instantiate(tcx, args);
        Ok(match src {
            ConstSource::Item { def_id, args } => {
                // Evaluating it may steal its promoteds, which we must have read first.
                if let Some(local_def_id) = def_id.as_local() {
                    self.alloc_types.raw_promoteds(tcx, local_def_id);
                }
                let uv = mir::UnevaluatedConst {
                    def: def_id,
                    args,
                    promoted: None,
                };
                let ty = tcx
                    .type_of(def_id)
                    .instantiate_identity()
                    .skip_normalization();
                let val = tcx
                    .const_eval_resolve(self.eval_typing_env(args), uv, span)
                    .ok();
                let evaluated = val.map(|val| (val, ty));
                // Otherwise, we can still read the value of "trivial" consts, which rustc
                // stores directly. This works even for generic consts.
                let (val, ty) = evaluated
                    .or_else(|| tcx.trivial_const(def_id))
                    .ok_or(ReadError::NotEvaluable)?;
                Evaluated::Value(val, instantiate(ty, args).skip_normalization())
            }
            ConstSource::Promoted {
                def_id,
                args,
                promoted,
            } => {
                // Evaluating it steals the promoteds, which we must have read first.
                if let Some(local_def_id) = def_id.as_local() {
                    self.alloc_types.raw_promoteds(tcx, local_def_id);
                }
                let uv = mir::UnevaluatedConst {
                    def: def_id,
                    args,
                    promoted: Some(promoted),
                };
                let val = tcx
                    .const_eval_resolve(self.eval_typing_env(args), uv, span)
                    .map_err(|_| ReadError::NotEvaluable)?;
                // Promoteds aren't items so `type_of` doesn't work for them; instead we read
                // their type off the return place of their MIR body.
                let ty = promoted_body(tcx, &self.alloc_types, def_id, promoted, |body| {
                    body.local_decls[mir::RETURN_PLACE].ty
                });
                Evaluated::Value(val, instantiate(ty, args).skip_normalization())
            }
            ConstSource::Global(global) => {
                let alloc = global.memory(tcx).ok_or(ReadError::NotEvaluable)?;
                // A mutable allocation (e.g. of a `static mut`, or of a static whose type has
                // interior mutability) can't be read by const-eval. We don't care though, so we
                // reintern it as immutable.
                let alloc = if alloc.inner().mutability.is_mut() {
                    let mut alloc = alloc.inner().clone();
                    alloc.mutability = mir::Mutability::Not;
                    tcx.mk_const_alloc(alloc)
                } else {
                    alloc
                };
                // Give the allocation a fresh `AllocId` so we can read it like any other
                // allocation. This creates a fresh `AllocId` each time we read the global. This
                // doesn't break sharing.
                let val = mir::ConstValue::Indirect {
                    alloc_id: tcx.reserve_and_set_memory_alloc(alloc),
                    offset: rustc_abi::Size::ZERO,
                };
                Evaluated::Value(val, self.global_ty(global))
            }
            // Evaluate these only if they represent anon consts that don't show up in the type
            // system (e.g. through `adt_const_params`).
            ConstSource::TyConst(uv)
                if let Some(def_id) = uv.kind.opt_def_id()
                    && let rustc_hir::def::DefKind::AnonConst = tcx.def_kind(def_id)
                    && let ty::AnonConstKind::NonTypeSystemInline = tcx.anon_const_kind(def_id)
                    && !uv.has_opaque_types() =>
            {
                return self.evaluate(
                    span,
                    ConstSource::Item {
                        def_id,
                        args: uv.args,
                    },
                );
            }
            ConstSource::TyConst(uv) => {
                let value = self.eval_to_valtree(span, uv);
                Evaluated::ValTree(value.ok_or(ReadError::NotEvaluable)?)
            }
            ConstSource::ValTree(value) => Evaluated::ValTree(value),
            ConstSource::Value(val, ty) => Evaluated::Value(val, ty),
        })
    }

    /// Evaluate a type-level constant to a valtree. Returns `None` if the constant is generic, if
    /// its evaluation fails, or if its type has no valtree representation.
    fn eval_to_valtree(&self, span: Span, uv: ty::AliasConst<'tcx>) -> Option<ty::Value<'tcx>> {
        let tcx = self.tcx;
        if uv.has_non_region_param() {
            return None;
        }
        let def = uv.kind.opt_def_id()?;
        let erased_uv = tcx.erase_and_anonymize_regions(uv);
        let valtree = tcx
            .const_eval_resolve_for_typeck(self.eval_typing_env(erased_uv), erased_uv, span)
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

    /// The typing environment in which to evaluate a constant with arguments `args`: the empty one
    /// if the current one can't matter, i.e. `args` mention no parameters and every clause of the
    /// current environment mentions a type or const parameter.
    fn eval_typing_env(&self, args: impl TypeVisitableExt<TyCtxt<'tcx>>) -> ty::TypingEnv<'tcx> {
        // rustc caches evaluations per typing environment: this evaluates a constant used by many
        // items only once. A clause without type or const parameters (e.g. `where Foo: Trait` with
        // `trivial_bounds`, or a clause that only mentions lifetimes, which are erased) may apply
        // to `args`.
        let env_independent = !args.has_param()
            && self
                .typing_env
                .param_env
                .caller_bounds()
                .all(|clause| clause.has_non_region_param());
        if env_independent {
            ty::TypingEnv::fully_monomorphized()
        } else {
            self.typing_env
        }
    }

    /// The type at which we read a global.
    pub fn global_ty(&self, global: GlobalRef) -> Ty<'tcx> {
        let tcx = self.tcx;
        match global {
            GlobalRef::Static(def_id) => self.normalize(
                tcx.type_of(def_id)
                    .instantiate_identity()
                    .skip_normalization(),
            ),
            GlobalRef::Alloc(alloc_id) => self.alloc_types.ty(tcx, alloc_id),
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
        // Fast paths: there are lots of `FnDef` constants (one per function call) and scalar
        // literals, which `read_op` would read back as is.
        if mode == ReadMode::Structured && matches!(ty.kind(), ty::FnDef(..)) {
            return Ok(Const {
                ty,
                kind: ConstKind::fn_def(self.tcx, ty),
            });
        }
        if mode == ReadMode::Structured
            && let mir::ConstValue::Scalar(interpret::Scalar::Int(int)) = val
            && matches!(
                ty.kind(),
                ty::Char | ty::Bool | ty::Uint(_) | ty::Int(_) | ty::Float(_)
            )
        {
            return Ok(Const {
                ty,
                kind: ConstKind::Scalar(int),
            });
        }
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
