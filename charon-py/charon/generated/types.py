"""WARNING: this file is auto-generated. Do not edit `types.py` by hand. Edit
`generate_py/templates/types.py` instead, or improve the code generation tool so as to avoid the
need for hand-writing things.

`generate_py/templates/types.py` contains the manual definitions and some `# __REPLACEn__`
comments. These comments are replaced by auto-generated definitions by running `make
generate-asts` in the crate root. The code-generation code is in `charon/src/bin/generate-asts`.

Enums are represented as a union of one dataclass per variant, which is how a type checker
understands a tagged union. Since the AST is deeply recursive, all the annotations here are
forward references; `from __future__ import annotations` makes that work.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Generic, NewType, NoReturn, Optional, TypeAlias, TypeVar, Union

T0 = TypeVar("T0")
T1 = TypeVar("T1")
T2 = TypeVar("T2")
T3 = TypeVar("T3")

@dataclass
class AbiRust:
    pass

@dataclass
class AbiC:
    pass

@dataclass
class AbiOther:
    r"""Rust's spelling for the ABI, e.g. "C-unwind" or "system"."""
    _0: str

Abi: TypeAlias = "Union[AbiRust, AbiC, AbiOther]"


@dataclass
class AbortKindPanic:
    r"""A built-in panicking function, or a panic due to a failed built-in check (e.g. for out-of-bounds accesses)."""
    _0: Optional[Name]

@dataclass
class AbortKindUndefinedBehavior:
    r"""Undefined behavior in the rust abstract machine."""

@dataclass
class AbortKindUnwindTerminate:
    r"""Unwind had to stop for ABI reasons or because cleanup code panicked again."""

# (U)LLBC is a language with side-effects: a statement may abort in a way that isn't tracked by
# control-flow. The three kinds of abort are:
# - Panic
# - Undefined behavior (caused by an "assume")
# - Unwind termination
AbortKind: TypeAlias = "Union[AbortKindPanic, AbortKindUndefinedBehavior, AbortKindUnwindTerminate]"


@dataclass
class AggregateKindAggregatedAdt:
    r"""A struct, enum or union aggregate. The `VariantId`, if present, indicates this is an enum
    and the aggregate uses that variant. The `FieldId`, if present, indicates this is a union
    and the aggregate writes into that field. Otherwise this is a struct."""
    _0: TypeDeclRef
    _1: Optional[VariantId]
    _2: Optional[FieldId]

@dataclass
class AggregateKindAggregatedArray:
    r"""We don't put this with the ADT cas because this is the only built-in type
    with aggregates, and it is a primitive type. In particular, it makes
    sense to treat it differently because it has a variable number of fields.
    The third field is the proof that the element type is `Sized`; it is absent with
    `--hide-marker-traits`."""
    _0: Ty
    _1: ConstantExpr
    _2: Optional[TraitRef]

@dataclass
class AggregateKindAggregatedRawPtr:
    r"""Construct a raw pointer from a pointer value, and its metadata (can be unit, if building
    a thin pointer). The type is the type of the pointee."""
    _0: Ty
    _1: RefKind

# An aggregated ADT.
# Note that ADTs are desaggregated at some point in MIR. For instance, if
# we have in Rust:
# ```ignore
# let ls = Cons(hd, tl);
# ```
# In MIR we have (yes, the discriminant update happens *at the end* for some
# reason):
# ```text
# (ls as Cons).0 = move hd;
# (ls as Cons).1 = move tl;
# discriminant(ls) = 0; // assuming `Cons` is the variant of index 0
# ```
# Rem.: in the Aeneas semantics, both cases are handled (in case of desaggregated
# initialization, `ls` is initialized to `⊥`, then this `⊥` is expanded to
# `Cons (⊥, ⊥)` upon the first assignment, at which point we can initialize
# the field 0, etc.).
AggregateKind: TypeAlias = "Union[AggregateKindAggregatedAdt, AggregateKindAggregatedArray, AggregateKindAggregatedRawPtr]"


@dataclass
class AlignmentModifierAlign:
    _0: int

@dataclass
class AlignmentModifierPack:
    _0: int

# Describes modifiers to the alignment and packing of the corresponding type.
# Represents `repr(align(n))` and `repr(packed(n))`.
AlignmentModifier: TypeAlias = "Union[AlignmentModifierAlign, AlignmentModifierPack]"


@dataclass
class Assertion:
    r"""Check the value of an operand and abort if the value is not expected. This is introduced to
    avoid a lot of small branches.

    We translate MIR asserts (introduced for out-of-bounds accesses or divisions by zero for
    instance) to this. We then eliminate them in [crate::transform::resugar::reconstruct_fallible_operations],
    because they're implicit in the semantics of our array accesses etc. Finally we introduce new asserts in
    [crate::transform::resugar::reconstruct_asserts]."""
    cond: Operand
    expected: bool
    r"""The value that the operand should evaluate to for the assert to succeed."""
    check_kind: Optional[BuiltinAssertKind]
    r"""The kind of check performed by this assert. This is only used for error reporting, as the check
    is actually performed by the instructions preceding the assert."""


AssocConstId = NewType("AssocConstId", int)


@dataclass
class AssocItemIdAssocIdType:
    _0: AssocTypeId

@dataclass
class AssocItemIdAssocIdMethod:
    _0: TraitMethodId

@dataclass
class AssocItemIdAssocIdConst:
    _0: AssocConstId

# The id of an associated item within a trait.
AssocItemId: TypeAlias = "Union[AssocItemIdAssocIdType, AssocItemIdAssocIdMethod, AssocItemIdAssocIdConst]"


@dataclass
class AssocItemNames:
    types: list[TraitItemName]
    methods: list[TraitItemName]
    consts: list[TraitItemName]


AssocTypeId = NewType("AssocTypeId", int)


@dataclass
class AttrInfo:
    r"""Information about the attributes and visibility of an item, field or variant.."""
    attributes: list[Attribute]
    r"""Attributes (`#[...]`)."""
    inline: Optional[InlineAttr]
    r"""Inline hints (on functions only)."""
    rename: Optional[str]
    r"""The name computed from `charon::rename` and `charon::variants_prefix` attributes, if any.
    This provides a custom name that can be used by consumers of llbc. E.g. Aeneas uses this to
    rename definitions in the extracted code."""
    public: bool
    r"""Whether this item is declared public. Impl blocks and closures don't have visibility
    modifiers; we arbitrarily set this to `false` for them.

    Note that this is different from being part of the crate's public API: to be part of the
    public API, an item has to also be reachable from public items in the crate root. For
    example:
    ```rust,ignore
    mod foo {
        pub struct X;
    }
    mod bar {
        pub fn something(_x: super::foo::X) {}
    }
    pub use bar::something; // exposes `X`
    ```
    Without the `pub use ...`, neither `X` nor `something` would be part of the crate's public
    API (this is called "pub-in-priv" items). With or without the `pub use`, we set `public =
    true`; computing item reachability is harder."""


@dataclass
class AttributeAttrOpaque:
    r"""Do not translate the body of this item.
    Written `#[charon::opaque]`"""

@dataclass
class AttributeAttrExclude:
    r"""Do not translate this item at all.
    Written `#[charon::exclude]`"""

@dataclass
class AttributeAttrRename:
    r"""Provide a new name that consumers of the llbc can use.
    Written `#[charon::rename("new_name")]`"""
    _0: str

@dataclass
class AttributeAttrVariantsPrefix:
    r"""For enums only: rename the variants by pre-pending their names with the given prefix.
    Written `#[charon::variants_prefix("prefix_")]`."""
    _0: str

@dataclass
class AttributeAttrVariantsSuffix:
    r"""Same as `VariantsPrefix`, but appends to the name instead of pre-pending."""
    _0: str

@dataclass
class AttributeAttrTransparent:
    r"""The structure is treated as a transparent wrapper around its sole field.
    Written `#[charon::transparent]`."""

@dataclass
class AttributeAttrIsContract:
    r"""An item annotated with `#[charon::contract(kind = "...", parent)]` or
    `#[charon::contract(kind = "...", for = "...")]`. This makes it a contract for the target
    item."""
    kind: str
    target: MaybeAssocItemId

@dataclass
class AttributeAttrHasContract:
    r"""An item that has a contract that applies to it. The referenced item is the function that
    specifies the contract."""
    kind: str
    contract: FunDeclId

@dataclass
class AttributeAttrDocComment:
    r"""A doc-comment such as `/// ...`."""
    _0: str

@dataclass
class AttributeAttrBuiltin:
    r"""A built-in attribute."""
    _0: RustcAttributeKind

@dataclass
class AttributeAttrUnknown:
    r"""None of the above."""
    _0: RawAttribute

# Attributes (`#[...]`).
Attribute: TypeAlias = "Union[AttributeAttrOpaque, AttributeAttrExclude, AttributeAttrRename, AttributeAttrVariantsPrefix, AttributeAttrVariantsSuffix, AttributeAttrTransparent, AttributeAttrIsContract, AttributeAttrHasContract, AttributeAttrDocComment, AttributeAttrBuiltin, AttributeAttrUnknown]"


@dataclass
class RustcAttributeKindAutomaticallyDerived:
    r"""Represents `#[automatically_derived]`"""

@dataclass
class RustcAttributeKindCold:
    r"""Represents `#[cold]`."""

@dataclass
class RustcAttributeKindDeprecated:
    r"""Represents [`#[deprecated]`](https://doc.rust-lang.org/stable/reference/attributes/diagnostics.html#the-deprecated-attribute)."""
    deprecation: RustcDeprecation
    span: Span

@dataclass
class RustcAttributeKindFundamental:
    r"""Represents `#[fundamental]`."""

@dataclass
class RustcAttributeKindIgnore:
    r"""Represents `#[ignore]`"""
    span: Span
    reason: Optional[str]
    r"""ignore can optionally have a reason: `#[ignore = "reason this is ignored"]`"""

@dataclass
class RustcAttributeKindInline:
    r"""Represents `#[inline]` and `#[rustc_force_inline]`."""
    _0: RustcInlineAttr
    _1: Span

@dataclass
class RustcAttributeKindMayDangle:
    r"""Represents [`#[may_dangle]`](https://std-dev-guide.rust-lang.org/tricky/may-dangle.html)."""
    _0: Span

@dataclass
class RustcAttributeKindNaked:
    r"""Represents `#[naked]`"""
    _0: Span

@dataclass
class RustcAttributeKindNoLink:
    r"""Represents `#[no_link]`"""

@dataclass
class RustcAttributeKindNoMangle:
    r"""Represents `#[no_mangle]`"""
    _0: Span

@dataclass
class RustcAttributeKindNonExhaustive:
    r"""Represents `#[non_exhaustive]`"""
    _0: Span

@dataclass
class RustcAttributeKindOptimize:
    r"""Represents `#[optimize(size|speed)]`"""
    _0: RustcOptimizeAttr
    _1: Span

@dataclass
class RustcAttributeKindRustcAlign:
    r"""Represents `#[align(N)]`."""
    align: int
    span: Span

@dataclass
class RustcAttributeKindRustcIntrinsic:
    r"""Represents `#[rustc_intrinsic]`"""

@dataclass
class RustcAttributeKindRustcTestEntrypointMarker:
    r"""Represents `#[rustc_test_entrypoint_marker]`"""

@dataclass
class RustcAttributeKindShouldPanic:
    r"""Represents `#[should_panic]`"""
    reason: Optional[str]

@dataclass
class RustcAttributeKindTargetFeature:
    r"""Represents `#[target_feature(enable = "...")]` and
    `#[unsafe(force_target_feature(enable = "...")]`."""
    features: list[tuple[str, Span]]
    attr_span: Span
    was_forced: bool

@dataclass
class RustcAttributeKindTrackCaller:
    r"""Represents `#[track_caller]`"""
    _0: Span

# Represents parsed *built-in* inert attributes.
# ## Overview
# These attributes are markers that guide the compilation process and are never expanded into other code.
# They persist throughout the compilation phases, from AST to HIR and beyond.
# ## Attribute Processing
# While attributes are initially parsed by [`rustc_parse`] into [`ast::Attribute`], they still contain raw token streams
# because different attributes have different internal structures. This enum represents the final,
# fully parsed form of these attributes, where each variant contains all the information and
# structure relevant for the specific attribute.
# Some attributes can be applied multiple times to the same item, and they are "collapsed" into a single
# semantic attribute. For example:
# ```rust
# #[repr(C)]
# #[repr(packed)]
# struct S { }
# ```
# This is equivalent to `#[repr(C, packed)]` and results in a single [`AttributeKind::Repr`] containing
# both `C` and `packed` annotations. This collapsing happens during parsing and is reflected in the
# data structures defined in this enum.
# ## Usage
# These parsed attributes are used throughout the compiler to:
# - Control code generation (e.g., `#[repr]`)
# - Mark API stability (`#[stable]`, `#[unstable]`)
# - Provide documentation (`#[doc]`)
# - Guide compiler behavior (e.g., `#[allow_internal_unstable]`)
# ## Note on Attribute Organization
# Some attributes like `InlineAttr`, `OptimizeAttr`, and `InstructionSetAttr` are defined separately
# from this enum because they are used in specific compiler phases (like code generation) and don't
# need to persist throughout the entire compilation process. They are typically processed and
# converted into their final form earlier in the compilation pipeline.
# For example:
# - `InlineAttr` is used during code generation to control function inlining
# - `OptimizeAttr` is used to control optimization levels
# - `InstructionSetAttr` is used for target-specific code generation
# These attributes are handled by their respective compiler passes in the [`rustc_codegen_ssa`] crate
# and don't need to be preserved in the same way as the attributes in this enum.
# For more details on attribute parsing, see the [`rustc_attr_parsing`] crate.
# [`rustc_parse`]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_parse/index.html
# [`rustc_codegen_ssa`]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_codegen_ssa/index.html
# [`rustc_attr_parsing`]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_attr_parsing/index.html
RustcAttributeKind: TypeAlias = "Union[RustcAttributeKindAutomaticallyDerived, RustcAttributeKindCold, RustcAttributeKindDeprecated, RustcAttributeKindFundamental, RustcAttributeKindIgnore, RustcAttributeKindInline, RustcAttributeKindMayDangle, RustcAttributeKindNaked, RustcAttributeKindNoLink, RustcAttributeKindNoMangle, RustcAttributeKindNonExhaustive, RustcAttributeKindOptimize, RustcAttributeKindRustcAlign, RustcAttributeKindRustcIntrinsic, RustcAttributeKindRustcTestEntrypointMarker, RustcAttributeKindShouldPanic, RustcAttributeKindTargetFeature, RustcAttributeKindTrackCaller]"


@dataclass
class BinopBitXor:
    pass

@dataclass
class BinopBitAnd:
    pass

@dataclass
class BinopBitOr:
    pass

@dataclass
class BinopEq:
    pass

@dataclass
class BinopLt:
    pass

@dataclass
class BinopLe:
    pass

@dataclass
class BinopNe:
    pass

@dataclass
class BinopGe:
    pass

@dataclass
class BinopGt:
    pass

@dataclass
class BinopAdd:
    _0: OverflowMode

@dataclass
class BinopSub:
    _0: OverflowMode

@dataclass
class BinopMul:
    _0: OverflowMode

@dataclass
class BinopDiv:
    _0: OverflowMode

@dataclass
class BinopRem:
    _0: OverflowMode

@dataclass
class BinopAddChecked:
    r"""Returns `(result, did_overflow)`, where `result` is the result of the operation with
    wrapping semantics, and `did_overflow` is a boolean that indicates whether the operation
    overflowed. This operation does not fail."""

@dataclass
class BinopSubChecked:
    r"""Like `AddChecked`."""

@dataclass
class BinopMulChecked:
    r"""Like `AddChecked`."""

@dataclass
class BinopShl:
    r"""Fails if the shift is bigger than the bit-size of the type."""
    _0: OverflowMode

@dataclass
class BinopShr:
    r"""Fails if the shift is bigger than the bit-size of the type."""
    _0: OverflowMode

@dataclass
class BinopOffset:
    r"""`BinOp(Offset, ptr, n)` for `ptr` a pointer to type `T` offsets `ptr` by `n * size_of::<T>()`."""

@dataclass
class BinopCmp:
    r"""`BinOp(Cmp, a, b)` returns `-1u8` if `a < b`, `0u8` if `a == b`, and `1u8` if `a > b`."""

# Binary operations.
Binop: TypeAlias = "Union[BinopBitXor, BinopBitAnd, BinopBitOr, BinopEq, BinopLt, BinopLe, BinopNe, BinopGe, BinopGt, BinopAdd, BinopSub, BinopMul, BinopDiv, BinopRem, BinopAddChecked, BinopSubChecked, BinopMulChecked, BinopShl, BinopShr, BinopOffset, BinopCmp]"


@dataclass
class Binder(Generic[T0]):
    r"""A value of type `T` bound by generic parameters. Used in any context where we're adding generic
    parameters that aren't on the top-level item, e.g. `for<'a>` clauses (uses `RegionBinder` for
    now), trait methods, GATs (TODO)."""
    binder_params: GenericParams
    binder_value: T0
    r"""Named this way to highlight accesses to the inner value that might be handling parameters
    incorrectly. Prefer using helper methods."""


@dataclass
class BinderKindBKTraitType:
    r"""The parameters of a generic associated type."""
    _0: TraitDeclId
    _1: AssocTypeId

@dataclass
class BinderKindBKTraitMethod:
    r"""The parameters of a trait method. Used in the `methods` lists in trait decls and trait
    impls."""
    _0: TraitDeclId
    _1: TraitMethodId

@dataclass
class BinderKindBKInherentImplBlock:
    r"""The parameters bound in a non-trait `impl` block. Used in the `Name`s of inherent methods."""

@dataclass
class BinderKindBKDyn:
    r"""Binder used for `dyn Trait` existential predicates."""

@dataclass
class BinderKindBKOther:
    r"""Some other use of a binder outside the main Charon ast."""

BinderKind: TypeAlias = "Union[BinderKindBKTraitType, BinderKindBKTraitMethod, BinderKindBKInherentImplBlock, BinderKindBKDyn, BinderKindBKOther]"


@dataclass
class LlbcBlock:
    r"""A sequence of statements."""
    span: Span
    block_id: LlbcBlockId
    r"""Integer uniquely identifying this block. To simplify things we generate globally-fresh ids
    when creating a new `Block`."""
    statements: list[LlbcStatement]


@dataclass
class UllbcBlock:
    r"""A "basic block", which contains a linear sequence of statements, followed by a terminator, which
    is where non-linear control-flow happens."""
    statements: list[UllbcStatement]
    terminator: Terminator


UllbcBlockId = NewType("UllbcBlockId", int)


LlbcBlockId = NewType("LlbcBlockId", int)


@dataclass
class BodyUnstructuredBody:
    r"""Body represented as a CFG. This is what ullbc is made of, and what we get after translating MIR."""
    _0: GexprBody[list[UllbcBlock]]

@dataclass
class BodyStructuredBody:
    r"""Body represented with structured control flow. This is what llbc is made of. We restructure
    the control flow in the `ullbc_to_llbc` pass."""
    _0: GexprBody[LlbcBlock]

@dataclass
class BodyTargetDispatchBody:
    r"""A façade body that dispatches to one of several per-target function bodies. Created during
    multi-target merging for functions with the same signature but different bodies across
    targets."""
    _0: list[tuple[str, FunDeclRef]]

@dataclass
class BodyExternBody:
    r"""Function declared in an `extern { ... }` block. The string is the foreign symbol name."""
    _0: str

@dataclass
class BodyIntrinsicBody:
    r"""Rust intrinsic function."""
    name: str
    r"""The intrinsic name."""
    arg_names: list[Optional[str]]
    r"""The argument names, None if not available."""

@dataclass
class BodyOpaqueBody:
    r"""A body that the user chose not to translate, based on opacity settings like
    `--include`/`--opaque`."""

@dataclass
class BodyMissingBody:
    r"""A body that was not available. Typically that's function bodies for non-generic and
    non-inlineable std functions, as these are not present in the compiled standard library
    `.rmeta` file shipped with a rust toolchain."""

@dataclass
class BodyErrorBody:
    r"""We encountered an error while translating this body."""
    _0: Error

# The body of a function.
Body: TypeAlias = "Union[BodyUnstructuredBody, BodyStructuredBody, BodyTargetDispatchBody, BodyExternBody, BodyIntrinsicBody, BodyOpaqueBody, BodyMissingBody, BodyErrorBody]"


@dataclass
class BorrowKindBShared:
    pass

@dataclass
class BorrowKindBMut:
    pass

@dataclass
class BorrowKindBTwoPhaseMut:
    r"""See <https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.MutBorrowKind.html#variant.TwoPhaseBorrow>
    and <https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html>"""

@dataclass
class BorrowKindBShallow:
    r"""Those are typically introduced when using guards in matches, to make sure guards don't
    change the variant of an enum value while me match over it.

    See <https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.FakeBorrowKind.html#variant.Shallow>."""

@dataclass
class BorrowKindBUniqueImmutable:
    r"""Data must be immutable but not aliasable. In other words you can't mutate the data but you
    can mutate *through it*, e.g. if it points to a `&mut T`. This is only used in closure
    captures, e.g.
    ```rust,ignore
    let mut z = 3;
    let x: &mut isize = &mut z;
    let y = || *x += 5;
    ```
    Here the captured variable can't be `&mut &mut x` since the `x` binding is not mutable, yet
    we must be able to mutate what it points to.

    See <https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.MutBorrowKind.html#variant.ClosureCapture>."""

BorrowKind: TypeAlias = "Union[BorrowKindBShared, BorrowKindBMut, BorrowKindBTwoPhaseMut, BorrowKindBShallow, BorrowKindBUniqueImmutable]"


@dataclass
class BorrowckStatementFakeRead:
    r"""Acts like a read of the place."""
    _0: Place

@dataclass
class BorrowckStatementSetType:
    r"""Relate the type of a place to the provided type. For example, `let x: Self = value`
    produces `SetType` for `x` and `Self`."""
    place: Place
    ty: Ty
    variance: Variance

@dataclass
class BorrowckStatementSetOutlives:
    r"""Require a type to outlive a region. For example, the `'a` bound in
    `let x: impl Copy + 'a = value` produces `SetOutlives(typeof(x), 'a)`."""
    _0: Ty
    _1: Region

@dataclass
class BorrowckStatementPredicateHolds:
    r"""Require a trait predicate to hold. For example, the `Copy` bound in
    `let x: impl Copy = value` produces `PredicateHolds(typeof(x): Copy)`."""
    _0: TraitRef

# Statements that only affect borrow-checking. They are no-ops at runtime.
BorrowckStatement: TypeAlias = "Union[BorrowckStatementFakeRead, BorrowckStatementSetType, BorrowckStatementSetOutlives, BorrowckStatementPredicateHolds]"


BranchId = NewType("BranchId", int)


@dataclass
class BuiltinAdtTTuple:
    r"""A tuple `(A, B, ...)`, including `unit`."""

@dataclass
class BuiltinAdtTBox:
    r"""Boxes; always detected, though they are only treated as primitives with `--treat-box-as-builtin`"""

@dataclass
class BuiltinAdtTStr:
    r"""The `str` type, which corresponds to a `[u8]` that encodes a string with UTF-8."""

# Builtin ADT identifiers.
BuiltinAdt: TypeAlias = "Union[BuiltinAdtTTuple, BuiltinAdtTBox, BuiltinAdtTStr]"


@dataclass
class BuiltinAssertKindBoundsCheck:
    len: Operand
    index: Operand

@dataclass
class BuiltinAssertKindOverflow:
    _0: Binop
    _1: Operand
    _2: Operand

@dataclass
class BuiltinAssertKindOverflowNeg:
    _0: Operand

@dataclass
class BuiltinAssertKindDivisionByZero:
    _0: Operand

@dataclass
class BuiltinAssertKindRemainderByZero:
    _0: Operand

@dataclass
class BuiltinAssertKindMisalignedPointerDereference:
    required: Operand
    found: Operand

@dataclass
class BuiltinAssertKindNullPointerDereference:
    pass

@dataclass
class BuiltinAssertKindNullReferenceCreated:
    pass

@dataclass
class BuiltinAssertKindInvalidEnumConstruction:
    _0: Operand

@dataclass
class BuiltinAssertKindResumedAfterReturn:
    pass

@dataclass
class BuiltinAssertKindResumedAfterPanic:
    pass

@dataclass
class BuiltinAssertKindResumedAfterDrop:
    pass

# The kind of a built-in assertion, which may panic and unwind. These are removed
# by `reconstruct_fallible_operations` because they're implicit in the semantics of (U)LLBC.
# This kind should only be used for error-reporting purposes, as the check itself
# is performed in the instructions preceding the assert.
BuiltinAssertKind: TypeAlias = "Union[BuiltinAssertKindBoundsCheck, BuiltinAssertKindOverflow, BuiltinAssertKindOverflowNeg, BuiltinAssertKindDivisionByZero, BuiltinAssertKindRemainderByZero, BuiltinAssertKindMisalignedPointerDereference, BuiltinAssertKindNullPointerDereference, BuiltinAssertKindNullReferenceCreated, BuiltinAssertKindInvalidEnumConstruction, BuiltinAssertKindResumedAfterReturn, BuiltinAssertKindResumedAfterPanic, BuiltinAssertKindResumedAfterDrop]"


@dataclass
class BuiltinImplDataBuiltinAuto:
    r"""Auto traits (defined with `auto trait ...`, also `Unpin`)."""

@dataclass
class BuiltinImplDataBuiltinSized:
    pass

@dataclass
class BuiltinImplDataBuiltinMetaSized:
    pass

@dataclass
class BuiltinImplDataBuiltinPointeeSized:
    pass

@dataclass
class BuiltinImplDataBuiltinCopy:
    pass

@dataclass
class BuiltinImplDataBuiltinClone:
    pass

@dataclass
class BuiltinImplDataBuiltinTuple:
    pass

@dataclass
class BuiltinImplDataBuiltinTransmute:
    pass

@dataclass
class BuiltinImplDataBuiltinUnsize:
    pass

@dataclass
class BuiltinImplDataBuiltinPointee:
    pass

@dataclass
class BuiltinImplDataBuiltinDiscriminantKind:
    pass

@dataclass
class BuiltinImplDataBuiltinFn:
    pass

@dataclass
class BuiltinImplDataBuiltinFnMut:
    pass

@dataclass
class BuiltinImplDataBuiltinFnOnce:
    pass

@dataclass
class BuiltinImplDataBuiltinFnPtr:
    pass

@dataclass
class BuiltinImplDataBuiltinAsyncFn:
    pass

@dataclass
class BuiltinImplDataBuiltinAsyncFnMut:
    pass

@dataclass
class BuiltinImplDataBuiltinAsyncFnOnce:
    pass

@dataclass
class BuiltinImplDataBuiltinCoroutine:
    pass

@dataclass
class BuiltinImplDataBuiltinFuture:
    pass

@dataclass
class BuiltinImplDataBuiltinTryAsDynCompatible:
    r"""Auto-trait used for `try_as_dyn` (see https://github.com/rust-lang/rust/issues/144361)"""

@dataclass
class BuiltinImplDataBuiltinNoopDestruct:
    r"""An impl of `Destruct` for a type with no drop glue."""

@dataclass
class BuiltinImplDataBuiltinUntrackedDestruct:
    r"""An impl of `Destruct` for a type parameter, which we could not resolve because
    `--add-drop-bounds` was not set."""

@dataclass
class BuiltinImplDataBuiltinRemovedAdtClause:
    r"""Placeholder used by the `--remove-adt-clauses` pass when it strips a trait clause from a
    type declaration. References to the removed clause are rewritten as
    `BuiltinOrAuto { builtin_data: RemovedAdtClause, .. }`."""

# Describes a built-in impl. Mostly lists the implemented trait, sometimes with more details
# about the contents of the implementation.
BuiltinImplData: TypeAlias = "Union[BuiltinImplDataBuiltinAuto, BuiltinImplDataBuiltinSized, BuiltinImplDataBuiltinMetaSized, BuiltinImplDataBuiltinPointeeSized, BuiltinImplDataBuiltinCopy, BuiltinImplDataBuiltinClone, BuiltinImplDataBuiltinTuple, BuiltinImplDataBuiltinTransmute, BuiltinImplDataBuiltinUnsize, BuiltinImplDataBuiltinPointee, BuiltinImplDataBuiltinDiscriminantKind, BuiltinImplDataBuiltinFn, BuiltinImplDataBuiltinFnMut, BuiltinImplDataBuiltinFnOnce, BuiltinImplDataBuiltinFnPtr, BuiltinImplDataBuiltinAsyncFn, BuiltinImplDataBuiltinAsyncFnMut, BuiltinImplDataBuiltinAsyncFnOnce, BuiltinImplDataBuiltinCoroutine, BuiltinImplDataBuiltinFuture, BuiltinImplDataBuiltinTryAsDynCompatible, BuiltinImplDataBuiltinNoopDestruct, BuiltinImplDataBuiltinUntrackedDestruct, BuiltinImplDataBuiltinRemovedAdtClause]"


@dataclass
class BuiltinPathElemPeTuple:
    r"""The tuple of the given arity."""
    _0: int

@dataclass
class BuiltinPathElemPeStr:
    r"""`str`, which is a struct containing a `[u8]` the standard library expects
    to be valid UTF-8."""

@dataclass
class BuiltinPathElemPeClosure:
    r"""A closure."""

@dataclass
class BuiltinPathElemPeUse:
    r"""A `use` declaration."""

@dataclass
class BuiltinPathElemPeAnonConst:
    r"""An anonymous constant."""

@dataclass
class BuiltinPathElemPePromotedConst:
    r"""A constant that rustc promoted out of a body."""

@dataclass
class BuiltinPathElemPeClosureAsFn:
    r"""The function item we generate for a closure that is cast to a function pointer."""

@dataclass
class BuiltinPathElemPeDropGlue:
    r"""The method we add to the `Destruct` trait to hold the drop glue."""

@dataclass
class BuiltinPathElemPeVTable:
    r"""The vtable struct of a trait, or the vtable global of a trait impl."""

@dataclass
class BuiltinPathElemPeVTableMethod:
    r"""The version of a method that is stored in a vtable."""

@dataclass
class BuiltinPathElemPeVTableDropShim:
    r"""The `drop_in_place` shim stored in a vtable."""

# Used for builtin items, rather than hardcoding these as strings.
BuiltinPathElem: TypeAlias = "Union[BuiltinPathElemPeTuple, BuiltinPathElemPeStr, BuiltinPathElemPeClosure, BuiltinPathElemPeUse, BuiltinPathElemPeAnonConst, BuiltinPathElemPePromotedConst, BuiltinPathElemPeClosureAsFn, BuiltinPathElemPeDropGlue, BuiltinPathElemPeVTable, BuiltinPathElemPeVTableMethod, BuiltinPathElemPeVTableDropShim]"


@dataclass
class ByteUninit:
    r"""An uninitialized byte"""

@dataclass
class ByteValue:
    r"""A concrete byte value"""
    _0: int

@dataclass
class ByteProvenance:
    r"""A byte that is part of a pointer with provenance. The u8 is the offset within the
    pointer. Note that we do not have an actual value for this pointer byte, unlike
    MiniRust, as that is non-deterministic."""
    _0: Provenance
    _1: int

# A byte, in the MiniRust sense: it can either be uninitialized, a concrete u8 value,
# or part of a pointer with provenance (e.g. to a global or a function)
Byte: TypeAlias = "Union[ByteUninit, ByteValue, ByteProvenance]"


@dataclass
class Call:
    func: FnOperand
    args: list[Operand]
    dest: Place


@dataclass
class CastKindCastScalar:
    r"""Conversion between types in `{Integer, Bool}`
    Remark: for now we don't support conversions with Char."""
    _0: ScalarType
    _1: ScalarType

@dataclass
class CastKindCastRawPtr:
    _0: Ty
    _1: Ty

@dataclass
class CastKindCastFnPtr:
    _0: Ty
    _1: Ty

@dataclass
class CastKindCastUnsize:
    r"""[Unsize coercion](https://doc.rust-lang.org/std/ops/trait.CoerceUnsized.html). This is
    either `[T; N]` -> `[T]` or `T: Trait` -> `dyn Trait` coercions, behind a pointer
    (reference, `Box`, or other type that implements `CoerceUnsized`).

    The special case of `&[T; N]` -> `&[T]` coercion is caught by `UnOp::ArrayToSlice`."""
    _0: Ty
    _1: Ty
    _2: UnsizingMetadata

@dataclass
class CastKindCastTransmute:
    r"""Reinterprets the bits of a value of one type as another type, i.e. exactly what
    [`std::mem::transmute`] does."""
    _0: Ty
    _1: Ty

@dataclass
class CastKindCastConcretize:
    r"""Converts a receiver type with `dyn Trait<...>` to a concrete type `T`, used in vtable method shims.
    Valid conversions are references, raw pointers, and (optionally) boxes:
    - `&[mut] dyn Trait<...>` -> `&[mut] T`
    - `*[mut] dyn Trait<...>` -> `*[mut] T`
    - `Box<dyn Trait<...>>` -> `Box<T>` when no `--raw-boxes`

    For possible receivers, see: <https://doc.rust-lang.org/reference/items/traits.html#dyn-compatibility>.
    Other receivers, e.g., `Rc` should be unpacked before the cast and re-boxed after.
    FIXME(ssyram): but this is not implemented yet, namely, there may still be
        something like `Rc<dyn Trait<...>> -> Rc<T>` in the types."""
    _0: Ty
    _1: Ty

# For all the variants: the first type gives the source type, the second one gives
# the destination type.
CastKind: TypeAlias = "Union[CastKindCastScalar, CastKindCastRawPtr, CastKindCastFnPtr, CastKindCastUnsize, CastKindCastTransmute, CastKindCastConcretize]"


@dataclass
class CliOptions:
    ullbc: bool
    r"""Extract the unstructured LLBC (i.e., don't reconstruct the control-flow)"""
    precise_drops: bool
    r"""Whether to precisely translate drops and drop-related code. For this, we add explicit
    `Destruct` bounds to all generic parameters and set the MIR level to at least `elaborated`.

    Without this option, drops may be "conditional" and we may lack information about what code
    is run on drop in a given polymorphic function body."""
    mir: Optional[MirLevel]
    r"""The MIR stage to extract. This is only relevant for the current crate; for dependencies only
    MIR optimized is available."""
    rustc_args: list[str]
    r"""Extra flags to pass to rustc."""
    targets: list[str]
    r"""A list of target architectures to translate for. Charon will run the compiler once for each
    target and aggregate the results, which is useful if the code includes `#[cfg(..)]`
    filters.
    Warning: this is an initial implementation which is extremely slow."""
    sysroot: Optional[str]
    r"""Sysroot to use for rustc invocations. By default Charon builds a sysroot that has full MIR
    for the standard library. You can pass a custom sysroot to use instead, or pass "default"
    to use the normal distributed sysroot, which lacks MIR bodies for many standard library
    functions."""
    monomorphize: bool
    r"""Monomorphize the items encountered when possible. Generic items found in the crate are
    skipped. To only translate a particular call graph, use `--start-from`. Note: this doesn't
    currently support `dyn Trait`."""
    monomorphize_mut: Optional[MonomorphizeMut]
    r"""Partially monomorphize items to make it so that no item is ever monomorphized with a
    mutable reference (or type containing one); said differently, so that the presence of
    mutable references in a type is independent of its generics. This is used by Aeneas."""
    start_from: list[str]
    r"""A list of item paths to use as starting points for the translation. We will translate these
    items and any items they refer to, according to the opacity rules. When absent, we start
    from the path `crate` (which translates the whole crate)."""
    start_from_if_exists: list[str]
    r"""Same as --start-from, but won't raise an error if a pattern doesn't match any item. This is useful
    when the patterns are generated by a build script and may be out of sync with the code."""
    start_from_attribute: list[str]
    r"""Use all the items annotated with the given attribute(s) as starting points for translation
    (except modules).
    If an attribute name is not specified, `verify::start_from` is used."""
    start_from_pub: bool
    r"""Use all the `pub` items as starting points for translation (except modules)."""
    included: list[str]
    r"""Whitelist of items to translate. These use the name-matcher syntax."""
    opaque: list[str]
    r"""Blacklist of items to keep opaque. Works just like `--include`, see the doc there."""
    exclude: list[str]
    r"""Blacklist of items to not translate at all. Works just like `--include`, see the doc there."""
    extract_opaque_bodies: bool
    r"""Usually we skip the bodies of foreign methods and structs with private fields. When this
    flag is on, we don't."""
    translate_all_methods: bool
    r"""Usually we skip the provided methods that aren't used. When this flag is on, we translate
    them all."""
    duplicate_defaulted_methods: bool
    r"""Whenever an impl doesn't implement a method (because it has a default body), this creates a
    duplicate method as if it had been implemented. This can simplify the call-graphs as
    otherwise calls within the default body would be indirected through trait proofs."""
    lift_associated_types: list[str]
    r"""Transform the associate types of traits to be type parameters instead. This takes a list
    of name patterns of the traits to transform, using the same syntax as `--include`."""
    hide_marker_traits: bool
    r"""Whether to hide various marker traits such as `Sized`, `Sync`, and `Send`
    anywhere they show up. This can considerably speed up translation."""
    hide_allocator: bool
    r"""Hide the `A` type parameter on standard library containers (`Box`, `Vec`, etc)."""
    remove_unused_clauses: bool
    r"""Remove trait clauses that aren't ultimately used anywhere. This is potentially incorrect as
    sometimes the mere presence of a trait clause is used to justify an operation, e.g. copying
    `Copy` data using `unsafe`."""
    remove_unused_self_clauses: bool
    r"""Trait method default bodies take a `Self: Trait` clause as parameter, so that they can be
    reused by multiple trait impls. This however causes trait definitions to be mutually
    recursive with their default methods. This flag removes `Self` clauses that aren't used to
    break this mutual recursion when possible."""
    remove_adt_clauses: bool
    r"""Remove trait clauses from type declarations. Best combined with `--lift-associated-types`
    for type declarations that use trait associated types in their fields."""
    desugar_drops: bool
    r"""Transform precise drops to the equivalent `drop_glue(&mut p)` call."""
    ops_to_function_calls: bool
    r"""Transform array-to-slice unsizing and repeat expressions into standard library function
    calls in LLBC."""
    index_to_function_calls: bool
    r"""Transform array/slice indexing into standard library function calls in LLBC. Note that this may
    introduce UB since it creates references that were not normally created, including when
    indexing behind a raw pointer."""
    treat_box_as_builtin: bool
    r"""Treat `Box<T>` as if it was a built-in type."""
    no_gen_tuple_structs: bool
    r"""Don't generate a type declaration per tuple arity. Instead, every tuple type refers to the
    single opaque declaration with id `TypeDeclId::UNIT`, and stores its field types in its
    generic arguments. This is meant for consumers that build tuples of arbitrary arity on the
    fly and don't care about their declaration. Note that this makes tuple types ill-typed with
    respect to their declaration; it is also incompatible with `--monomorphize`."""
    raw_consts: bool
    r"""Do not inline or evaluate constants."""
    consts: Optional[ConstHandling]
    r"""How to handle constants and statics: whether they should be represented as a call to their
    initializer function, or whether we should attempt to evaluate them into a value. When
    evaluation isn't possible (e.g. the constant is generic, or for recursive statics), we fall
    back to the initializer call."""
    unsized_strings: bool
    r"""Replace string literal constants with a constant u8 array that gets unsized,
    expliciting the fact a string constant has a hidden reference."""
    reconstruct_fallible_operations: bool
    r"""Replace "bound checks followed by UB-on-overflow operation" with the corresponding
    panic-on-overflow operation. This loses unwinding information."""
    reconstruct_asserts: bool
    r"""Replace `if x { panic() }` with `assert(x)`."""
    reconstruct_matches: bool
    r"""Recombine a `read_discriminant(place)` followed by a `switch` into a single operation that
    uses enum variants instead of their discriminants."""
    deallocate_all_locals: bool
    r"""Ensure all local deallocations are made explicit with `StorageDead` statements. If this flag is not passed,
    every non-return local is implicitly deallocated on function return.
    Note this can add a lot of statements (quadratically-many, because of unwind paths)."""
    unbind_item_vars: bool
    r"""Use `DeBruijnVar::Free` for the variables bound in item signatures, instead of
    `DeBruijnVar::Bound` everywhere. This simplifies the management of generics for projects
    that don't intend to manipulate them too much."""
    print_original_ullbc: bool
    r"""Pretty-print the ULLBC immediately after extraction from MIR."""
    print_ullbc: bool
    r"""Pretty-print the ULLBC after applying the micro-passes (before serialization/control-flow reconstruction)."""
    print_built_llbc: bool
    r"""Pretty-print the LLBC just after we built it (i.e., immediately after loop reconstruction)."""
    print_llbc: bool
    r"""Pretty-print the final LLBC (after all the cleaning micro-passes)."""
    dest_dir: Optional[str]
    r"""The destination directory. Files will be generated as
    `<dest_dir>/<crate_name>.{u}llbc` for json and `<dest_dir>/<crate_name>.{u}llbc.postcard`
    for postcard, unless `dest_file` is set. `dest_dir` defaults to the current directory."""
    dest_file: Optional[str]
    r"""The destination file. By default this depends on `format` and `ullbc`. If this is set we
    ignore `dest_dir`. If used with `format=all`, will add an extension corresponding to the file format
    at the end of the provided file name."""
    no_dedup_serialized_ast: bool
    r"""Don't deduplicate values (types, trait refs) in the .(u)llbc file. This makes the file easier to inspect."""
    format: Optional[SerializationFormatArg]
    r"""Serialization format for emitted (U)LLBC files. Defaults to json."""
    no_serialize: bool
    r"""Don't serialize the final (U)LLBC to a file."""
    skip_borrowck: bool
    r"""If activated, this skips borrow-checking of the crate."""
    no_typecheck: bool
    r"""Skip the typecheck passes."""
    no_normalize: bool
    r"""Don't normalize associated types."""
    no_reorder_decls: bool
    r"""Don't compute a stable order for declarations."""
    abort_on_error: bool
    r"""Panic on the first error. This is useful for debugging."""
    error_on_warnings: bool
    r"""Consider any warnings to be errors."""
    preset: Optional[Preset]
    r"""Named builtin sets of options."""


@dataclass
class ClosureInfo:
    r"""Additional information for closures."""
    kind: ClosureKind
    fn_once_impl: RegionBinder[TraitImplRef]
    r"""The `FnOnce` implementation of this closure -- always exists."""
    fn_mut_impl: Optional[RegionBinder[TraitImplRef]]
    r"""The `FnMut` implementation of this closure, if any."""
    fn_impl: Optional[RegionBinder[TraitImplRef]]
    r"""The `Fn` implementation of this closure, if any."""
    signature: RegionBinder[FunSig]
    r"""The signature of the function that this closure represents."""


@dataclass
class ClosureKindFn:
    pass

@dataclass
class ClosureKindFnMut:
    pass

@dataclass
class ClosureKindFnOnce:
    pass

ClosureKind: TypeAlias = "Union[ClosureKindFn, ClosureKindFnMut, ClosureKindFnOnce]"


@dataclass
class ConstGenericParam:
    r"""A const generic variable in a signature or binder."""
    index: ConstGenericVarId
    r"""Index identifying the variable among other variables bound at the same level."""
    name: str
    r"""Const generic name"""
    ty: Ty
    r"""Type of the const generic"""


ConstGenericVarId = NewType("ConstGenericVarId", int)


@dataclass
class ConstHandlingInitializers:
    r"""Keep consts as calls to their initializer with `ConstantExprKind::Call`, without attempting
    to do any const-evaluation. This is the default."""

@dataclass
class ConstHandlingValues:
    r"""Try evaluating consts and statics to their final value. If evaluation fails, we fall back to the
    initializer call."""

# How to handle constants and statics.
ConstHandling: TypeAlias = "Union[ConstHandlingInitializers, ConstHandlingValues]"


@dataclass
class ConstantExpr:
    kind: ConstantExprKind
    ty: Ty


@dataclass
class ConstantExprKindCBool:
    r"""Boolean value."""
    _0: bool

@dataclass
class ConstantExprKindCInteger:
    r"""Integer value."""
    _0: IntegerValue

@dataclass
class ConstantExprKindCChar:
    r"""Char value."""
    _0: str

@dataclass
class ConstantExprKindCFloat:
    r"""Float value."""
    _0: FloatValue

@dataclass
class ConstantExprKindCAdt:
    r"""Value of an ADT (struct or enum).

    This is eliminated inside functions if `--raw-consts` is off."""
    _0: Optional[VariantId]
    _1: list[ConstantExpr]

@dataclass
class ConstantExprKindCArray:
    r"""Array value.

    This is eliminated inside functions if `--raw-consts` is off."""
    _0: list[ConstantExpr]

@dataclass
class ConstantExprKindCRef:
    r"""A shared reference to a constant value.

    This is eliminated inside functions if `--raw-consts` is off."""
    _0: ConstantExpr
    _1: Optional[UnsizingMetadata]

@dataclass
class ConstantExprKindCPtr:
    r"""A pointer to a static.

    This is eliminated inside functions if `--raw-consts` is off."""
    _0: RefKind
    _1: ConstantExpr
    _2: Optional[UnsizingMetadata]

@dataclass
class ConstantExprKindCStr:
    r"""`str` value."""
    _0: str

@dataclass
class ConstantExprKindCByteStr:
    r"""Byte string value."""
    _0: list[int]

@dataclass
class ConstantExprKindCFnDef:
    r"""ZST constant corresponding to the unique value of the type of a function item."""
    _0: FnPtr

@dataclass
class ConstantExprKindCFnPtr:
    r"""A function pointer value; this is a pointer (i.e. an address).

    This is eliminated inside functions if `--raw-consts` is off."""
    _0: FnPtr

@dataclass
class ConstantExprKindCPtrNoProvenance:
    r"""A pointer with no provenance (e.g. 0 for the null pointer)

    This is eliminated inside functions if `--raw-consts` is off."""
    _0: int

@dataclass
class ConstantExprKindCTypeId:
    r"""The `TypeId` value for a type."""
    _0: Ty

@dataclass
class ConstantExprKindCRawMemory:
    r"""Raw memory value obtained from constant evaluation. Used when a more structured
    representation isn't possible (e.g. for unions) or just isn't implemented yet."""
    _0: list[Byte]

@dataclass
class ConstantExprKindCVar:
    r"""A const generic var"""
    _0: DeBruijnVar[ConstGenericVarId]

@dataclass
class ConstantExprKindCGlobal:
    r"""The value of a constant/static.

    This is eliminated inside functions if `--raw-consts` is off."""
    _0: GlobalDeclRef

@dataclass
class ConstantExprKindCCall:
    r"""A call to a `const fn`."""
    _0: FnPtr
    _1: list[ConstantExpr]

@dataclass
class ConstantExprKindCTraitConst:
    r"""A trait associated constant.

    E.g.:
    ```text
    impl Foo for Bar {
      const C : usize = 32; // <-
    }
    ```"""
    _0: TraitRef
    _1: AssocConstId

@dataclass
class ConstantExprKindCVTableRef:
    r"""A reference to the vtable `static` item for this trait ref. This can be normalized if we
    emitted a vtable item.

    This is eliminated if `--raw-consts` is off."""
    _0: TraitRef

@dataclass
class ConstantExprKindCDiscriminant:
    r"""The integer discriminant value corresponding to this enum variant."""
    _0: TypeDeclRef
    _1: VariantId

@dataclass
class ConstantExprKindCSizeOf:
    r"""The size of the given type."""
    _0: Ty

@dataclass
class ConstantExprKindCAlignOf:
    r"""The alignment of the given type."""
    _0: Ty

@dataclass
class ConstantExprKindCOpaque:
    r"""A constant expression that Charon doesn't handle, along with the reason why."""
    _0: str

ConstantExprKind: TypeAlias = "Union[ConstantExprKindCBool, ConstantExprKindCInteger, ConstantExprKindCChar, ConstantExprKindCFloat, ConstantExprKindCAdt, ConstantExprKindCArray, ConstantExprKindCRef, ConstantExprKindCPtr, ConstantExprKindCStr, ConstantExprKindCByteStr, ConstantExprKindCFnDef, ConstantExprKindCFnPtr, ConstantExprKindCPtrNoProvenance, ConstantExprKindCTypeId, ConstantExprKindCRawMemory, ConstantExprKindCVar, ConstantExprKindCGlobal, ConstantExprKindCCall, ConstantExprKindCTraitConst, ConstantExprKindCVTableRef, ConstantExprKindCDiscriminant, ConstantExprKindCSizeOf, ConstantExprKindCAlignOf, ConstantExprKindCOpaque]"


# The index of a binder, counting from the innermost. See [`DeBruijnVar`] for details.
DeBruijnId: TypeAlias = "int"


@dataclass
class DeBruijnVarBound(Generic[T0]):
    r"""A variable attached to the nth binder, counting from the innermost."""
    _0: DeBruijnId
    _1: T0

@dataclass
class DeBruijnVarFree(Generic[T0]):
    r"""A variable attached to the outermost binder (the one on the item). This is not used within
    Charon itself, instead ewe insert it at the end if `--unbind-item-vars` is set."""
    _0: T0

# Type-level variable.
# Variables are bound in groups. Each item has a top-level binding group in its `generic_params`
# field, and then inner binders are possible using the `RegionBinder<T>` and `Binder<T>` types.
# Each variable is linked to exactly one binder. The `Id` then identifies the specific variable
# among all those bound in that group.
# For instance, we have the following:
# ```text
# fn f<'a, 'b>(x: for<'c> fn(&'b u8, &'c u16, for<'d> fn(&'b u32, &'c u64, &'d u128)) -> u64) {}
# ^^^^^^         ^^       ^       ^          ^^       ^        ^        ^
# |       inner binder  |       |     inner binder  |        |        |
# top-level binder            |       |                   |        |        |
# Bound(1, b)   |              Bound(2, b)   |     Bound(0, d)
# |                            |
# Bound(0, c)                 Bound(1, c)
# ```
# To make consumption easier for projects that don't do heavy substitution, `--unbind-item-vars`
# changes the variables bound at the top-level (i.e. in the `GenericParams` of items) to be
# `Free`. The example above becomes:
# ```text
# fn f<'a, 'b>(x: for<'c> fn(&'b u8, &'c u16, for<'d> fn(&'b u32, &'c u64, &'d u128)) -> u64) {}
# ^^^^^^         ^^       ^       ^          ^^       ^        ^        ^
# |       inner binder  |       |     inner binder  |        |        |
# top-level binder            |       |                   |        |        |
# Free(b)    |                Free(b)     |     Bound(0, d)
# |                            |
# Bound(0, c)                 Bound(1, c)
# ```
DeBruijnVar: TypeAlias = "Union[DeBruijnVarBound[T0], DeBruijnVarFree[T0]]"


@dataclass
class DeclarationGroupTypeGroup:
    r"""A type declaration group"""
    _0: GDeclarationGroup[TypeDeclId]

@dataclass
class DeclarationGroupFunGroup:
    r"""A function declaration group"""
    _0: GDeclarationGroup[FunDeclId]

@dataclass
class DeclarationGroupGlobalGroup:
    r"""A global declaration group"""
    _0: GDeclarationGroup[GlobalDeclId]

@dataclass
class DeclarationGroupTraitDeclGroup:
    _0: GDeclarationGroup[TraitDeclId]

@dataclass
class DeclarationGroupTraitImplGroup:
    _0: GDeclarationGroup[TraitImplId]

@dataclass
class DeclarationGroupMixedGroup:
    r"""Anything that doesn't fit into these categories."""
    _0: GDeclarationGroup[ItemId]

# A (group of) top-level declaration(s), properly reordered.
DeclarationGroup: TypeAlias = "Union[DeclarationGroupTypeGroup, DeclarationGroupFunGroup, DeclarationGroupGlobalGroup, DeclarationGroupTraitDeclGroup, DeclarationGroupTraitImplGroup, DeclarationGroupMixedGroup]"


@dataclass
class RustcDeprecatedSinceRustcVersion:
    _0: RustcRustcVersion

@dataclass
class RustcDeprecatedSinceFuture:
    r"""Deprecated in the future ("to be determined")."""

@dataclass
class RustcDeprecatedSinceNonStandard:
    r"""`feature(staged_api)` is off. Deprecation versions outside the standard
    library are allowed to be arbitrary strings, for better or worse."""
    _0: str

@dataclass
class RustcDeprecatedSinceUnspecified:
    r"""Deprecation version is unspecified but optional."""

@dataclass
class RustcDeprecatedSinceErr:
    r"""Failed to parse a deprecation version, or the deprecation version is
    unspecified and required. An error has already been emitted."""

# Release in which an API is deprecated.
RustcDeprecatedSince: TypeAlias = "Union[RustcDeprecatedSinceRustcVersion, RustcDeprecatedSinceFuture, RustcDeprecatedSinceNonStandard, RustcDeprecatedSinceUnspecified, RustcDeprecatedSinceErr]"


@dataclass
class RustcDeprecation:
    since: RustcDeprecatedSince
    note: Optional[RustcIdent]
    r"""The note to issue a reason."""
    suggestion: Optional[str]
    r"""A text snippet used to completely replace any use of the deprecated item in an expression.

    This is currently unstable."""


Disambiguator = NewType("Disambiguator", int)


@dataclass
class DiscriminatorKnown:
    r"""The variant is known."""
    _0: VariantId

@dataclass
class DiscriminatorInvalid:
    r"""No valid variant (e.g., invalid tag value)."""

@dataclass
class DiscriminatorBranch:
    r"""Branch on an integer value read from memory at `offset`."""
    offset: OffsetExpr
    r"""Byte offset to read from."""
    int_ty: IntegerType
    r"""Integer type to read."""
    children: list[tuple[tuple[IntegerValue, IntegerValue], Discriminator]]
    r"""If the integer is in one of these ranges, continue with the given `Discriminator`. The
    ranges are sorted."""
    fallback: Discriminator
    r"""Fallback if no range in `children` matches."""

# Decision tree used to determine the active variant by reading memory. Mirrors MiniRust's
# `Discriminator`.
Discriminator: TypeAlias = "Union[DiscriminatorKnown, DiscriminatorInvalid, DiscriminatorBranch]"


@dataclass
class DropKindPrecise:
    r"""A real drop. This calls `<T as Destruct>::drop_glue(&mut place)` and marks the
    place as moved-out-of. Use `--desugar-drops` to transform all such drops to an actual
    function call.

    The `drop_glue` method is added by Charon to the `Destruct` trait to make it possible
    to track drop code in polymorphic code. It contains the same code as the
    `core::ptr::drop_glue<T>` builtin would.

    Drop are precise in MIR `elaborated` and `optimized`."""

@dataclass
class DropKindConditional:
    r"""A conditional drop, which may or may not end up running drop code depending on the code
    path that led to it. A conditional drop may also become a partial drop (dropping only the
    subplaces that haven't been moved out of), may be conditional on the code path that led to
    it, or become an async drop. The exact semantics are left intentionally unspecified by
    rustc developers. To elaborate such drops into precise drops, pass `--precise-drops` to
    Charon.

    A conditional drop may also be passed an unaligned place when dropping fields of packed
    structs. Such a thing is UB for a precise drop.

    Drop are conditional in MIR `built` and `promoted`."""

# A `Drop` statement/terminator can mean two things, depending on what MIR phase we retrieved
# from rustc: it could be a real drop, or it could be a "conditional drop", which is where drop
# may happen depending on whether the borrow-checker determines a drop is needed.
DropKind: TypeAlias = "Union[DropKindPrecise, DropKindConditional]"


@dataclass
class DynPredicate:
    r"""The contents of a `dyn Trait` type."""
    binder: Binder[Ty]
    r"""This binder binds a single type `T`, which is considered existentially quantified. The
    predicates in the binder apply to `T` and represent the `dyn Trait` constraints.
    E.g. `dyn Iterator<Item=u32> + Send` is represented as `exists<T: Iterator<Item=u32> + Send> T`.

    Only the first trait clause may have methods. We use the vtable of this trait in the `dyn
    Trait` pointer metadata."""


@dataclass
class Error:
    r"""Common error used during the translation."""
    span: Span
    msg: str


# An expression that represents a size in bytes.
ExactSizeExpr: TypeAlias = "ExactSizeExprKind"


@dataclass
class ExactSizeExprKindExactSizeExprConstant:
    r"""An arbitrary constant of type `usize`."""
    _0: ConstantExpr

@dataclass
class ExactSizeExprKindExactSizeExprFromMetadata:
    r"""Layout information stored in the pointer metadata to this object."""
    _0: MetadataValue

@dataclass
class ExactSizeExprKindExactSizeExprMax:
    _0: list[ExactSizeExpr]

@dataclass
class ExactSizeExprKindExactSizeExprMin:
    _0: list[ExactSizeExpr]

@dataclass
class ExactSizeExprKindExactSizeExprPlus:
    _0: ExactSizeExpr
    _1: ExactSizeExpr

@dataclass
class ExactSizeExprKindExactSizeExprScale:
    _0: ExactSizeExpr
    _1: ConstantExpr

@dataclass
class ExactSizeExprKindExactSizeExprAlignTo:
    r"""The next multiple of `target_align` from `base`."""
    base: ExactSizeExpr
    target_align: ExactSizeExpr

@dataclass
class ExactSizeExprKindExactSizeExprIfInhabited:
    r"""A size expression that depens on whether the given type is inhabited."""
    ty: Ty
    then_size: ExactSizeExpr
    else_size: ExactSizeExpr

ExactSizeExprKind: TypeAlias = "Union[ExactSizeExprKindExactSizeExprConstant, ExactSizeExprKindExactSizeExprFromMetadata, ExactSizeExprKindExactSizeExprMax, ExactSizeExprKindExactSizeExprMin, ExactSizeExprKindExactSizeExprPlus, ExactSizeExprKindExactSizeExprScale, ExactSizeExprKindExactSizeExprAlignTo, ExactSizeExprKindExactSizeExprIfInhabited]"


@dataclass
class Field:
    span: Span
    attr_info: AttrInfo
    field_name: str
    is_positional: bool
    r"""Whether this field is positional, as in a tuple struct, tuple variant, or closure. If so,
    its name is based on its position, such as `_0`; otherwise, it is a user-provided name."""
    field_ty: Ty


FieldId = NewType("FieldId", int)


@dataclass
class File:
    name: FileName
    r"""The path to the file."""
    crate_name: str
    r"""Name of the crate this file comes from."""
    contents: Optional[str]
    r"""The contents of the source file, as seen by rustc at the time of translation.
    Some files don't have contents."""


FileId: TypeAlias = "File"


@dataclass
class FileNameVirtual:
    r"""A remapped path (namely paths into stdlib)"""
    _0: str

@dataclass
class FileNameLocal:
    r"""A local path (a file coming from the current crate for instance)"""
    _0: str

@dataclass
class FileNameNotReal:
    r"""A "not real" file name (macro, query, etc.)"""
    _0: str

# A filename.
FileName: TypeAlias = "Union[FileNameVirtual, FileNameLocal, FileNameNotReal]"


@dataclass
class FloatTypeF16:
    pass

@dataclass
class FloatTypeF32:
    pass

@dataclass
class FloatTypeF64:
    pass

@dataclass
class FloatTypeF128:
    pass

FloatType: TypeAlias = "Union[FloatTypeF16, FloatTypeF32, FloatTypeF64, FloatTypeF128]"


@dataclass
class FloatValue:
    r"""This is simlar to the Scalar value above. However, instead of storing
    the float value itself, we store its String representation. This allows
    to derive the Eq and Ord traits, which are not implemented for floats"""
    float_value: str
    float_ty: FloatType


@dataclass
class FnOperandFnOpRegular:
    r"""Regular case: call to a top-level function, trait method, etc."""
    _0: FnPtr

@dataclass
class FnOperandFnOpDynamic:
    r"""Use of a function pointer."""
    _0: Operand

# A function operand is used in function calls.
# It either designates a top-level function, or a place in case
# we are using function pointers stored in local variables.
FnOperand: TypeAlias = "Union[FnOperandFnOpRegular, FnOperandFnOpDynamic]"


@dataclass
class FnPtr:
    r"""Reference to a function, possibly indirected via a trait."""
    kind: FnPtrKind
    generics: GenericArgs


@dataclass
class FnPtrKindFun:
    _0: FunDeclId

@dataclass
class FnPtrKindTraitMethod:
    r"""If a trait: the reference to the trait and the id of the trait method."""
    _0: TraitRef
    _1: TraitMethodId

FnPtrKind: TypeAlias = "Union[FnPtrKindFun, FnPtrKindTraitMethod]"


@dataclass
class FunDecl:
    r"""A function definition"""
    def_id: FunDeclId
    item_meta: ItemMeta
    r"""The meta data associated with the declaration."""
    generics: GenericParams
    signature: FunSig
    r"""The signature contains the inputs/output types and ABI details."""
    src: FunSource
    r"""The function kind: "regular" function, trait method declaration, etc."""
    body: Body
    r"""The function body."""


FunDeclId = NewType("FunDeclId", int)


@dataclass
class FunDeclRef:
    r"""Reference to a function declaration."""
    id: FunDeclId
    generics: GenericArgs
    r"""Generic arguments passed to the function."""


@dataclass
class FunSig:
    r"""A function signature."""
    is_unsafe: bool
    r"""Is the function unsafe or not"""
    abi: Abi
    r"""The calling convention of this function."""
    is_variadic: bool
    r"""Whether this is a C-variadic function (its last parameter is `...`)."""
    inputs: list[Ty]
    output: Ty


@dataclass
class FunSourceNormalFun:
    r"""A normal function."""

@dataclass
class FunSourceAdtConstructorFun:
    r"""A synthetic function representing an ADT constructor."""

@dataclass
class FunSourceTraitDefaultFun:
    r"""A default method in a trait declaration."""
    trait_ref: TraitDeclRef
    r"""The trait declaration this item belongs to."""
    item_id: TraitMethodId
    r"""The method this corresponds to."""

@dataclass
class FunSourceTraitImplFun:
    r"""A method in a trait implementation."""
    impl_ref: TraitImplRef
    r"""The trait implementation the method belongs to."""
    trait_ref: TraitDeclRef
    r"""The trait declaration that the impl block implements."""
    item_id: TraitMethodId
    r"""The method this corresponds to."""
    reuses_default: bool
    r"""True if the trait decl had a default implementation for this method and this item is a
    copy of the default item."""

@dataclass
class FunSourceVTableShimFun:
    r"""Wraps a concrete implementation of a method into a function that takes `dyn Trait` as its
    `Self` type. This shim casts the receiver to the known concrete type and calls the real
    method."""

@dataclass
class FunSourceGlobalInitializerFun:
    r"""The initializer for a global."""
    _0: GlobalDeclRef

@dataclass
class FunSourceTargetDependentFun:
    r"""A target-specific variant behind a `TargetDispatch` façade. The dispatcher is the function
    with the `Body::TargetDispatch` body that dispatches to this function."""
    dispatcher: FunDeclRef

# Where a given function came from.
FunSource: TypeAlias = "Union[FunSourceNormalFun, FunSourceAdtConstructorFun, FunSourceTraitDefaultFun, FunSourceTraitImplFun, FunSourceVTableShimFun, FunSourceGlobalInitializerFun, FunSourceTargetDependentFun]"


@dataclass
class GDeclarationGroupNonRecGroup(Generic[T0]):
    r"""A non-recursive declaration"""
    _0: T0

@dataclass
class GDeclarationGroupRecGroup(Generic[T0]):
    r"""A (group of mutually) recursive declaration(s)"""
    _0: list[T0]

# A (group of) top-level declaration(s), properly reordered.
# "G" stands for "generic"
GDeclarationGroup: TypeAlias = "Union[GDeclarationGroupNonRecGroup[T0], GDeclarationGroupRecGroup[T0]]"


@dataclass
class GexprBody(Generic[T0]):
    r"""An expression body.
    TODO: arg_count should be stored in GFunDecl below. But then,
          the print is obfuscated and Aeneas may need some refactoring."""
    span: Span
    bound_body_regions: int
    r"""The number of regions existentially bound in this body. We introduce fresh such regions
    during translation instead of the erased regions that rustc gives us."""
    locals: Locals
    r"""The local variables."""
    body: T0
    r"""The statements and blocks that compose this body."""


@dataclass
class GenericArgs:
    r"""A set of generic arguments."""
    regions: list[Region]
    types: list[Ty]
    const_generics: list[ConstantExpr]
    trait_refs: list[TraitRef]


@dataclass
class GenericParams:
    r"""Generic parameters for a declaration, including predicates."""
    regions: list[RegionParam]
    types: list[TypeParam]
    const_generics: list[ConstGenericParam]
    trait_clauses: list[TraitParam]
    regions_outlive: list[RegionBinder[OutlivesPred[Region, Region]]]
    r"""The first region in the pair outlives the second region"""
    types_outlive: list[RegionBinder[OutlivesPred[Ty, Region]]]
    r"""The type outlives the region"""
    trait_type_constraints: list[RegionBinder[TraitTypeConstraint]]
    r"""Constraints over trait associated types"""


@dataclass
class GlobalDecl:
    r"""A global variable definition (constant or static)."""
    def_id: GlobalDeclId
    item_meta: ItemMeta
    r"""The meta data associated with the declaration."""
    generics: GenericParams
    r"""Remark: constants can actually have generic parameters.
    ```text
    struct V<const N: usize, T> {
        x: [T; N],
    }

    impl<const N: usize, T> V<N, T> {
        const LEN: usize = N; // This has generics <N, T>
    }

    fn use_v<const N: usize, T>(v: V<N, T>) {
        let l = V::<N, T>::LEN; // We need to provided a substitution here
    }
    ```"""
    ty: Ty
    src: GlobalSource
    r"""The context of the global: distinguishes normal items from trait-associated items and
    vtable instances."""
    global_kind: GlobalKind
    r"""The kind of global (static or const)."""
    value: ConstantExpr
    r"""The value of this constant/static. By default this is a [`ConstantExprKind::Call`] to the
    initializer function that computes the value (the function uses the same generic parameters
    as the global)."""


GlobalDeclId = NewType("GlobalDeclId", int)


@dataclass
class GlobalDeclRef:
    r"""Reference to a global declaration."""
    id: GlobalDeclId
    generics: GenericArgs


@dataclass
class GlobalKindStatic:
    r"""A static."""

@dataclass
class GlobalKindThreadLocal:
    r"""A thread-local static."""

@dataclass
class GlobalKindNamedConst:
    r"""A const with a name (either top-level or an associated const in a trait)."""

@dataclass
class GlobalKindAnonConst:
    r"""A const without a name:
    - An inline const expression (`const { 1 + 1 }`);
    - A const expression in a type (`[u8; sizeof::<T>()]`);
    - A promoted constant, automatically lifted from a body (`&0`)."""

GlobalKind: TypeAlias = "Union[GlobalKindStatic, GlobalKindThreadLocal, GlobalKindNamedConst, GlobalKindAnonConst]"


@dataclass
class GlobalSourceNormalGlobal:
    r"""A normal global."""

@dataclass
class GlobalSourceTraitDefaultGlobal:
    r"""A default assoc const in a trait declaration."""
    trait_ref: TraitDeclRef
    r"""The trait declaration the const belongs to."""
    item_id: AssocConstId
    r"""The associated const this corresponds to."""

@dataclass
class GlobalSourceTraitImplGlobal:
    r"""An associated const in a trait implementation."""
    impl_ref: TraitImplRef
    r"""The trait implementation the const belongs to."""
    trait_ref: TraitDeclRef
    r"""The trait declaration that the impl block implements."""
    item_id: AssocConstId
    r"""The associated const this corresponds to."""
    reuses_default: bool
    r"""True if the trait decl had a default value for this const and this item is a copy of
    the default item."""

@dataclass
class GlobalSourceVTableInstanceGlobal:
    r"""Defines the vtable for a trait impl."""
    impl_ref: Optional[TraitImplRef]
    r"""The originating impl. This is `None` in monomorphized mode: the vtable global itself
    identifies the concrete instantiation, so we don't translate an impl reference solely
    to record its provenance."""

# Where a given global came from.
GlobalSource: TypeAlias = "Union[GlobalSourceNormalGlobal, GlobalSourceTraitDefaultGlobal, GlobalSourceTraitImplGlobal, GlobalSourceVTableInstanceGlobal]"


# `HashConsed` is transparent on the python side; it has no declaration of its own.


@dataclass
class RustcIdent:
    name: str
    r"""`name` should never be the empty symbol. If you are considering that,
    you are probably conflating "empty identifier with "no identifier" and
    you should use `Option<Ident>` instead.
    Trying to construct an `Ident` with an empty name will trigger debug assertions."""
    span: Span


@dataclass
class ImplElemTy:
    _0: Binder[Ty]

@dataclass
class ImplElemTrait:
    _0: TraitImplId

# There are two kinds of `impl` blocks:
# - impl blocks linked to a type ("inherent" impl blocks following Rust terminology):
# ```text
# impl<T> List<T> { ...}
# ```
# - trait impl blocks:
# ```text
# impl<T> PartialEq for List<T> { ...}
# ```
# We distinguish the two.
ImplElem: TypeAlias = "Union[ImplElemTy, ImplElemTrait]"


@dataclass
class InlineAttrHint:
    r"""`#[inline]`"""

@dataclass
class InlineAttrNever:
    r"""`#[inline(never)]`"""

@dataclass
class InlineAttrAlways:
    r"""`#[inline(always)]`"""

# `#[inline]` built-in attribute.
InlineAttr: TypeAlias = "Union[InlineAttrHint, InlineAttrNever, InlineAttrAlways]"


@dataclass
class RustcInlineAttrNone:
    pass

@dataclass
class RustcInlineAttrHint:
    pass

@dataclass
class RustcInlineAttrAlways:
    pass

@dataclass
class RustcInlineAttrNever:
    pass

@dataclass
class RustcInlineAttrForce:
    r"""`#[rustc_force_inline]` forces inlining to happen in the MIR inliner - it reports an error
    if the inlining cannot happen. It is limited to only free functions so that the calls
    can always be resolved."""
    attr_span: Span
    reason: Optional[str]

RustcInlineAttr: TypeAlias = "Union[RustcInlineAttrNone, RustcInlineAttrHint, RustcInlineAttrAlways, RustcInlineAttrNever, RustcInlineAttrForce]"


@dataclass
class IntTyIsize:
    pass

@dataclass
class IntTyI8:
    pass

@dataclass
class IntTyI16:
    pass

@dataclass
class IntTyI32:
    pass

@dataclass
class IntTyI64:
    pass

@dataclass
class IntTyI128:
    pass

IntTy: TypeAlias = "Union[IntTyIsize, IntTyI8, IntTyI16, IntTyI32, IntTyI64, IntTyI128]"


@dataclass
class IntegerTypeSigned:
    _0: IntTy

@dataclass
class IntegerTypeUnsigned:
    _0: UIntTy

IntegerType: TypeAlias = "Union[IntegerTypeSigned, IntegerTypeUnsigned]"


@dataclass
class IntegerValueUnsignedInteger:
    _0: UIntTy
    _1: int

@dataclass
class IntegerValueSignedInteger:
    _0: IntTy
    _1: int

# A scalar value.
IntegerValue: TypeAlias = "Union[IntegerValueUnsignedInteger, IntegerValueSignedInteger]"


@dataclass
class ItemIdIdType:
    _0: TypeDeclId

@dataclass
class ItemIdIdTraitDecl:
    _0: TraitDeclId

@dataclass
class ItemIdIdTraitImpl:
    _0: TraitImplId

@dataclass
class ItemIdIdFun:
    _0: FunDeclId

@dataclass
class ItemIdIdGlobal:
    _0: GlobalDeclId

# The id of a translated item.
ItemId: TypeAlias = "Union[ItemIdIdType, ItemIdIdTraitDecl, ItemIdIdTraitImpl, ItemIdIdFun, ItemIdIdGlobal]"


@dataclass
class ItemMeta:
    r"""Meta information about an item (function, trait decl, trait impl, type decl, global)."""
    name: Name
    span: Span
    source_text: Optional[str]
    r"""The source code that corresponds to this item."""
    attr_info: AttrInfo
    r"""Attributes and visibility."""
    is_local: bool
    r"""`true` if the type decl is a local type decl, `false` if it comes from an external crate."""
    opacity: ItemOpacity
    r"""Whether this item is considered opaque. For function and globals, this means we don't
    translate the body (the code); for ADTs, this means we don't translate the fields/variants.
    For traits and trait impls, this doesn't change anything. For modules, this means we don't
    explore its contents (we still translate any of its items mentioned from somewhere else).

    This can happen either if the item was annotated with `#[charon::opaque]` or if it was
    declared opaque via a command-line argument."""
    lang_item: Optional[RustcLangItem]
    r"""If the item is a rustc lang item, record which one it is."""
    diagnostic_item: Optional[str]
    r"""If the item is a rustc diagnostic item, record its internal identifier."""


@dataclass
class ItemOpacityTransparent:
    r"""Translate the item fully."""

@dataclass
class ItemOpacityForeign:
    r"""Translate the item depending on the normal rust visibility of its contents: for types, we
    translate fully if it is a struct with public fields or an enum; for other items this is
    equivalent to `Opaque`."""

@dataclass
class ItemOpacityItemOpaque:
    r"""Translate the item name and signature, but not its contents. For function and globals, this
    means we don't translate the body (the code); for ADTs, this means we don't translate the
    fields/variants. For traits and trait impls, this doesn't change anything. For modules,
    this means we don't explore its contents (we still translate any of its items mentioned
    from somewhere else).

    This can happen either if the item was annotated with `#[charon::opaque]` or if it was
    declared opaque via a command-line argument."""

@dataclass
class ItemOpacityInvisible:
    r"""Translate nothing of this item. The corresponding map will not have an entry for the
    `ItemId`. Useful when even the signature of the item causes errors."""

# How much to translate for a given item.
ItemOpacity: TypeAlias = "Union[ItemOpacityTransparent, ItemOpacityForeign, ItemOpacityItemOpaque, ItemOpacityInvisible]"


@dataclass
class RustcLangItemSized:
    r"""The `sized` lang item."""

@dataclass
class RustcLangItemMetaSized:
    r"""The `meta_sized` lang item."""

@dataclass
class RustcLangItemPointeeSized:
    r"""The `pointee_sized` lang item."""

@dataclass
class RustcLangItemUnsize:
    r"""The `unsize` lang item."""

@dataclass
class RustcLangItemAlignOf:
    r"""The `mem_align_const` lang item."""

@dataclass
class RustcLangItemSizeOf:
    r"""The `mem_size_const` lang item."""

@dataclass
class RustcLangItemOffsetOf:
    r"""The `offset_of` lang item."""

@dataclass
class RustcLangItemStructuralPeq:
    r"""The `structural_peq` lang item.
    Trait injected by `#[derive(PartialEq)]`, (i.e. "Partial EQ")."""

@dataclass
class RustcLangItemCopy:
    r"""The `copy` lang item."""

@dataclass
class RustcLangItemClone:
    r"""The `clone` lang item."""

@dataclass
class RustcLangItemCloneFn:
    r"""The `clone_fn` lang item."""

@dataclass
class RustcLangItemUseCloned:
    r"""The `use_cloned` lang item."""

@dataclass
class RustcLangItemTrivialClone:
    r"""The `trivial_clone` lang item."""

@dataclass
class RustcLangItemSync:
    r"""The `sync` lang item."""

@dataclass
class RustcLangItemDiscriminantKind:
    r"""The `discriminant_kind` lang item."""

@dataclass
class RustcLangItemDiscriminant:
    r"""The `discriminant_type` lang item.
    The associated item of the `DiscriminantKind` trait."""

@dataclass
class RustcLangItemPointeeTrait:
    r"""The `pointee_trait` lang item."""

@dataclass
class RustcLangItemMetadata:
    r"""The `metadata_type` lang item."""

@dataclass
class RustcLangItemDynMetadata:
    r"""The `dyn_metadata` lang item."""

@dataclass
class RustcLangItemFreeze:
    r"""The `freeze` lang item."""

@dataclass
class RustcLangItemUnsafeUnpin:
    r"""The `unsafe_unpin` lang item."""

@dataclass
class RustcLangItemFnPtrTrait:
    r"""The `fn_ptr_trait` lang item."""

@dataclass
class RustcLangItemFnPtrAddr:
    r"""The `fn_ptr_addr` lang item."""

@dataclass
class RustcLangItemDrop:
    r"""The `drop` lang item."""

@dataclass
class RustcLangItemDestruct:
    r"""The `destruct` lang item."""

@dataclass
class RustcLangItemAsyncDrop:
    r"""The `async_drop` lang item."""

@dataclass
class RustcLangItemAsyncDropInPlace:
    r"""The `async_drop_in_place` lang item."""

@dataclass
class RustcLangItemCoerceUnsized:
    r"""The `coerce_unsized` lang item."""

@dataclass
class RustcLangItemDispatchFromDyn:
    r"""The `dispatch_from_dyn` lang item."""

@dataclass
class RustcLangItemTryAsDyn:
    r"""The `try_as_dyn` lang item."""

@dataclass
class RustcLangItemTransmuteOpts:
    r"""The `transmute_opts` lang item."""

@dataclass
class RustcLangItemTransmuteTrait:
    r"""The `transmute_trait` lang item."""

@dataclass
class RustcLangItemAdd:
    r"""The `add` lang item."""

@dataclass
class RustcLangItemSub:
    r"""The `sub` lang item."""

@dataclass
class RustcLangItemMul:
    r"""The `mul` lang item."""

@dataclass
class RustcLangItemDiv:
    r"""The `div` lang item."""

@dataclass
class RustcLangItemRem:
    r"""The `rem` lang item."""

@dataclass
class RustcLangItemNeg:
    r"""The `neg` lang item."""

@dataclass
class RustcLangItemNot:
    r"""The `not` lang item."""

@dataclass
class RustcLangItemBitXor:
    r"""The `bitxor` lang item."""

@dataclass
class RustcLangItemBitAnd:
    r"""The `bitand` lang item."""

@dataclass
class RustcLangItemBitOr:
    r"""The `bitor` lang item."""

@dataclass
class RustcLangItemShl:
    r"""The `shl` lang item."""

@dataclass
class RustcLangItemShr:
    r"""The `shr` lang item."""

@dataclass
class RustcLangItemAddAssign:
    r"""The `add_assign` lang item."""

@dataclass
class RustcLangItemSubAssign:
    r"""The `sub_assign` lang item."""

@dataclass
class RustcLangItemMulAssign:
    r"""The `mul_assign` lang item."""

@dataclass
class RustcLangItemDivAssign:
    r"""The `div_assign` lang item."""

@dataclass
class RustcLangItemRemAssign:
    r"""The `rem_assign` lang item."""

@dataclass
class RustcLangItemBitXorAssign:
    r"""The `bitxor_assign` lang item."""

@dataclass
class RustcLangItemBitAndAssign:
    r"""The `bitand_assign` lang item."""

@dataclass
class RustcLangItemBitOrAssign:
    r"""The `bitor_assign` lang item."""

@dataclass
class RustcLangItemShlAssign:
    r"""The `shl_assign` lang item."""

@dataclass
class RustcLangItemShrAssign:
    r"""The `shr_assign` lang item."""

@dataclass
class RustcLangItemIndex:
    r"""The `index` lang item."""

@dataclass
class RustcLangItemIndexMut:
    r"""The `index_mut` lang item."""

@dataclass
class RustcLangItemUnsafeCell:
    r"""The `unsafe_cell` lang item."""

@dataclass
class RustcLangItemCovariantUnsafeCell:
    r"""The `covariant_unsafe_cell` lang item."""

@dataclass
class RustcLangItemUnsafePinned:
    r"""The `unsafe_pinned` lang item."""

@dataclass
class RustcLangItemVaArgSafe:
    r"""The `va_arg_safe` lang item."""

@dataclass
class RustcLangItemVaList:
    r"""The `va_list` lang item."""

@dataclass
class RustcLangItemComplex:
    r"""The `complex` lang item."""

@dataclass
class RustcLangItemDeref:
    r"""The `deref` lang item."""

@dataclass
class RustcLangItemDerefMut:
    r"""The `deref_mut` lang item."""

@dataclass
class RustcLangItemDerefPure:
    r"""The `deref_pure` lang item."""

@dataclass
class RustcLangItemDerefTarget:
    r"""The `deref_target` lang item."""

@dataclass
class RustcLangItemReceiver:
    r"""The `receiver` lang item."""

@dataclass
class RustcLangItemReceiverTarget:
    r"""The `receiver_target` lang item."""

@dataclass
class RustcLangItemLegacyReceiver:
    r"""The `legacy_receiver` lang item."""

@dataclass
class RustcLangItemFn:
    r"""The `Fn` lang item."""

@dataclass
class RustcLangItemFnMut:
    r"""The `fn_mut` lang item."""

@dataclass
class RustcLangItemFnOnce:
    r"""The `fn_once` lang item."""

@dataclass
class RustcLangItemAsyncFn:
    r"""The `async_fn` lang item."""

@dataclass
class RustcLangItemAsyncFnMut:
    r"""The `async_fn_mut` lang item."""

@dataclass
class RustcLangItemAsyncFnOnce:
    r"""The `async_fn_once` lang item."""

@dataclass
class RustcLangItemAsyncFnOnceOutput:
    r"""The `async_fn_once_output` lang item."""

@dataclass
class RustcLangItemCallOnceFuture:
    r"""The `call_once_future` lang item."""

@dataclass
class RustcLangItemCallRefFuture:
    r"""The `call_ref_future` lang item."""

@dataclass
class RustcLangItemAsyncFnKindHelper:
    r"""The `async_fn_kind_helper` lang item."""

@dataclass
class RustcLangItemAsyncFnKindUpvars:
    r"""The `async_fn_kind_upvars` lang item."""

@dataclass
class RustcLangItemFnOnceOutput:
    r"""The `fn_once_output` lang item."""

@dataclass
class RustcLangItemIterator:
    r"""The `iterator` lang item."""

@dataclass
class RustcLangItemFusedIterator:
    r"""The `fused_iterator` lang item."""

@dataclass
class RustcLangItemFuture:
    r"""The `future_trait` lang item."""

@dataclass
class RustcLangItemFutureOutput:
    r"""The `future_output` lang item."""

@dataclass
class RustcLangItemAsyncIterator:
    r"""The `async_iterator` lang item."""

@dataclass
class RustcLangItemCoroutineState:
    r"""The `coroutine_state` lang item."""

@dataclass
class RustcLangItemCoroutine:
    r"""The `coroutine` lang item."""

@dataclass
class RustcLangItemCoroutineReturn:
    r"""The `coroutine_return` lang item."""

@dataclass
class RustcLangItemCoroutineYield:
    r"""The `coroutine_yield` lang item."""

@dataclass
class RustcLangItemCoroutineResume:
    r"""The `coroutine_resume` lang item."""

@dataclass
class RustcLangItemUnpin:
    r"""The `unpin` lang item."""

@dataclass
class RustcLangItemPin:
    r"""The `pin` lang item."""

@dataclass
class RustcLangItemOrderingEnum:
    r"""The `Ordering` lang item."""

@dataclass
class RustcLangItemPartialEq:
    r"""The `eq` lang item."""

@dataclass
class RustcLangItemPartialOrd:
    r"""The `partial_ord` lang item."""

@dataclass
class RustcLangItemCVoid:
    r"""The `c_void` lang item."""

@dataclass
class RustcLangItemType:
    r"""The `type_info` lang item."""

@dataclass
class RustcLangItemTypeGeneric:
    r"""The `type_info_generic` lang item."""

@dataclass
class RustcLangItemTypeId:
    r"""The `type_id` lang item."""

@dataclass
class RustcLangItemPanic:
    r"""The `panic` lang item."""

@dataclass
class RustcLangItemPanicNounwind:
    r"""The `panic_nounwind` lang item."""

@dataclass
class RustcLangItemPanicFmt:
    r"""The `panic_fmt` lang item."""

@dataclass
class RustcLangItemPanicDisplay:
    r"""The `panic_display` lang item."""

@dataclass
class RustcLangItemConstPanicFmt:
    r"""The `const_panic_fmt` lang item."""

@dataclass
class RustcLangItemPanicBoundsCheck:
    r"""The `panic_bounds_check` lang item."""

@dataclass
class RustcLangItemPanicMisalignedPointerDereference:
    r"""The `panic_misaligned_pointer_dereference` lang item."""

@dataclass
class RustcLangItemPanicInfo:
    r"""The `panic_info` lang item."""

@dataclass
class RustcLangItemPanicLocation:
    r"""The `panic_location` lang item."""

@dataclass
class RustcLangItemPanicImpl:
    r"""The `panic_impl` lang item."""

@dataclass
class RustcLangItemPanicCannotUnwind:
    r"""The `panic_cannot_unwind` lang item."""

@dataclass
class RustcLangItemPanicInCleanup:
    r"""The `panic_in_cleanup` lang item."""

@dataclass
class RustcLangItemPanicAddOverflow:
    r"""The `panic_const_add_overflow` lang item.
    Constant panic messages, used for codegen of MIR asserts."""

@dataclass
class RustcLangItemPanicSubOverflow:
    r"""The `panic_const_sub_overflow` lang item."""

@dataclass
class RustcLangItemPanicMulOverflow:
    r"""The `panic_const_mul_overflow` lang item."""

@dataclass
class RustcLangItemPanicDivOverflow:
    r"""The `panic_const_div_overflow` lang item."""

@dataclass
class RustcLangItemPanicRemOverflow:
    r"""The `panic_const_rem_overflow` lang item."""

@dataclass
class RustcLangItemPanicNegOverflow:
    r"""The `panic_const_neg_overflow` lang item."""

@dataclass
class RustcLangItemPanicShrOverflow:
    r"""The `panic_const_shr_overflow` lang item."""

@dataclass
class RustcLangItemPanicShlOverflow:
    r"""The `panic_const_shl_overflow` lang item."""

@dataclass
class RustcLangItemPanicDivZero:
    r"""The `panic_const_div_by_zero` lang item."""

@dataclass
class RustcLangItemPanicRemZero:
    r"""The `panic_const_rem_by_zero` lang item."""

@dataclass
class RustcLangItemPanicCoroutineResumed:
    r"""The `panic_const_coroutine_resumed` lang item."""

@dataclass
class RustcLangItemPanicAsyncFnResumed:
    r"""The `panic_const_async_fn_resumed` lang item."""

@dataclass
class RustcLangItemPanicAsyncGenFnResumed:
    r"""The `panic_const_async_gen_fn_resumed` lang item."""

@dataclass
class RustcLangItemPanicGenFnNone:
    r"""The `panic_const_gen_fn_none` lang item."""

@dataclass
class RustcLangItemPanicCoroutineResumedPanic:
    r"""The `panic_const_coroutine_resumed_panic` lang item."""

@dataclass
class RustcLangItemPanicAsyncFnResumedPanic:
    r"""The `panic_const_async_fn_resumed_panic` lang item."""

@dataclass
class RustcLangItemPanicAsyncGenFnResumedPanic:
    r"""The `panic_const_async_gen_fn_resumed_panic` lang item."""

@dataclass
class RustcLangItemPanicGenFnNonePanic:
    r"""The `panic_const_gen_fn_none_panic` lang item."""

@dataclass
class RustcLangItemPanicNullPointerDereference:
    r"""The `panic_null_pointer_dereference` lang item."""

@dataclass
class RustcLangItemPanicNullReferenceConstructed:
    r"""The `panic_null_reference_constructed` lang item."""

@dataclass
class RustcLangItemPanicInvalidEnumConstruction:
    r"""The `panic_invalid_enum_construction` lang item."""

@dataclass
class RustcLangItemPanicCoroutineResumedDrop:
    r"""The `panic_const_coroutine_resumed_drop` lang item."""

@dataclass
class RustcLangItemPanicAsyncFnResumedDrop:
    r"""The `panic_const_async_fn_resumed_drop` lang item."""

@dataclass
class RustcLangItemPanicAsyncGenFnResumedDrop:
    r"""The `panic_const_async_gen_fn_resumed_drop` lang item."""

@dataclass
class RustcLangItemPanicGenFnNoneDrop:
    r"""The `panic_const_gen_fn_none_drop` lang item."""

@dataclass
class RustcLangItemBeginPanic:
    r"""The `begin_panic` lang item.
    libstd panic entry point. Necessary for const eval to be able to catch it"""

@dataclass
class RustcLangItemFormatArgument:
    r"""The `format_argument` lang item."""

@dataclass
class RustcLangItemFormatArguments:
    r"""The `format_arguments` lang item."""

@dataclass
class RustcLangItemDropGlue:
    r"""The `drop_glue` lang item."""

@dataclass
class RustcLangItemAllocLayout:
    r"""The `alloc_layout` lang item."""

@dataclass
class RustcLangItemStart:
    r"""The `start` lang item.
    For all binary crates without `#![no_main]`, Rust will generate a "main" function.
    The exact name and signature are target-dependent. The "main" function will invoke
    this lang item, passing it the `argc` and `argv` (or null, if those don't exist
    on the current target) as well as the user-defined `fn main` from the binary crate."""

@dataclass
class RustcLangItemEhPersonality:
    r"""The `eh_personality` lang item."""

@dataclass
class RustcLangItemCompilerMove:
    r"""The `compiler_move` lang item."""

@dataclass
class RustcLangItemCompilerCopy:
    r"""The `compiler_copy` lang item."""

@dataclass
class RustcLangItemOwnedBox:
    r"""The `owned_box` lang item."""

@dataclass
class RustcLangItemGlobalAlloc:
    r"""The `global_alloc_ty` lang item."""

@dataclass
class RustcLangItemPhantomData:
    r"""The `phantom_data` lang item."""

@dataclass
class RustcLangItemManuallyDrop:
    r"""The `manually_drop` lang item."""

@dataclass
class RustcLangItemMaybeDangling:
    r"""The `maybe_dangling` lang item."""

@dataclass
class RustcLangItemBikeshedGuaranteedNoDrop:
    r"""The `bikeshed_guaranteed_no_drop` lang item."""

@dataclass
class RustcLangItemMaybeUninit:
    r"""The `maybe_uninit` lang item."""

@dataclass
class RustcLangItemTermination:
    r"""The `termination` lang item."""

@dataclass
class RustcLangItemTry:
    r"""The `Try` lang item."""

@dataclass
class RustcLangItemTuple:
    r"""The `tuple_trait` lang item."""

@dataclass
class RustcLangItemSliceLen:
    r"""The `slice_len_fn` lang item."""

@dataclass
class RustcLangItemTryTraitFromResidual:
    r"""The `from_residual` lang item."""

@dataclass
class RustcLangItemTryTraitFromOutput:
    r"""The `from_output` lang item."""

@dataclass
class RustcLangItemTryTraitBranch:
    r"""The `branch` lang item."""

@dataclass
class RustcLangItemTryTraitFromYeet:
    r"""The `from_yeet` lang item."""

@dataclass
class RustcLangItemResidualIntoTryType:
    r"""The `into_try_type` lang item."""

@dataclass
class RustcLangItemCoercePointeeValidated:
    r"""The `coerce_pointee_validated` lang item."""

@dataclass
class RustcLangItemConstParamTy:
    r"""The `const_param_ty` lang item."""

@dataclass
class RustcLangItemPoll:
    r"""The `Poll` lang item."""

@dataclass
class RustcLangItemPollReady:
    r"""The `Ready` lang item."""

@dataclass
class RustcLangItemPollPending:
    r"""The `Pending` lang item."""

@dataclass
class RustcLangItemAsyncGenReady:
    r"""The `AsyncGenReady` lang item."""

@dataclass
class RustcLangItemAsyncGenPending:
    r"""The `AsyncGenPending` lang item."""

@dataclass
class RustcLangItemAsyncGenFinished:
    r"""The `AsyncGenFinished` lang item."""

@dataclass
class RustcLangItemResumeTy:
    r"""The `ResumeTy` lang item."""

@dataclass
class RustcLangItemGetContext:
    r"""The `get_context` lang item."""

@dataclass
class RustcLangItemContext:
    r"""The `Context` lang item."""

@dataclass
class RustcLangItemFuturePoll:
    r"""The `poll` lang item."""

@dataclass
class RustcLangItemAsyncIteratorPollNext:
    r"""The `async_iterator_poll_next` lang item."""

@dataclass
class RustcLangItemIntoAsyncIterIntoIter:
    r"""The `into_async_iter_into_iter` lang item."""

@dataclass
class RustcLangItemOption:
    r"""The `Option` lang item."""

@dataclass
class RustcLangItemOptionSome:
    r"""The `Some` lang item."""

@dataclass
class RustcLangItemOptionNone:
    r"""The `None` lang item."""

@dataclass
class RustcLangItemResultOk:
    r"""The `Ok` lang item."""

@dataclass
class RustcLangItemResultErr:
    r"""The `Err` lang item."""

@dataclass
class RustcLangItemControlFlowContinue:
    r"""The `Continue` lang item."""

@dataclass
class RustcLangItemControlFlowBreak:
    r"""The `Break` lang item."""

@dataclass
class RustcLangItemIntoFutureIntoFuture:
    r"""The `into_future` lang item."""

@dataclass
class RustcLangItemIntoIterIntoIter:
    r"""The `into_iter` lang item."""

@dataclass
class RustcLangItemIteratorNext:
    r"""The `next` lang item."""

@dataclass
class RustcLangItemPinNewUnchecked:
    r"""The `new_unchecked` lang item."""

@dataclass
class RustcLangItemRangeFrom:
    r"""The `RangeFrom` lang item."""

@dataclass
class RustcLangItemRangeFull:
    r"""The `RangeFull` lang item."""

@dataclass
class RustcLangItemRangeInclusiveStruct:
    r"""The `RangeInclusive` lang item."""

@dataclass
class RustcLangItemRangeInclusiveNew:
    r"""The `range_inclusive_new` lang item."""

@dataclass
class RustcLangItemRange:
    r"""The `Range` lang item."""

@dataclass
class RustcLangItemRangeToInclusive:
    r"""The `RangeToInclusive` lang item."""

@dataclass
class RustcLangItemRangeTo:
    r"""The `RangeTo` lang item."""

@dataclass
class RustcLangItemRangeMax:
    r"""The `RangeMax` lang item."""

@dataclass
class RustcLangItemRangeMin:
    r"""The `RangeMin` lang item."""

@dataclass
class RustcLangItemRangeSub:
    r"""The `RangeSub` lang item."""

@dataclass
class RustcLangItemRangeFromCopy:
    r"""The `RangeFromCopy` lang item."""

@dataclass
class RustcLangItemRangeCopy:
    r"""The `RangeCopy` lang item."""

@dataclass
class RustcLangItemRangeInclusiveCopy:
    r"""The `RangeInclusiveCopy` lang item."""

@dataclass
class RustcLangItemRangeToInclusiveCopy:
    r"""The `RangeToInclusiveCopy` lang item."""

@dataclass
class RustcLangItemString:
    r"""The `String` lang item."""

@dataclass
class RustcLangItemCStr:
    r"""The `CStr` lang item."""

@dataclass
class RustcLangItemContractBuildCheckEnsures:
    r"""The `contract_build_check_ensures` lang item."""

@dataclass
class RustcLangItemContractCheckRequires:
    r"""The `contract_check_requires` lang item."""

@dataclass
class RustcLangItemDefaultTrait4:
    r"""The `default_trait4` lang item."""

@dataclass
class RustcLangItemDefaultTrait3:
    r"""The `default_trait3` lang item."""

@dataclass
class RustcLangItemDefaultTrait2:
    r"""The `default_trait2` lang item."""

@dataclass
class RustcLangItemDefaultTrait1:
    r"""The `default_trait1` lang item."""

@dataclass
class RustcLangItemContractCheckEnsures:
    r"""The `contract_check_ensures` lang item."""

@dataclass
class RustcLangItemReborrow:
    r"""The `reborrow` lang item."""

@dataclass
class RustcLangItemCoerceShared:
    r"""The `coerce_shared` lang item."""

@dataclass
class RustcLangItemFieldRepresentingType:
    r"""The `field_representing_type` lang item."""

@dataclass
class RustcLangItemField:
    r"""The `field` lang item."""

@dataclass
class RustcLangItemFieldBase:
    r"""The `field_base` lang item."""

@dataclass
class RustcLangItemFieldType:
    r"""The `field_type` lang item."""

@dataclass
class RustcLangItemFieldOffset:
    r"""The `field_offset` lang item."""

@dataclass
class RustcLangItemFrom:
    r"""The `From` lang item."""

@dataclass
class RustcLangItemFromFn:
    r"""The `from` lang item."""

# A representation of all the valid lang items in Rust.
RustcLangItem: TypeAlias = "Union[RustcLangItemSized, RustcLangItemMetaSized, RustcLangItemPointeeSized, RustcLangItemUnsize, RustcLangItemAlignOf, RustcLangItemSizeOf, RustcLangItemOffsetOf, RustcLangItemStructuralPeq, RustcLangItemCopy, RustcLangItemClone, RustcLangItemCloneFn, RustcLangItemUseCloned, RustcLangItemTrivialClone, RustcLangItemSync, RustcLangItemDiscriminantKind, RustcLangItemDiscriminant, RustcLangItemPointeeTrait, RustcLangItemMetadata, RustcLangItemDynMetadata, RustcLangItemFreeze, RustcLangItemUnsafeUnpin, RustcLangItemFnPtrTrait, RustcLangItemFnPtrAddr, RustcLangItemDrop, RustcLangItemDestruct, RustcLangItemAsyncDrop, RustcLangItemAsyncDropInPlace, RustcLangItemCoerceUnsized, RustcLangItemDispatchFromDyn, RustcLangItemTryAsDyn, RustcLangItemTransmuteOpts, RustcLangItemTransmuteTrait, RustcLangItemAdd, RustcLangItemSub, RustcLangItemMul, RustcLangItemDiv, RustcLangItemRem, RustcLangItemNeg, RustcLangItemNot, RustcLangItemBitXor, RustcLangItemBitAnd, RustcLangItemBitOr, RustcLangItemShl, RustcLangItemShr, RustcLangItemAddAssign, RustcLangItemSubAssign, RustcLangItemMulAssign, RustcLangItemDivAssign, RustcLangItemRemAssign, RustcLangItemBitXorAssign, RustcLangItemBitAndAssign, RustcLangItemBitOrAssign, RustcLangItemShlAssign, RustcLangItemShrAssign, RustcLangItemIndex, RustcLangItemIndexMut, RustcLangItemUnsafeCell, RustcLangItemCovariantUnsafeCell, RustcLangItemUnsafePinned, RustcLangItemVaArgSafe, RustcLangItemVaList, RustcLangItemComplex, RustcLangItemDeref, RustcLangItemDerefMut, RustcLangItemDerefPure, RustcLangItemDerefTarget, RustcLangItemReceiver, RustcLangItemReceiverTarget, RustcLangItemLegacyReceiver, RustcLangItemFn, RustcLangItemFnMut, RustcLangItemFnOnce, RustcLangItemAsyncFn, RustcLangItemAsyncFnMut, RustcLangItemAsyncFnOnce, RustcLangItemAsyncFnOnceOutput, RustcLangItemCallOnceFuture, RustcLangItemCallRefFuture, RustcLangItemAsyncFnKindHelper, RustcLangItemAsyncFnKindUpvars, RustcLangItemFnOnceOutput, RustcLangItemIterator, RustcLangItemFusedIterator, RustcLangItemFuture, RustcLangItemFutureOutput, RustcLangItemAsyncIterator, RustcLangItemCoroutineState, RustcLangItemCoroutine, RustcLangItemCoroutineReturn, RustcLangItemCoroutineYield, RustcLangItemCoroutineResume, RustcLangItemUnpin, RustcLangItemPin, RustcLangItemOrderingEnum, RustcLangItemPartialEq, RustcLangItemPartialOrd, RustcLangItemCVoid, RustcLangItemType, RustcLangItemTypeGeneric, RustcLangItemTypeId, RustcLangItemPanic, RustcLangItemPanicNounwind, RustcLangItemPanicFmt, RustcLangItemPanicDisplay, RustcLangItemConstPanicFmt, RustcLangItemPanicBoundsCheck, RustcLangItemPanicMisalignedPointerDereference, RustcLangItemPanicInfo, RustcLangItemPanicLocation, RustcLangItemPanicImpl, RustcLangItemPanicCannotUnwind, RustcLangItemPanicInCleanup, RustcLangItemPanicAddOverflow, RustcLangItemPanicSubOverflow, RustcLangItemPanicMulOverflow, RustcLangItemPanicDivOverflow, RustcLangItemPanicRemOverflow, RustcLangItemPanicNegOverflow, RustcLangItemPanicShrOverflow, RustcLangItemPanicShlOverflow, RustcLangItemPanicDivZero, RustcLangItemPanicRemZero, RustcLangItemPanicCoroutineResumed, RustcLangItemPanicAsyncFnResumed, RustcLangItemPanicAsyncGenFnResumed, RustcLangItemPanicGenFnNone, RustcLangItemPanicCoroutineResumedPanic, RustcLangItemPanicAsyncFnResumedPanic, RustcLangItemPanicAsyncGenFnResumedPanic, RustcLangItemPanicGenFnNonePanic, RustcLangItemPanicNullPointerDereference, RustcLangItemPanicNullReferenceConstructed, RustcLangItemPanicInvalidEnumConstruction, RustcLangItemPanicCoroutineResumedDrop, RustcLangItemPanicAsyncFnResumedDrop, RustcLangItemPanicAsyncGenFnResumedDrop, RustcLangItemPanicGenFnNoneDrop, RustcLangItemBeginPanic, RustcLangItemFormatArgument, RustcLangItemFormatArguments, RustcLangItemDropGlue, RustcLangItemAllocLayout, RustcLangItemStart, RustcLangItemEhPersonality, RustcLangItemCompilerMove, RustcLangItemCompilerCopy, RustcLangItemOwnedBox, RustcLangItemGlobalAlloc, RustcLangItemPhantomData, RustcLangItemManuallyDrop, RustcLangItemMaybeDangling, RustcLangItemBikeshedGuaranteedNoDrop, RustcLangItemMaybeUninit, RustcLangItemTermination, RustcLangItemTry, RustcLangItemTuple, RustcLangItemSliceLen, RustcLangItemTryTraitFromResidual, RustcLangItemTryTraitFromOutput, RustcLangItemTryTraitBranch, RustcLangItemTryTraitFromYeet, RustcLangItemResidualIntoTryType, RustcLangItemCoercePointeeValidated, RustcLangItemConstParamTy, RustcLangItemPoll, RustcLangItemPollReady, RustcLangItemPollPending, RustcLangItemAsyncGenReady, RustcLangItemAsyncGenPending, RustcLangItemAsyncGenFinished, RustcLangItemResumeTy, RustcLangItemGetContext, RustcLangItemContext, RustcLangItemFuturePoll, RustcLangItemAsyncIteratorPollNext, RustcLangItemIntoAsyncIterIntoIter, RustcLangItemOption, RustcLangItemOptionSome, RustcLangItemOptionNone, RustcLangItemResultOk, RustcLangItemResultErr, RustcLangItemControlFlowContinue, RustcLangItemControlFlowBreak, RustcLangItemIntoFutureIntoFuture, RustcLangItemIntoIterIntoIter, RustcLangItemIteratorNext, RustcLangItemPinNewUnchecked, RustcLangItemRangeFrom, RustcLangItemRangeFull, RustcLangItemRangeInclusiveStruct, RustcLangItemRangeInclusiveNew, RustcLangItemRange, RustcLangItemRangeToInclusive, RustcLangItemRangeTo, RustcLangItemRangeMax, RustcLangItemRangeMin, RustcLangItemRangeSub, RustcLangItemRangeFromCopy, RustcLangItemRangeCopy, RustcLangItemRangeInclusiveCopy, RustcLangItemRangeToInclusiveCopy, RustcLangItemString, RustcLangItemCStr, RustcLangItemContractBuildCheckEnsures, RustcLangItemContractCheckRequires, RustcLangItemDefaultTrait4, RustcLangItemDefaultTrait3, RustcLangItemDefaultTrait2, RustcLangItemDefaultTrait1, RustcLangItemContractCheckEnsures, RustcLangItemReborrow, RustcLangItemCoerceShared, RustcLangItemFieldRepresentingType, RustcLangItemField, RustcLangItemFieldBase, RustcLangItemFieldType, RustcLangItemFieldOffset, RustcLangItemFrom, RustcLangItemFromFn]"


@dataclass
class Layout:
    r"""Type layout information.

    Does not include information about niches.
    If the type does not have a fully known layout (e.g. it is ?Sized)
    some of the layout parts are not available."""
    size: SizeExpr
    r"""The size of the type in bytes."""
    align: SizeExpr
    r"""The alignment, in bytes."""
    discriminator: Optional[Discriminator]
    r"""Decision tree that determines the active variant by reading memory. Only `Some` for enums."""
    uninhabited: bool
    r"""Whether the type is uninhabited, i.e. has any valid value at all.
    Note that uninhabited types can have arbitrary layouts: `(u32, !)` has space for the `u32`
    and `enum E2 { A, B(!), C(i32, !) }` may have space for a discriminant."""
    variant_layouts: list[Optional[VariantLayout]]
    r"""Map from `VariantId` to the corresponding field layouts. Some variants don't have a
    meaningful layout due to being uninhabited (though an uninhabited variant may have a
    layout). Structs and unions are modeled as having exactly one variant."""
    repr: ReprOptions
    r"""The representation options of this type declaration as annotated by the user."""


@dataclass
class LifetimeMutabilityLtMutable:
    r"""A lifetime that is used for a mutable reference."""

@dataclass
class LifetimeMutabilityLtShared:
    r"""A lifetime used only in shared references."""

@dataclass
class LifetimeMutabilityLtUnknown:
    r"""A lifetime for which we couldn't/didn't compute mutability."""

# The nature of locations where a given lifetime parameter is used. If this lifetime ever flows
# to be used as the lifetime of a mutable reference `&'a mut` then we consider it mutable.
LifetimeMutability: TypeAlias = "Union[LifetimeMutabilityLtMutable, LifetimeMutabilityLtShared, LifetimeMutabilityLtUnknown]"


@dataclass
class Loc:
    line: int
    r"""The (1-based) line number."""
    col: int
    r"""The (0-based) column offset."""


@dataclass
class Local:
    r"""A variable"""
    index: LocalId
    r"""Unique index identifying the variable"""
    name: Optional[str]
    r"""Variable name - may be `None` if the variable was introduced by Rust
    through desugaring."""
    span: Span
    r"""Span of the variable declaration."""
    local_ty: Ty
    r"""The variable type"""


LocalId = NewType("LocalId", int)


@dataclass
class Locals:
    r"""The local variables of a body."""
    arg_count: int
    r"""The number of local variables used for the input arguments."""
    locals: list[Local]
    r"""The local variables.
    We always have, in the following order:
    - the local used for the return value (index 0)
    - the `arg_count` input arguments
    - the remaining locals, used for the intermediate computations"""


@dataclass
class MaybeAssocItemIdItemFree:
    _0: ItemId

@dataclass
class MaybeAssocItemIdItemAssoc:
    _0: TraitDeclId
    _1: AssocItemId

# The id of a translated item or associated item definition.
MaybeAssocItemId: TypeAlias = "Union[MaybeAssocItemIdItemFree, MaybeAssocItemIdItemAssoc]"


@dataclass
class MetadataValueDynSize:
    r"""For a DST with `dyn Trait` metadata, this refers to the size found in the metadata."""

@dataclass
class MetadataValueDynAlign:
    r"""For a DST with `dyn Trait` metadata, this refers to the alignment found in the metadata."""

@dataclass
class MetadataValueSliceLength:
    r"""For a DST with slice metadata, this refers to the length found in the metadata."""

# Layout information given by the metadata of an unsized type.
MetadataValue: TypeAlias = "Union[MetadataValueDynSize, MetadataValueDynAlign, MetadataValueSliceLength]"


@dataclass
class MirLevelBuilt:
    r"""The MIR just after MIR lowering."""

@dataclass
class MirLevelPromoted:
    r"""The MIR after const promotion. This is the MIR used by the borrow-checker."""

@dataclass
class MirLevelElaborated:
    r"""The MIR after drop elaboration. This is the first MIR to include all the runtime
    information."""

@dataclass
class MirLevelOptimized:
    r"""The MIR after optimizations. Charon disables all the optimizations it can, so this is
    sensibly the same MIR as the elaborated MIR."""

# The MIR stage to use. This is only relevant for the current crate: for dependencies, only mir
# optimized is available (or mir elaborated for consts).
MirLevel: TypeAlias = "Union[MirLevelBuilt, MirLevelPromoted, MirLevelElaborated, MirLevelOptimized]"


@dataclass
class MonomorphizeMutAll:
    r"""Monomorphize any item instantiated with `&mut`."""

@dataclass
class MonomorphizeMutExceptTypes:
    r"""Monomorphize all non-typedecl items instantiated with `&mut`."""

MonomorphizeMut: TypeAlias = "Union[MonomorphizeMutAll, MonomorphizeMutExceptTypes]"


# An item name/path
# A name really is a list of strings. However, we sometimes need to
# introduce unique indices to disambiguate. This mostly happens because
# of "impl" blocks:
# ```text
# impl<T> List<T> {
# ...
# }
# ```
# A type in Rust can have several "impl" blocks, and  those blocks can
# contain items with similar names. For this reason, we need to disambiguate
# them with unique indices. Rustc calls those "disambiguators". In rustc, this
# gives names like this:
# - `betree_main::betree::NodeIdCounter{impl#0}::new`
# - note that impl blocks can be nested, and macros sometimes generate
# weird names (which require disambiguation):
# `betree_main::betree_utils::_#1::{impl#0}::deserialize::{impl#0}`
# Finally, the paths used by rustc are a lot more precise and explicit than
# those we expose in LLBC: for instance, every identifier belongs to a specific
# namespace (value namespace, type namespace, etc.), and is coupled with a
# disambiguator.
# On our side, we want to stay high-level and simple: we use string identifiers
# as much as possible, insert disambiguators only when necessary (for instance
# when we find an "impl" block or when two loaded crates have the same name)
# and check that the disambiguator is useless in the other situations (i.e.,
# the disambiguator is always equal to 0).
# Moreover, the items are uniquely disambiguated by their (integer) ids
# (`TypeDeclId`, etc.), and when extracting the code we have to deal with
# name clashes anyway. Still, we might want to be more precise in the future.
# Also note that the first path element in the name is always the crate name.
Name: TypeAlias = "list[PathElem]"


@dataclass
class NullopSizeOf:
    pass

@dataclass
class NullopAlignOf:
    pass

@dataclass
class NullopOffsetOf:
    _0: TypeDeclRef
    _1: Optional[VariantId]
    _2: FieldId

@dataclass
class NullopUbChecks:
    pass

@dataclass
class NullopOverflowChecks:
    pass

@dataclass
class NullopContractChecks:
    pass

# Nullary operation
Nullop: TypeAlias = "Union[NullopSizeOf, NullopAlignOf, NullopOffsetOf, NullopUbChecks, NullopOverflowChecks, NullopContractChecks]"


@dataclass
class OffsetExpr:
    r"""An expression denoting an offset in bytes."""
    guarantee: Optional[OffsetGuarantee]
    r"""The guarantees about this offset that can be relied on according to the Rust Reference."""
    chosen: Optional[int]
    r"""The offset chosen by this rustc run. `None` for unsized fields."""


@dataclass
class OffsetGuaranteeAtOffsetZero:
    r"""Guaranteed to be at offset zero. This applies for `repr(transparent)` and in some `repr(C)` cases."""

@dataclass
class OffsetGuaranteeGuaranteedAlignment:
    r"""Guaranteed only to be aligned to the given expression."""
    _0: ExactSizeExpr

@dataclass
class OffsetGuaranteeReprCField:
    r"""This offset is computed by the layout algorithm for C: take the previous field offset, add
    the previous field size, and align to the current field alignment."""
    predecessor: Optional[FieldId]
    r"""If this is `None`, then the field is directly after the enum tag."""

# Guaranteed facts about a field offset.
OffsetGuarantee: TypeAlias = "Union[OffsetGuaranteeAtOffsetZero, OffsetGuaranteeGuaranteedAlignment, OffsetGuaranteeReprCField]"


@dataclass
class OperandCopy:
    _0: Place

@dataclass
class OperandMove:
    _0: Place

@dataclass
class OperandConstant:
    r"""Constant value (including constant and static variables)"""
    _0: ConstantExpr

Operand: TypeAlias = "Union[OperandCopy, OperandMove, OperandConstant]"


@dataclass
class RustcOptimizeAttrDefault:
    r"""No `#[optimize(..)]` attribute"""

@dataclass
class RustcOptimizeAttrDoNotOptimize:
    r"""`#[optimize(none)]`"""

@dataclass
class RustcOptimizeAttrSpeed:
    r"""`#[optimize(speed)]`"""

@dataclass
class RustcOptimizeAttrSize:
    r"""`#[optimize(size)]`"""

RustcOptimizeAttr: TypeAlias = "Union[RustcOptimizeAttrDefault, RustcOptimizeAttrDoNotOptimize, RustcOptimizeAttrSpeed, RustcOptimizeAttrSize]"


@dataclass
class OutlivesPred(Generic[T0, T1]):
    r""".0 outlives .1"""
    _0: T0
    _1: T1


@dataclass
class OverflowModeOPanic:
    r"""If this operation overflows, it panics. Only exists in debug mode, for instance in
    `a + b`, and only if `--reconstruct-fallible-operations` is passed to Charon. Otherwise the
    bound check will be explicit."""

@dataclass
class OverflowModeOUB:
    r"""If this operation overflows, it is UB; for instance in `core::num::unchecked_add`. This can
    exists in safe code, but will always be preceded by a bounds check."""

@dataclass
class OverflowModeOWrap:
    r"""If this operation overflows, it wraps around for instance in `core::num::wrapping_add`,
    or `a + b` in release mode."""

OverflowMode: TypeAlias = "Union[OverflowModeOPanic, OverflowModeOUB, OverflowModeOWrap]"


@dataclass
class PathElemPeIdent:
    _0: str
    _1: Disambiguator

@dataclass
class PathElemPeImpl:
    _0: ImplElem

@dataclass
class PathElemPeInstantiated:
    r"""This item was obtained by instantiating its parent with the given args. The binder binds
    the parameters of the new items. If the binder binds nothing then this is a
    monomorphization."""
    _0: Binder[GenericArgs]

@dataclass
class PathElemPeTarget:
    r"""This item is only available on the given target. Only appears in multi-target mode."""
    _0: str

@dataclass
class PathElemPeBuiltin:
    r"""A path element that doesn't come from the source code: either a builtin type such as
    tuples, or an item that has no name of its own such as a closure or a vtable."""
    _0: BuiltinPathElem
    _1: Disambiguator

# See the comments for [Name]
PathElem: TypeAlias = "Union[PathElemPeIdent, PathElemPeImpl, PathElemPeInstantiated, PathElemPeTarget, PathElemPeBuiltin]"


@dataclass
class Place:
    kind: PlaceKind
    ty: Ty


@dataclass
class PlaceKindPlaceLocal:
    r"""A local variable in a function body."""
    _0: LocalId

@dataclass
class PlaceKindPlaceProjection:
    r"""A subplace of a place."""
    _0: Place
    _1: ProjectionElem

@dataclass
class PlaceKindPlaceGlobal:
    r"""A global (const or static).
    Not present in MIR; introduced in [simplify_constants.rs]."""
    _0: GlobalDeclRef

PlaceKind: TypeAlias = "Union[PlaceKindPlaceLocal, PlaceKindPlaceProjection, PlaceKindPlaceGlobal]"


@dataclass
class PredicateOriginWhereClauseOnFn:
    pass

@dataclass
class PredicateOriginWhereClauseOnType:
    pass

@dataclass
class PredicateOriginWhereClauseOnImpl:
    pass

@dataclass
class PredicateOriginTraitSelf:
    pass

@dataclass
class PredicateOriginWhereClauseOnTrait:
    pass

@dataclass
class PredicateOriginTraitItem:
    _0: AssocTypeId

@dataclass
class PredicateOriginOriginDyn:
    r"""Clauses that are part of a `dyn Trait` type."""

# Where a given predicate came from.
PredicateOrigin: TypeAlias = "Union[PredicateOriginWhereClauseOnFn, PredicateOriginWhereClauseOnType, PredicateOriginWhereClauseOnImpl, PredicateOriginTraitSelf, PredicateOriginWhereClauseOnTrait, PredicateOriginTraitItem, PredicateOriginOriginDyn]"


@dataclass
class PresetOldDefaults:
    r"""The default translation used before May 2025. After that, many passes were made optional
    and disabled by default."""

@dataclass
class PresetRawMir:
    r"""Emit the MIR as unmodified as possible. This is very imperfect for now, we should make more
    passes optional."""

@dataclass
class PresetFast:
    r"""Skip as many optional transformations as possible."""

@dataclass
class PresetAeneas:
    pass

@dataclass
class PresetEurydice:
    pass

@dataclass
class PresetSoteria:
    pass

@dataclass
class PresetTests:
    pass

# Presets to make it easier to tweak options without breaking dependent projects. Eventually we
# should define semantically-meaningful presets instead of project-specific ones.
Preset: TypeAlias = "Union[PresetOldDefaults, PresetRawMir, PresetFast, PresetAeneas, PresetEurydice, PresetSoteria, PresetTests]"


@dataclass
class ProjectionElemDeref:
    r"""Dereference a shared/mutable reference, a box, or a raw pointer."""

@dataclass
class ProjectionElemField:
    r"""Project to the field of an ADT (struct, union, or enum)."""
    _0: Optional[VariantId]
    _1: FieldId

@dataclass
class ProjectionElemPtrMetadata:
    r"""A built-in pointer (a reference, raw pointer, or `Box`) in Rust is always a fat pointer: it
    contains an address and metadata for the pointed-to place. This metadata is empty for sized
    types, it's the length for slices, and the vtable for `dyn Trait`.

    We consider such pointers to be like a struct with two fields; this represent access to the
    metadata "field"."""

@dataclass
class ProjectionElemProjIndex:
    r"""MIR imposes that the argument to an index projection be a local variable, meaning
    that even constant indices into arrays are let-bound as separate variables.
    We **eliminate** this variant in a micro-pass for LLBC."""
    offset: Operand
    from_end: bool

@dataclass
class ProjectionElemSubslice:
    r"""Take a subslice of a slice or array. If `from_end` is `true` this is
    `slice[from..slice.len() - to]`, otherwise this is `slice[from..to]`.
    We **eliminate** this variant in a micro-pass for LLBC."""
    from_: Operand
    to: Operand
    from_end: bool

# Projects a place to a subplace.
ProjectionElem: TypeAlias = "Union[ProjectionElemDeref, ProjectionElemField, ProjectionElemPtrMetadata, ProjectionElemProjIndex, ProjectionElemSubslice]"


@dataclass
class ProvenanceProvGlobal:
    _0: GlobalDeclRef

@dataclass
class ProvenanceProvFunction:
    _0: FunDeclRef

@dataclass
class ProvenanceProvUnknown:
    pass

Provenance: TypeAlias = "Union[ProvenanceProvGlobal, ProvenanceProvFunction, ProvenanceProvUnknown]"


@dataclass
class PtrMetadataNoMetadata:
    r"""Types that need no metadata, namely `T: Sized` types."""

@dataclass
class PtrMetadataLength:
    r"""Metadata for `[T]` and `str`, and user-defined types
    that directly or indirectly contain one of the two.
    Of type `usize`.
    Notably, length for `[T]` denotes the number of elements in the slice.
    While for `str` it denotes the number of bytes in the string."""

@dataclass
class PtrMetadataVTable:
    r"""Metadata for `dyn Trait`, referring to the vtable struct. Has type `&'static vtable`"""
    _0: TypeDeclRef

@dataclass
class PtrMetadataInheritFrom:
    r"""Unknown due to generics, but will inherit from the given type.
    This is consistent with `<Ty as Pointee>::Metadata`.
    Of type `TyKind::Metadata(Ty)`."""
    _0: Ty

# The metadata stored in a pointer. That's the information stored in pointers alongside
# their address. It's empty for `Sized` types, and interesting for unsized
# aka dynamically-sized types.
PtrMetadata: TypeAlias = "Union[PtrMetadataNoMetadata, PtrMetadataLength, PtrMetadataVTable, PtrMetadataInheritFrom]"


@dataclass
class RawAttribute:
    r"""A general attribute."""
    path: str
    args: Optional[str]
    r"""The arguments passed to the attribute, if any. We don't distinguish different delimiters or
    the `path = lit` case."""


@dataclass
class RefKindRMut:
    pass

@dataclass
class RefKindRShared:
    pass

RefKind: TypeAlias = "Union[RefKindRMut, RefKindRShared]"


@dataclass
class RegionRVar:
    r"""Region variable. See `DeBruijnVar` for details."""
    _0: DeBruijnVar[RegionId]

@dataclass
class RegionRStatic:
    r"""Static region"""

@dataclass
class RegionRBody:
    r"""Body-local region, considered existentially-bound at the level of a body."""
    _0: RegionId

@dataclass
class RegionRErased:
    r"""Erased region"""

Region: TypeAlias = "Union[RegionRVar, RegionRStatic, RegionRBody, RegionRErased]"


@dataclass
class RegionBinder(Generic[T0]):
    r"""A value of type `T` bound by regions. We should use `binder` instead but this causes name clash
    issues in the derived ocaml visitors."""
    binder_regions: list[RegionParam]
    binder_value: T0
    r"""Named this way to highlight accesses to the inner value that might be handling parameters
    incorrectly. Prefer using helper methods."""


RegionId = NewType("RegionId", int)


@dataclass
class RegionParam:
    r"""A region variable in a signature or binder."""
    index: RegionId
    r"""Index identifying the variable among other variables bound at the same level."""
    name: Optional[str]
    r"""Region name"""
    variance: Variance
    r"""Variance of this parameter."""
    mutability: LifetimeMutability
    r"""Whether this lifetime is (recursively) used in a `&'a mut T` type. Only `true` if this
    lifetime parameter belongs to an ADT. This is a global analysis that looks even into opaque
    items. When unsure, err on the side of assuming mutability."""


@dataclass
class ReprAlgorithmRust:
    r"""The default layout algorithm. Used without an explicit `ŗepr` or for `repr(Rust)`."""

@dataclass
class ReprAlgorithmC:
    r"""The C layout algorithm as enforced by `repr(C)`."""

# Describes which layout algorithm is used for representing the corresponding type.
# Depends on the `#[repr(...)]` used.
ReprAlgorithm: TypeAlias = "Union[ReprAlgorithmRust, ReprAlgorithmC]"


@dataclass
class ReprOptions:
    r"""The representation options as annotated by the user.

    NOTE: This does not include less common/unstable representations such as `#[repr(simd)]`
    or the compiler internal `#[repr(linear)]`. Similarly, enum discriminant representations
    are encoded in [`Variant::discriminant`] and [`Discriminator`] instead."""
    repr_algo: ReprAlgorithm
    align_modif: Optional[AlignmentModifier]
    transparent: bool
    explicit_discr_type: Optional[IntegerType]
    r"""The type supplied to `repr(..)`, if any."""


@dataclass
class RustcRustcVersion:
    major: int
    minor: int
    patch: int


@dataclass
class RvalueUse:
    r"""Lifts an operand as an rvalue."""
    _0: Operand
    _1: WithRetag

@dataclass
class RvalueRvRef:
    r"""Takes a reference to the given place.
    The `Operand` refers to the init value of the metadata, it is `()` if no metadata"""
    place: Place
    kind: BorrowKind
    ptr_metadata: Operand

@dataclass
class RvalueRawPtr:
    r"""Takes a raw pointer with the given mutability to the given place. This is generated by
    pointer casts like `&v as *const _` or raw borrow expressions like `&raw const v.`
    Like `Ref`, the `Operand` refers to the init value of the metadata, it is `()` if no metadata."""
    place: Place
    kind: RefKind
    ptr_metadata: Operand

@dataclass
class RvalueBinaryOp:
    r"""Binary operations (note that we merge "checked" and "unchecked" binops)"""
    _0: Binop
    _1: Operand
    _2: Operand

@dataclass
class RvalueUnaryOp:
    r"""Unary operation (e.g. not, neg)"""
    _0: Unop
    _1: Operand

@dataclass
class RvalueNullaryOp:
    r"""Nullary operation (e.g. `size_of`)"""
    _0: Nullop
    _1: Ty

@dataclass
class RvalueDiscriminant:
    r"""Discriminant read. Reads the discriminant value of an enum. The place must have the type of
    an enum. The discriminant in question is the one in the `discriminant` field of the
    corresponding `Variant`. This can be different than the value stored in memory (called
    `tag`); that one is described by [`Discriminator`] and [`VariantLayout::tagger`]."""
    _0: Place

@dataclass
class RvalueAggregate:
    r"""Creates an aggregate value, like a tuple, a struct or an enum:
    ```text
    l = List::Cons { value:x, tail:tl };
    ```
    Note that in some MIR passes (like optimized MIR), aggregate values are
    decomposed, like below:
    ```text
    (l as List::Cons).value = x;
    (l as List::Cons).tail = tl;
    ```
    Because we may want to plug our translation mechanism at various
    places, we need to take both into accounts in the translation and in
    our semantics. Aggregate value initialization is easy, you might want
    to have a look at expansion of `Bottom` values for explanations about the
    other case.

    Remark: in case of closures, the aggregated value groups the closure id
    together with its state."""
    _0: AggregateKind
    _1: list[Operand]

@dataclass
class RvalueLen:
    r"""Length of a place of type `[T]` or `[T; N]`. This applies to the place itself, not to a
    pointer value. This is inserted by rustc in a single case: slice patterns.
    ```text
    fn slice_pattern_4(x: &[()]) {
        match x {
            [_named] => (),
            _ => (),
        }
    }
    ```"""
    _0: Place
    _1: Ty
    _2: Optional[ConstantExpr]

@dataclass
class RvalueRepeat:
    r"""`Repeat(x, n)` creates an array where `x` is copied `n` times.

    We translate this to a function call for LLBC.
    The last field is the proof that the repeated value is `Copy`."""
    _0: Operand
    _1: Ty
    _2: ConstantExpr
    _3: TraitRef

# An expression that evaluates to a value. This is the RHS of an assignment.
Rvalue: TypeAlias = "Union[RvalueUse, RvalueRvRef, RvalueRawPtr, RvalueBinaryOp, RvalueUnaryOp, RvalueNullaryOp, RvalueDiscriminant, RvalueAggregate, RvalueLen, RvalueRepeat]"


@dataclass
class ScalarTypeTInteger:
    _0: IntegerType

@dataclass
class ScalarTypeTFloat:
    _0: FloatType

@dataclass
class ScalarTypeTBool:
    pass

@dataclass
class ScalarTypeTChar:
    pass

# Types of primitive scalar values.
ScalarType: TypeAlias = "Union[ScalarTypeTInteger, ScalarTypeTFloat, ScalarTypeTBool, ScalarTypeTChar]"


@dataclass
class SerializationFormatArgJson:
    pass

@dataclass
class SerializationFormatArgPostcard:
    pass

@dataclass
class SerializationFormatArgAllFormats:
    pass

SerializationFormatArg: TypeAlias = "Union[SerializationFormatArgJson, SerializationFormatArgPostcard, SerializationFormatArgAllFormats]"


@dataclass
class SizeExpr:
    r"""An expression denoting a size in bytes."""
    guarantee: Optional[SizeGuarantee]
    r"""The guarantees about this size that can be relied on according to the Rust Reference."""
    chosen: Optional[int]
    r"""The size chosen by this rustc run. `None` for unsized types."""


@dataclass
class SizeGuaranteeEquals:
    _0: ExactSizeExpr

@dataclass
class SizeGuaranteeAtLeast:
    _0: ExactSizeExpr

# Guaranteed facts about a layout size.
SizeGuarantee: TypeAlias = "Union[SizeGuaranteeEquals, SizeGuaranteeAtLeast]"


@dataclass
class Span:
    r"""A snippet of source code within a file, along with the place the code was generated from in
    case of macro expansion. This is a pair of the span itself (`data`) and an optional
    "generated from" span (`generated_from_span`).

    For code coming from a macro expansion, `data` is the span of the macro before expansion, i.e.
    the location where the user wrote the call to the macro, and `generated_from_span` is where
    the code actually comes from.

    Ex:
    ```text
    // Below, we consider the spans for the statements inside `test`

    //   the statement we consider, which gets inlined in `test`
                             VV
    macro_rules! macro { ... st ... } // `generated_from_span` refers to this location

    fn test() {
        macro!(); // <-- `data` refers to this location
    }
    ```"""
    data: SpanData
    r"""The source code span; for code coming from a macro expansion, the location of the macro
    call."""
    generated_from_span: Optional[SpanData]
    r"""Where the code actually comes from, in case of macro expansion/inlining/etc."""


@dataclass
class SpanData:
    r"""A snippet of source code within a file."""
    file: FileId
    beg_loc: Loc
    end_loc: Loc


@dataclass
class UllbcStatement:
    r"""A statement."""
    span: Span
    kind: UllbcStatementKind
    comments_before: list[str]
    r"""Comments that precede this statement."""


@dataclass
class LlbcStatement:
    r"""A statement, which can contain nested statements inside loops or switchers."""
    span: Span
    statement_id: StatementId
    r"""Integer uniquely identifying this statement among the statmeents in the current body. To
    simplify things we generate globally-fresh ids when creating a new `Statement`."""
    kind: LlbcStatementKind
    comments_before: list[str]
    r"""Comments that precede this statement."""


StatementId = NewType("StatementId", int)


@dataclass
class UllbcStatementKindAssign:
    _0: Place
    _1: Rvalue

@dataclass
class UllbcStatementKindSetDiscriminant:
    r"""A call. For now, we don't support dynamic calls (i.e. to a function pointer in memory)."""
    _0: Place
    _1: VariantId

@dataclass
class UllbcStatementKindStorageLive:
    r"""Indicates that this local should be allocated; if it is already allocated, this frees
    the local and re-allocates it. The arguments do not receive a `StorageLive`. We ensure in
    the micro-pass `insert_storage_statements` that all other locals have a `StorageLive`
    associated with them."""
    _0: LocalId

@dataclass
class UllbcStatementKindStorageDead:
    r"""Deallocates the given local; if it is already deallocated, this is
    a no-op. Not all local deallocations are explicit: if a non-return local is still live at
    function end (return or unwind), it is implicitly deallocated.
    If `--deallocate-all-locals` is set, all local deallocations are made explicit."""
    _0: LocalId

@dataclass
class UllbcStatementKindPlaceMention:
    r"""A place is mentioned, but not accessed. The place itself must still be valid though, so
    this statement is not a no-op: it can trigger UB if the place's projections are not valid
    (e.g. because they go out of bounds)."""
    _0: Place

@dataclass
class UllbcStatementKindBorrowck:
    r"""Statements that only affect borrow-checking."""
    _0: BorrowckStatement

@dataclass
class UllbcStatementKindAssert:
    r"""A non-diverging runtime check for a condition. This can be either:
    - Emitted for inlined "assumes" (which cause UB on failure)
    - Reconstructed from `if b { panic() }` if `--reconstruct-asserts` is set.

    This statement comes with the effect that happens when the check fails
    (rather than representing it as an unwinding edge)."""
    assert_: Assertion
    on_failure: AbortKind

@dataclass
class UllbcStatementKindNop:
    r"""Does nothing. Useful for passes."""

UllbcStatementKind: TypeAlias = "Union[UllbcStatementKindAssign, UllbcStatementKindSetDiscriminant, UllbcStatementKindStorageLive, UllbcStatementKindStorageDead, UllbcStatementKindPlaceMention, UllbcStatementKindBorrowck, UllbcStatementKindAssert, UllbcStatementKindNop]"


@dataclass
class LlbcStatementKindAssign:
    r"""Assigns an `Rvalue` to a `Place`. e.g. `let y = x;` could become
    `y := move x` which is represented as `Assign(y, Rvalue::Use(Operand::Move(x)))`."""
    _0: Place
    _1: Rvalue

@dataclass
class LlbcStatementKindSetDiscriminant:
    r"""Not used today because we take MIR built."""
    _0: Place
    _1: VariantId

@dataclass
class LlbcStatementKindStorageLive:
    r"""Indicates that this local should be allocated; if it is already allocated, this frees
    the local and re-allocates it. The arguments do not receive a `StorageLive`. We ensure in
    the micro-pass `insert_storage_statements` that all other locals have a `StorageLive`
    associated with them."""
    _0: LocalId

@dataclass
class LlbcStatementKindStorageDead:
    r"""Deallocates the given local; if it is already deallocated, this is
    a no-op. Not all local deallocations are explicit: if a non-return local is still live at
    function end (return or unwind), it is implicitly deallocated.
    If `--deallocate-all-locals` is set, all local deallocations are made explicit."""
    _0: LocalId

@dataclass
class LlbcStatementKindPlaceMention:
    r"""A place is mentioned, but not accessed. The place itself must still be valid though, so
    this statement is not a no-op: it can trigger UB if the place's projections are not valid
    (e.g. because they go out of bounds)."""
    _0: Place

@dataclass
class LlbcStatementKindBorrowck:
    r"""Statements that only affect borrow-checking."""
    _0: BorrowckStatement

@dataclass
class LlbcStatementKindDrop:
    r"""Drop the value at the given place.

    Depending on `DropKind`, this may be a real call to `drop_glue`, or a conditional call
    that should only happen if the place has not been moved out of. See the docs of `DropKind`
    for more details; to get precise drops use `--precise-drops`."""
    place: Place
    fn_ptr: FnPtr
    r"""Reference to the `drop_glue` code to call on drop."""
    kind: DropKind
    on_unwind: LlbcBlock

@dataclass
class LlbcStatementKindAssert:
    assert_: Assertion
    on_failure: AbortKind
    on_unwind: LlbcBlock

@dataclass
class LlbcStatementKindInlineAsm:
    r"""An inline assembly block. For now we only preserve the template string."""
    asm: str
    targets: list[LlbcBlock]
    on_unwind: LlbcBlock

@dataclass
class LlbcStatementKindCall:
    call: Call
    on_unwind: LlbcBlock

@dataclass
class LlbcStatementKindAbort:
    r"""Panic also handles "unreachable". We keep the name of the panicking function that was
    called."""
    _0: AbortKind

@dataclass
class LlbcStatementKindReturn:
    pass

@dataclass
class LlbcStatementKindUnwindResume:
    r"""Unwind out of the current function into its caller."""

@dataclass
class LlbcStatementKindBreak:
    r"""Break to outer loops.
    The `usize` gives the index of the outer loop to break to:
    * 0: break to first outer loop (the current loop)
    * 1: break to second outer loop
    * ..."""
    _0: int

@dataclass
class LlbcStatementKindContinue:
    r"""Continue to outer loops.
    The `usize` gives the index of the outer loop to continue to:
    * 0: continue to first outer loop (the current loop)
    * 1: continue to second outer loop
    * ..."""
    _0: int

@dataclass
class LlbcStatementKindNop:
    r"""No-op."""

@dataclass
class LlbcStatementKindSwitch:
    data: SwitchData
    branches: list[LlbcBlock]

@dataclass
class LlbcStatementKindLoop:
    _0: LlbcBlock

@dataclass
class LlbcStatementKindError:
    _0: str

LlbcStatementKind: TypeAlias = "Union[LlbcStatementKindAssign, LlbcStatementKindSetDiscriminant, LlbcStatementKindStorageLive, LlbcStatementKindStorageDead, LlbcStatementKindPlaceMention, LlbcStatementKindBorrowck, LlbcStatementKindDrop, LlbcStatementKindAssert, LlbcStatementKindInlineAsm, LlbcStatementKindCall, LlbcStatementKindAbort, LlbcStatementKindReturn, LlbcStatementKindUnwindResume, LlbcStatementKindBreak, LlbcStatementKindContinue, LlbcStatementKindNop, LlbcStatementKindSwitch, LlbcStatementKindLoop, LlbcStatementKindError]"


@dataclass
class SwitchData:
    r"""A branching operation."""
    scrutinee: SwitchScrutinee
    r"""The value to branch over."""
    branches: list[tuple[ConstantExpr, BranchId]]
    r"""Which branch to take for each value of the scrutinee. Several values may point to the same
    branch, and not all values may be accounted for.

    If the scrutinee is an operand, the constant expressions are literal values. If the
    scrutinee is a discriminant read, the expressions are of the form
    `ConstantExprKind::Discriminant`."""
    fallback: Optional[BranchId]
    r"""Branch to use if the scrutinee didn't match any of the values above. `None` if the set of
    branch values is known to be exhaustive."""


@dataclass
class SwitchScrutineeSwitchValue:
    r"""Inspect the value produced by an operand."""
    _0: Operand

@dataclass
class SwitchScrutineeSwitchDiscriminant:
    r"""Inspect the discriminant of an enum place."""
    _0: Place

# The value inspected by a switch. Must be of integer, bool or char type.
SwitchScrutinee: TypeAlias = "Union[SwitchScrutineeSwitchValue, SwitchScrutineeSwitchDiscriminant]"


@dataclass
class TargetInfo:
    target_pointer_size: int
    r"""The pointer size of the target in bytes."""
    is_little_endian: bool
    r"""Whether the target platform uses little endian byte order."""
    c_enum_smallest_repr_ty: IntTy
    r"""The minimum size of a [`repr(C)`] enum."""
    primitive_alignments: list[tuple[ScalarType, int]]
    r"""Alignments for primitive types."""


@dataclass
class Terminator:
    r"""A terminator: instruction to execute at the end of a block, which may jump to other blocks."""
    span: Span
    kind: TerminatorKind
    comments_before: list[str]
    r"""Comments that precede this terminator."""


@dataclass
class TerminatorKindGoto:
    target: UllbcBlockId

@dataclass
class TerminatorKindSwitch:
    data: SwitchData
    branches: list[UllbcBlockId]

@dataclass
class TerminatorKindCall:
    call: Call
    target: UllbcBlockId
    on_unwind: UllbcBlockId

@dataclass
class TerminatorKindDrop:
    r"""Drop the value at the given place.

    Depending on `DropKind`, this may be a real call to `drop_glue`, or a conditional call
    that should only happen if the place has not been moved out of. See the docs of `DropKind`
    for more details; to get precise drops use `--precise-drops`."""
    kind: DropKind
    place: Place
    fn_ptr: FnPtr
    r"""Reference to the `drop_glue` code to call on drop."""
    target: UllbcBlockId
    on_unwind: UllbcBlockId

@dataclass
class TerminatorKindTAssert:
    r"""Assert that the given condition holds, and if not, unwind to the given block. This is used for
    bounds checks, overflow checks, etc."""
    assert_: Assertion
    target: UllbcBlockId
    on_unwind: UllbcBlockId

@dataclass
class TerminatorKindInlineAsm:
    r"""An inline assembly block. For now we only preserve the template string."""
    asm: str
    targets: list[UllbcBlockId]
    on_unwind: UllbcBlockId

@dataclass
class TerminatorKindAbort:
    r"""Handles panics and impossible cases."""
    _0: AbortKind

@dataclass
class TerminatorKindReturn:
    pass

@dataclass
class TerminatorKindUnwindResume:
    r"""Unwind out of the current function into its caller."""

TerminatorKind: TypeAlias = "Union[TerminatorKindGoto, TerminatorKindSwitch, TerminatorKindCall, TerminatorKindDrop, TerminatorKindTAssert, TerminatorKindInlineAsm, TerminatorKindAbort, TerminatorKindReturn, TerminatorKindUnwindResume]"


@dataclass
class TraitAssocConst:
    r"""An associated constant in a trait."""
    name: TraitItemName
    attr_info: AttrInfo
    ty: Ty
    default: Optional[GlobalDeclRef]


@dataclass
class TraitAssocTy:
    r"""An associated type in a trait."""
    name: TraitItemName
    attr_info: AttrInfo
    default: Optional[TraitAssocTyImpl]
    implied_clauses: list[TraitParam]
    r"""List of trait clauses that apply to this type."""


@dataclass
class TraitAssocTyImpl:
    r"""The value of a trait associated type."""
    value: Ty
    implied_trait_refs: list[TraitRef]
    r"""This matches the corresponding vector in `TraitAssocTy`. In the same way, this is empty
    after the `lift_associated_item_clauses` pass."""


TraitClauseId = NewType("TraitClauseId", int)


@dataclass
class TraitDecl:
    r"""A trait **declaration**.

    For instance:
    ```text
    trait Foo {
      type Bar;

      fn baz(...); // required method (see below)

      fn test() -> bool { true } // provided method (see below)
    }
    ```

    In case of a trait declaration, we don't include the provided methods (the methods
    with a default implementation): they will be translated on a per-need basis. This is
    important for two reasons:
    - this makes the trait definitions a lot smaller (the Iterator trait
      has *one* declared function and more than 70 provided functions)
    - this is important for the external traits, whose provided methods
      often use features we don't support yet

    Remark:
    In Aeneas, we still translate the provided methods on an individual basis,
    and in such a way thay they take as input a trait instance. This means that
    we can use default methods *but*:
    - implementations of required methods shoudln't call default methods
    - trait implementations shouldn't redefine required methods

    The use case we have in mind is [std::iter::Iterator]: it declares one required
    method (`next`) that should be implemented for every iterator, and defines many
    helpers like `all`, `map`, etc. that shouldn't be re-implemented.
    Of course, this forbids other useful use cases such as visitors implemented
    by means of traits."""
    def_id: TraitDeclId
    item_meta: ItemMeta
    src: TraitDeclSource
    r"""Distinguishes normal traits from trait aliases."""
    generics: GenericParams
    implied_clauses: list[TraitParam]
    r"""The "parent" clauses: the supertraits.

    Supertraits are actually regular where clauses, but we decided to have
    a custom treatment.
    ```text
    trait Foo : Bar {
                ^^^
            supertrait, that we treat as a parent predicate
    }
    ```
    TODO: actually, as of today, we consider that all trait clauses of
    trait declarations are parent clauses."""
    consts: dict[AssocConstId, TraitAssocConst]
    r"""The associated constants declared in the trait."""
    types: dict[AssocTypeId, Binder[TraitAssocTy]]
    r"""The associated types declared in the trait. The binder binds the generic parameters of the
    type if it is a GAT (Generic Associated Type). For a plain associated type the binder binds
    nothing."""
    methods: dict[TraitMethodId, Binder[TraitMethod]]
    r"""The methods declared by the trait. The binder binds the generic parameters of the method.

    ```rust
    trait Trait<T> {
      // The `Binder` for this method binds `'a` and `U`.
      fn method<'a, U>(x: &'a U);
    }
    ```"""
    vtable: Optional[TypeDeclRef]
    r"""The virtual table struct for this trait, if it has one.
    It is guaranteed that the trait has a vtable iff it is dyn-compatible."""


TraitDeclId = NewType("TraitDeclId", int)


@dataclass
class TraitDeclRef:
    r"""A predicate of the form `Type: Trait<Args>`.

    About the generics, if we write:
    ```text
    impl Foo<bool> for String { ... }
    ```

    The substitution is: `[String, bool]`."""
    id: TraitDeclId
    generics: GenericArgs


@dataclass
class TraitDeclSourceNormalTraitDecl:
    r"""A regular trait."""

@dataclass
class TraitDeclSourceTraitAliasTraitDecl:
    r"""The trait declaration coming from a trait alias."""

# Where the trait comes from.
TraitDeclSource: TypeAlias = "Union[TraitDeclSourceNormalTraitDecl, TraitDeclSourceTraitAliasTraitDecl]"


@dataclass
class TraitImpl:
    r"""A trait **implementation**.

    For instance:
    ```text
    impl Foo for List {
      type Bar = ...

      fn baz(...) { ... }
    }
    ```"""
    def_id: TraitImplId
    item_meta: ItemMeta
    src: TraitImplSource
    impl_trait: TraitDeclRef
    r"""The information about the implemented trait.
    Note that this contains the instantiation of the "parent"
    clauses."""
    generics: GenericParams
    implied_trait_refs: list[TraitRef]
    r"""The trait references for the parent clauses (see [TraitDecl])."""
    consts: dict[AssocConstId, GlobalDeclRef]
    r"""The implemented associated constants."""
    types: dict[AssocTypeId, Binder[TraitAssocTyImpl]]
    r"""The implemented associated types."""
    methods: dict[TraitMethodId, Binder[FunDeclRef]]
    r"""The implemented methods"""
    vtable: Optional[GlobalDeclRef]
    r"""The virtual table instance for this trait implementation. This is `Some` iff the trait is
    dyn-compatible."""


TraitImplId = NewType("TraitImplId", int)


@dataclass
class TraitImplRef:
    r"""A reference to a tait impl, using the provided arguments."""
    id: TraitImplId
    generics: GenericArgs


@dataclass
class TraitImplSourceNormalTraitImpl:
    r"""A regular trait implementation."""

@dataclass
class TraitImplSourceTraitAliasTraitImpl:
    r"""The blanket implementation generated for a trait alias."""

@dataclass
class TraitImplSourceClosureTraitImpl:
    r"""An implementation of one of the `Fn*` traits, generated for a closure."""
    kind: ClosureKind

@dataclass
class TraitImplSourceDestructTraitImpl:
    r"""The `Destruct` implementation generated for an ADT or closure."""

# Where the impl comes from.
TraitImplSource: TypeAlias = "Union[TraitImplSourceNormalTraitImpl, TraitImplSourceTraitAliasTraitImpl, TraitImplSourceClosureTraitImpl, TraitImplSourceDestructTraitImpl]"


TraitItemName: TypeAlias = "str"


@dataclass
class TraitMethod:
    r"""A trait method."""
    name: TraitItemName
    item_meta: ItemMeta
    signature: FunSig
    default: Optional[FunDeclRef]
    r"""The default method implementation, if there is one."""


TraitMethodId = NewType("TraitMethodId", int)


@dataclass
class TraitParam:
    r"""A trait predicate in a signature, of the form `Type: Trait<Args>`. This functions like a
    variable binder, to which variables of the form `TraitRefKind::Clause` can refer to."""
    clause_id: TraitClauseId
    r"""Index identifying the clause among other clauses bound at the same level."""
    span: Optional[Span]
    origin: PredicateOrigin
    r"""Where the predicate was written, relative to the item that requires it."""
    trait: RegionBinder[TraitDeclRef]
    r"""The trait that is implemented."""


# A reference to a trait.
# This type is hash-consed, `TraitRefContents` contains the actual data.
TraitRef: TypeAlias = "TraitRefContents"


@dataclass
class TraitRefContents:
    kind: TraitRefKind
    trait_decl_ref: RegionBinder[TraitDeclRef]
    r"""Not necessary, but useful"""


@dataclass
class TraitRefKindTraitImpl:
    r"""A specific top-level implementation item."""
    _0: TraitImplRef

@dataclass
class TraitRefKindClause:
    r"""One of the local clauses.

    Example:
    ```text
    fn f<T>(...) where T : Foo
                       ^^^^^^^
                       Clause(0)
    ```"""
    _0: DeBruijnVar[TraitClauseId]

@dataclass
class TraitRefKindParentClause:
    r"""A parent clause

    Example:
    ```text
    trait Foo1 {}
    trait Foo2 { fn f(); }

    trait Bar : Foo1 + Foo2 {}
                ^^^^   ^^^^
                       parent clause 1
        parent clause 0

    fn g<T : Bar>(x : T) {
      x.f()
      ^^^^^
      Parent(Clause(0), 1)::f(x)
                        ^
                        parent clause 1 of clause 0
    }
    ```"""
    _0: TraitRef
    _1: TraitClauseId

@dataclass
class TraitRefKindItemClause:
    r"""A clause defined on an associated type. This variant is only used during translation; after
    the `lift_associated_item_clauses` pass, clauses on items become `ParentClause`s.

    Example:
    ```text
    trait Foo {
      type W: Bar0 + Bar1 // Bar1 contains a method bar1
                     ^^^^
                  this is the clause 1 applying to W
    }

    fn f<T : Foo>(x : T::W) {
      x.bar1();
      ^^^^^^^
      ItemClause(Clause(0), W, 1)
                            ^^^^
                            clause 1 from item W (from local clause 0)
    }
    ```"""
    _0: TraitRef
    _1: AssocTypeId
    _2: TraitClauseId

@dataclass
class TraitRefKindSelf:
    r"""The implicit `Self: Trait` clause. Present inside trait declarations, including trait
    method declarations. Not present in trait implementations as we can use `TraitImpl` intead."""

@dataclass
class TraitRefKindBuiltinOrAuto:
    r"""A trait implementation that is computed by the compiler, such as for built-in trait
    `Sized`. This morally points to an invisible `impl` block; as such it contains
    the information we may need from one.

    Also used as a placeholder for trait clauses that were stripped by the
    `--remove-adt-clauses` pass: the original `Clause` reference is replaced with a
    `BuiltinOrAuto { builtin_data: RemovedAdtClause, .. }`. See
    [`BuiltinImplData::RemovedAdtClause`]."""
    builtin_data: BuiltinImplData
    r"""Metadata that identifies this impl."""
    parent_trait_refs: list[TraitRef]
    r"""Exactly like the same field on `TraitImpl`: the `TraitRef`s required to satisfy the
    implied predicates on the trait declaration. E.g. since `FnMut: FnOnce`, a built-in `T:
    FnMut` impl would have a `TraitRef` for `T: FnOnce`."""
    types: dict[AssocTypeId, TraitAssocTyImpl]
    r"""The values of the associated types for this trait."""
    vtable: Optional[GlobalDeclRef]
    r"""The vtable value for this builtin implementation, if we generated one."""

@dataclass
class TraitRefKindDyn:
    r"""The automatically-generated implementation for `dyn Trait`."""

@dataclass
class TraitRefKindUnknownTrait:
    r"""For error reporting."""
    _0: str

# Identifier of a trait instance.
# This is derived from the trait resolution.
# Should be read as a path inside the trait clauses which apply to the current
# definition. Note that every path designated by `TraitInstanceId` refers
# to a *trait instance*, which is why the [`TraitRefKind::Clause`] variant may seem redundant
# with some of the other variants.
TraitRefKind: TypeAlias = "Union[TraitRefKindTraitImpl, TraitRefKindClause, TraitRefKindParentClause, TraitRefKindItemClause, TraitRefKindSelf, TraitRefKindBuiltinOrAuto, TraitRefKindDyn, TraitRefKindUnknownTrait]"


@dataclass
class TraitTypeConstraint:
    r"""A constraint over a trait associated type.

    Example:
    ```text
    T : Foo<S = String>
            ^^^^^^^^^^
    ```"""
    trait_ref: TraitRef
    type_id: AssocTypeId
    ty: Ty


@dataclass
class TranslatedCrate:
    r"""The complete data of a Rust crate.

    A crate is mainly composed of 5 kinds of items:
    - Functions;
    - Type definitions;
    - Globals (constants and statics);
    - Trait declarations;
    - Trait implementations.

    These can each be found in the corresponding `IndexVec`. They are in an unspecified (though
    deterministic) order.
    If you need a more robust order, see `ordered_decls`.

    To get a `TranslatedCrate`, run `charon cargo` inside a Rust crate, then deserialize
    the resulting `crate_name.llbc` file using [`crate::deserialize_llbc`]."""
    crate_name: str
    r"""The name of the crate."""
    options: CliOptions
    r"""The options used when calling Charon. Can be used to check that Charon was called with the
    options that a given consumer requires."""
    target_information: list[tuple[str, TargetInfo]]
    r"""Information about each target platform for which the crate was translated. When translating
    a crate normally this will have a single entry; when using `--targets` this will have one
    entry per chosen target."""
    files: list[File]
    r"""The source files composing the crate and its dependencies. Each [`Span`] refers to a byte
    range within one of these files."""
    item_names: list[tuple[ItemId, Name]]
    r"""The names of all registered items. Available so we can know the names even of items that
    failed to translate.
    Invariant: after translation, any existing `ItemId` must have an associated name, even
    if the corresponding item wasn't translated."""
    assoc_item_names: dict[TraitDeclId, AssocItemNames]
    r"""The names of all the registered associated items. Available so we can know the names even
    of items that failed to translate.
    Invariant: after translation, any existing `AssocItemId` must have an associated name, even
    if the corresponding item wasn't translated."""
    short_names: list[tuple[ItemId, Name]]
    r"""Short names, for items whose last PathElem is unique."""
    type_decls: dict[TypeDeclId, TypeDecl]
    r"""The type definitions (structs, enums, ...)."""
    fun_decls: dict[FunDeclId, FunDecl]
    r"""The function definitions.

    Each item with a body becomes a function: actual functions, methods, and unevaluated
    consts/statics."""
    global_decls: dict[GlobalDeclId, GlobalDecl]
    r"""The global definitions, which are constants, statics, and thread locals."""
    trait_decls: dict[TraitDeclId, TraitDecl]
    r"""The trait declarations."""
    trait_impls: dict[TraitImplId, TraitImpl]
    r"""The trait implementations."""
    ordered_decls: Optional[list[DeclarationGroup]]
    r"""This contains a list of all the reachable items in the crate in a stable, logical order
    based on crate and file order, then further grouped and sorted such that every item comes
    after the items it depends on.
    Mutually-dependent groups of items are identified as such.
    This is meant for code-generation tools that want a stable output order.

    Not all the items in the `TranslatedCrate` are included: some trait impls are never
    referred to by reachable items so could in principle be removed from the crate, but we keep
    them around to be able to tell method implementations apart.

    `Some` after translation unless `--no-reorder-decls` is passed."""


# A type.
# This is an interned value; see `TyKind` for the actual contents.
Ty: TypeAlias = "TyKind"


@dataclass
class TyKindTScalar:
    r"""A scalar (integers, floats, `char`, or `bool`)."""
    _0: ScalarType

@dataclass
class TyKindTArray:
    r"""An array `[T; N]`. The third field is the proof that `T: Sized`; it is absent with
    `--hide-marker-traits`."""
    _0: Ty
    _1: ConstantExpr
    _2: Optional[TraitRef]

@dataclass
class TyKindTSlice:
    r"""A slice `[T]`. The second field is the proof that `T: Sized`; it is absent with
    `--hide-marker-traits`."""
    _0: Ty
    _1: Optional[TraitRef]

@dataclass
class TyKindTAdt:
    r"""An ADT: structs, enums, unions, as well as tuples and `str`."""
    _0: TypeDeclRef

@dataclass
class TyKindTRef:
    r"""A reference: `&T` or `&mut T`."""
    _0: Region
    _1: Ty
    _2: RefKind

@dataclass
class TyKindTRawPtr:
    r"""A raw pointer."""
    _0: Ty
    _1: RefKind

@dataclass
class TyKindTFnDef:
    r"""The unique type associated with each function item. Each function item is given a unique
    type that has the function's early-bound generics. This type is not generally nameable in
    Rust; it's a ZST (there's a unique value), and a value of that type can be cast to a
    function pointer or passed to functions that expect `FnOnce`/`FnMut`/`Fn` parameters.

    There's a binder here because charon function items take both early and late-bound
    lifetimes as arguments; given that the type we're pointing to is polymorphic in the
    late-bound variables, we need to bind them here.

    ```rust
    // `'a` is early-bound, 'b is late-bound.
    fn foo<'a, 'b>(x: &'a u32, y: &'b u32)
    where u32: 'b
    {}
    ```
    For rustc, there's a ZST `foo<'a>`, that can be cast to a `for<'b> fn(&'a u32, &'b u32)`
    function pointer.
    For charon, there's an item `foo<'a, 'b>`, and the `FnDef` item that corresponds to rustc's
    `foo<'a>` is represented as `FnDef(for<'b> foo<'a, 'b>)`."""
    _0: RegionBinder[FnPtr]

@dataclass
class TyKindTFnPtr:
    r"""Function pointer type. This is a literal pointer to a region of memory that contains a
    callable function.

    A function pointer can have lifetime generics, e.g. `for<'a> fn(&'a mut u32) -> &'a u32`,
    hence the binder."""
    _0: RegionBinder[FunSig]

@dataclass
class TyKindTDynTrait:
    r"""`dyn Trait`: erased value known to implement `Trait`. A pointer to it will carry a vtable
    pointer that stores the methods that can be called on this value."""
    _0: DynPredicate

@dataclass
class TyKindTPattern:
    r"""A pattern type: a type that is representationally identical to its base type, except the
    only valid values are the ones that match the pattern."""
    _0: Ty
    _1: TypePattern

@dataclass
class TyKindTNever:
    r"""The never type, the canonical uninhabited type."""

@dataclass
class TyKindTVar:
    r"""A type variable."""
    _0: DeBruijnVar[TypeVarId]

@dataclass
class TyKindTTraitType:
    r"""A trait associated type: `<T as Trait>::AssocType<Args>`."""
    _0: TraitRef
    _1: AssocTypeId
    _2: GenericArgs

@dataclass
class TyKindTPtrMetadata:
    r"""The type of pointer metadata for the given type; e.g. for `[T]`, this type is `usize`. The
    way to write this type in Rust is `<X as core::ptr::Pointee>::Metadata`."""
    _0: Ty

@dataclass
class TyKindTError:
    r"""A type that could not be computed or was incorrect."""
    _0: str

# A type.
# This is interned as `Ty`, making it cheap to clone and compare.
TyKind: TypeAlias = "Union[TyKindTScalar, TyKindTArray, TyKindTSlice, TyKindTAdt, TyKindTRef, TyKindTRawPtr, TyKindTFnDef, TyKindTFnPtr, TyKindTDynTrait, TyKindTPattern, TyKindTNever, TyKindTVar, TyKindTTraitType, TyKindTPtrMetadata, TyKindTError]"


@dataclass
class TypeDecl:
    r"""A type declaration.

    Types can be opaque or transparent.

    Transparent types are local types not marked as opaque.
    Opaque types are the others: local types marked as opaque, and non-local
    types (coming from external dependencies).

    In case the type is transparent, the declaration also contains the
    type definition (see [TypeDeclKind]).

    A type can only be an ADT (structure or enumeration), as type aliases are
    inlined in MIR."""
    def_id: TypeDeclId
    item_meta: ItemMeta
    r"""Meta information associated with the item."""
    generics: GenericParams
    src: TypeSource
    r"""The context of the type: distinguishes top-level items from closure-related items etc."""
    kind: TypeDeclKind
    r"""The type kind: enum, struct, or opaque."""
    layout: list[tuple[str, Layout]]
    r"""The layout of the type for each target. Information may be partial because of generics or
    dynamically-sized types. If we cannot compute a layout, the target has no entry."""
    ptr_metadata: PtrMetadata
    r"""The metadata associated with a pointer to the type."""


TypeDeclId = NewType("TypeDeclId", int)


@dataclass
class TypeDeclKindStruct:
    _0: list[Field]

@dataclass
class TypeDeclKindEnum:
    _0: list[Variant]

@dataclass
class TypeDeclKindUnion:
    _0: list[Field]

@dataclass
class TypeDeclKindOpaque:
    r"""An opaque type.

    Either a local type marked as opaque, or an external type."""

@dataclass
class TypeDeclKindAlias:
    r"""An alias to another type. This only shows up in the top-level list of items, as rustc
    inlines uses of type aliases everywhere else."""
    _0: Ty

@dataclass
class TypeDeclKindTDeclError:
    r"""Used if an error happened during the extraction, and we don't panic
    on error."""
    _0: str

TypeDeclKind: TypeAlias = "Union[TypeDeclKindStruct, TypeDeclKindEnum, TypeDeclKindUnion, TypeDeclKindOpaque, TypeDeclKindAlias, TypeDeclKindTDeclError]"


@dataclass
class TypeDeclRef:
    r"""Reference to a type declaration.

    This includes user-defined ADTs (structs, enums, unions), but also tuples,
    boxes, and `str`, which we translate as `struct str([u8])`."""
    id: TypeDeclId
    generics: GenericArgs
    builtin: Optional[BuiltinAdt]
    r"""If this points to a builtin ADT, it is recorded here for easier identification."""


@dataclass
class TypeParam:
    r"""A type variable in a signature or binder."""
    index: TypeVarId
    r"""Index identifying the variable among other variables bound at the same level."""
    name: str
    r"""Variable name"""
    variance: Variance
    r"""Variance of this parameter."""


@dataclass
class TypePatternRange:
    _0: ConstantExpr
    _1: ConstantExpr

@dataclass
class TypePatternOrPattern:
    _0: list[TypePattern]

@dataclass
class TypePatternNotNull:
    pass

# A type-level pattern used by [`TyKind::Pattern`].
TypePattern: TypeAlias = "Union[TypePatternRange, TypePatternOrPattern, TypePatternNotNull]"


@dataclass
class TypeSourceNormalType:
    r"""A normal type declaration."""

@dataclass
class TypeSourceClosureType:
    r"""The struct that carries the captured variables of a closure."""
    info: ClosureInfo

@dataclass
class TypeSourceVTableType:
    r"""Defines the vtable struct for a trait."""
    dyn_predicate: DynPredicate
    r"""The `dyn Trait` predicate implemented by this vtable."""
    field_map: list[VTableField]
    r"""Record what each vtable field means."""
    supertrait_map: list[Optional[FieldId]]
    r"""For each implied clause that is also a supertrait clause, records which field of the
    vtable corresponds to it."""

@dataclass
class TypeSourceBuiltinType:
    r"""A type declaration synthesised for a builtin ADT."""
    _0: BuiltinAdt

# Where a given type came from.
TypeSource: TypeAlias = "Union[TypeSourceNormalType, TypeSourceClosureType, TypeSourceVTableType, TypeSourceBuiltinType]"


TypeVarId = NewType("TypeVarId", int)


@dataclass
class UIntTyUsize:
    pass

@dataclass
class UIntTyU8:
    pass

@dataclass
class UIntTyU16:
    pass

@dataclass
class UIntTyU32:
    pass

@dataclass
class UIntTyU64:
    pass

@dataclass
class UIntTyU128:
    pass

UIntTy: TypeAlias = "Union[UIntTyUsize, UIntTyU8, UIntTyU16, UIntTyU32, UIntTyU64, UIntTyU128]"


@dataclass
class UnopNot:
    pass

@dataclass
class UnopNeg:
    r"""This can overflow, for `-i::MIN`."""
    _0: OverflowMode

@dataclass
class UnopCast:
    r"""Casts are rvalues in MIR, but we treat them as unops."""
    _0: CastKind

# Unary operation
Unop: TypeAlias = "Union[UnopNot, UnopNeg, UnopCast]"


@dataclass
class UnsizingMetadataMetaLength:
    r"""Cast from `[T; N]` to `[T]`."""
    _0: ConstantExpr

@dataclass
class UnsizingMetadataMetaVTable:
    r"""Cast from a sized value to a `dyn Trait` value. The `TraitRef` is the proof of the `dyn
    Trait` predicate; the constant expression is a reference to the vtable `static` value."""
    _0: TraitRef
    _1: ConstantExpr

@dataclass
class UnsizingMetadataMetaVTableUpcast:
    r"""Cast from `dyn Trait` to `dyn OtherTrait`. The fields indicate how to retreive the vtable:
    it's always either the same we already had, or the vtable for a (possibly nested) supertrait.

    Note that we cheat in one case: when upcasting to a marker trait (e.g. `dyn Trait -> dyn
    Sized`), we keep the current vtable."""
    _0: list[FieldId]

@dataclass
class UnsizingMetadataMetaUnknown:
    pass

UnsizingMetadata: TypeAlias = "Union[UnsizingMetadataMetaLength, UnsizingMetadataMetaVTable, UnsizingMetadataMetaVTableUpcast, UnsizingMetadataMetaUnknown]"


@dataclass
class VTableFieldVTableSize:
    pass

@dataclass
class VTableFieldVTableAlign:
    pass

@dataclass
class VTableFieldVTableDrop:
    pass

@dataclass
class VTableFieldVTableMethod:
    _0: TraitMethodId

@dataclass
class VTableFieldVTableSuperTrait:
    _0: TraitClauseId

VTableField: TypeAlias = "Union[VTableFieldVTableSize, VTableFieldVTableAlign, VTableFieldVTableDrop, VTableFieldVTableMethod, VTableFieldVTableSuperTrait]"


@dataclass
class VarianceCovariant:
    pass

@dataclass
class VarianceInvariant:
    pass

@dataclass
class VarianceContravariant:
    pass

@dataclass
class VarianceBivariant:
    pass

@dataclass
class VarianceVaUnknown:
    r"""Variance was not sensible (e.g. on impls), not available (e.g. on higher-kinded
    predicates), or not computed (e.g. on parameters that Charon invents)."""

# The variance of a lifetime or type parameter.
Variance: TypeAlias = "Union[VarianceCovariant, VarianceInvariant, VarianceContravariant, VarianceBivariant, VarianceVaUnknown]"


@dataclass
class Variant:
    id: VariantId
    span: Span
    attr_info: AttrInfo
    variant_name: str
    fields: list[Field]
    discriminant: IntegerValue
    r"""The discriminant value outputted by `std::mem::discriminant` for this variant. This can be
    different than the value stored in memory (called `tag`); that one is described by
    [`Discriminator`] and [`VariantLayout::tagger`]."""


VariantId = NewType("VariantId", int)


@dataclass
class VariantLayout:
    r"""Simplified layout of a single variant.

    Maps fields to their offset within the layout."""
    field_offsets: list[OffsetExpr]
    r"""The offset of each field."""
    uninhabited: bool
    r"""Whether the variant is uninhabited, i.e. has any valid possible value.
    Note that uninhabited types can have arbitrary layouts."""
    tagger: list[tuple[int, IntegerValue]]
    r"""How to write the tag when constructing this variant. Each entry means: write `value` at
    byte `offset`. Mirrors MiniRust's `Variant::tagger`."""


@dataclass
class WithRetagNoRetag:
    pass

@dataclass
class WithRetagYesRetag:
    pass

# Used for [`Rvalue::Use`] to indicate whether the operand should be retagged (this is used
# for Rust's aliasing model).
WithRetag: TypeAlias = "Union[WithRetagNoRetag, WithRetagYesRetag]"

