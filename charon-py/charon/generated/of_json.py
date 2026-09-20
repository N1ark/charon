"""WARNING: this file is partially auto-generated. Do not edit `of_json.py` by hand. Edit
`generate_py/templates/of_json.py` instead, or improve the code generation tool so as to avoid the
need for hand-writing things.

`generate_py/templates/of_json.py` contains the manual definitions and some `# __REPLACEn__`
comments. These comments are replaced by auto-generated definitions by running `make
generate-asts` in the crate root. The code-generation code is in `charon/src/bin/generate-asts`.
"""

from __future__ import annotations

import json as _json
import os
from dataclasses import dataclass, field

from ..errors import DeserializeError, unknown_variant
from ..json_basic import *
from ..postcard_basic import InputFormat, format_hint
from ..version import SUPPORTED_CHARON_VERSION
from .types import *


@dataclass
class OfJsonCtx:
    """The state threaded through the deserializers.

    Files are serialized once and referred to by id afterwards, and values that come up often are
    deduplicated the same way; these tables hold what we have read so far.
    """

    files: dict[int, File] = field(default_factory=dict)
    ty_kind_dedup: dict[int, TyKind] = field(default_factory=dict)
    trait_ref_contents_dedup: dict[int, TraitRefContents] = field(default_factory=dict)
    constant_expr_dedup: dict[int, ConstantExpr] = field(default_factory=dict)
    exact_size_expr_kind_dedup: dict[int, ExactSizeExprKind] = field(default_factory=dict)
    span_dedup: dict[int, Span] = field(default_factory=dict)


def abi_of_json(ctx: OfJsonCtx, js: Json) -> Abi:
    __tag, __payload = split_variant(js)
    if __tag == "Rust":
        return AbiRust()
    if __tag == "C":
        return AbiC()
    if __tag == "Other":
        _0 = string_of_json(ctx, __payload)
        return AbiOther(_0)
    raise unknown_variant("Abi", __tag)

def abort_kind_of_json(ctx: OfJsonCtx, js: Json) -> AbortKind:
    __tag, __payload = split_variant(js)
    if __tag == "Panic":
        _0 = option_of_json(name_of_json)(ctx, __payload)
        return AbortKindPanic(_0)
    if __tag == "UndefinedBehavior":
        return AbortKindUndefinedBehavior()
    if __tag == "UnwindTerminate":
        return AbortKindUnwindTerminate()
    raise unknown_variant("AbortKind", __tag)

def aggregate_kind_of_json(ctx: OfJsonCtx, js: Json) -> AggregateKind:
    __tag, __payload = split_variant(js)
    if __tag == "Adt":
        __items = expect_list(__payload, 3)
        _0 = type_decl_ref_of_json(ctx, __items[0])
        _1 = option_of_json(variant_id_of_json)(ctx, __items[1])
        _2 = option_of_json(field_id_of_json)(ctx, __items[2])
        return AggregateKindAggregatedAdt(_0, _1, _2)
    if __tag == "Array":
        __items = expect_list(__payload, 3)
        _0 = ty_of_json(ctx, __items[0])
        _1 = constant_expr_of_json(ctx, __items[1])
        _2 = option_of_json(trait_ref_of_json)(ctx, __items[2])
        return AggregateKindAggregatedArray(_0, _1, _2)
    if __tag == "RawPtr":
        __items = expect_list(__payload, 2)
        _0 = ty_of_json(ctx, __items[0])
        _1 = ref_kind_of_json(ctx, __items[1])
        return AggregateKindAggregatedRawPtr(_0, _1)
    raise unknown_variant("AggregateKind", __tag)

def alignment_modifier_of_json(ctx: OfJsonCtx, js: Json) -> AlignmentModifier:
    __tag, __payload = split_variant(js)
    if __tag == "Align":
        _0 = int_of_json(ctx, __payload)
        return AlignmentModifierAlign(_0)
    if __tag == "Pack":
        _0 = int_of_json(ctx, __payload)
        return AlignmentModifierPack(_0)
    raise unknown_variant("AlignmentModifier", __tag)

def assertion_of_json(ctx: OfJsonCtx, js: Json) -> Assertion:
    __fields = expect_object(js)
    cond = operand_of_json(ctx, __fields["cond"])
    expected = bool_of_json(ctx, __fields["expected"])
    check_kind = option_of_json(builtin_assert_kind_of_json)(ctx, __fields["check_kind"])
    return Assertion(cond, expected, check_kind)

def assoc_const_id_of_json(ctx: OfJsonCtx, js: Json) -> AssocConstId:
    return AssocConstId(int_of_json(ctx, js))

def assoc_item_id_of_json(ctx: OfJsonCtx, js: Json) -> AssocItemId:
    __tag, __payload = split_variant(js)
    if __tag == "Type":
        _0 = assoc_type_id_of_json(ctx, __payload)
        return AssocItemIdAssocIdType(_0)
    if __tag == "Method":
        _0 = trait_method_id_of_json(ctx, __payload)
        return AssocItemIdAssocIdMethod(_0)
    if __tag == "Const":
        _0 = assoc_const_id_of_json(ctx, __payload)
        return AssocItemIdAssocIdConst(_0)
    raise unknown_variant("AssocItemId", __tag)

def assoc_item_names_of_json(ctx: OfJsonCtx, js: Json) -> AssocItemNames:
    __fields = expect_object(js)
    types = list_of_json(trait_item_name_of_json)(ctx, __fields["types"])
    methods = list_of_json(trait_item_name_of_json)(ctx, __fields["methods"])
    consts = list_of_json(trait_item_name_of_json)(ctx, __fields["consts"])
    return AssocItemNames(types, methods, consts)

def assoc_type_id_of_json(ctx: OfJsonCtx, js: Json) -> AssocTypeId:
    return AssocTypeId(int_of_json(ctx, js))

def attr_info_of_json(ctx: OfJsonCtx, js: Json) -> AttrInfo:
    __fields = expect_object(js)
    attributes = list_of_json(attribute_of_json)(ctx, __fields["attributes"])
    inline = option_of_json(inline_attr_of_json)(ctx, __fields["inline"])
    rename = option_of_json(string_of_json)(ctx, __fields["rename"])
    public = bool_of_json(ctx, __fields["public"])
    return AttrInfo(attributes, inline, rename, public)

def attribute_of_json(ctx: OfJsonCtx, js: Json) -> Attribute:
    __tag, __payload = split_variant(js)
    if __tag == "Opaque":
        return AttributeAttrOpaque()
    if __tag == "Exclude":
        return AttributeAttrExclude()
    if __tag == "Rename":
        _0 = string_of_json(ctx, __payload)
        return AttributeAttrRename(_0)
    if __tag == "VariantsPrefix":
        _0 = string_of_json(ctx, __payload)
        return AttributeAttrVariantsPrefix(_0)
    if __tag == "VariantsSuffix":
        _0 = string_of_json(ctx, __payload)
        return AttributeAttrVariantsSuffix(_0)
    if __tag == "Transparent":
        return AttributeAttrTransparent()
    if __tag == "IsContract":
        __fields = expect_object(__payload)
        kind = string_of_json(ctx, __fields["kind"])
        target = maybe_assoc_item_id_of_json(ctx, __fields["target"])
        return AttributeAttrIsContract(kind, target)
    if __tag == "HasContract":
        __fields = expect_object(__payload)
        kind = string_of_json(ctx, __fields["kind"])
        contract = fun_decl_id_of_json(ctx, __fields["contract"])
        return AttributeAttrHasContract(kind, contract)
    if __tag == "DocComment":
        _0 = string_of_json(ctx, __payload)
        return AttributeAttrDocComment(_0)
    if __tag == "Builtin":
        _0 = rustc_attribute_kind_of_json(ctx, __payload)
        return AttributeAttrBuiltin(_0)
    if __tag == "Unknown":
        _0 = raw_attribute_of_json(ctx, __payload)
        return AttributeAttrUnknown(_0)
    raise unknown_variant("Attribute", __tag)

def rustc_attribute_kind_of_json(ctx: OfJsonCtx, js: Json) -> RustcAttributeKind:
    __tag, __payload = split_variant(js)
    if __tag == "AutomaticallyDerived":
        return RustcAttributeKindAutomaticallyDerived()
    if __tag == "Cold":
        return RustcAttributeKindCold()
    if __tag == "Deprecated":
        __fields = expect_object(__payload)
        deprecation = rustc_deprecation_of_json(ctx, __fields["deprecation"])
        span = span_of_json(ctx, __fields["span"])
        return RustcAttributeKindDeprecated(deprecation, span)
    if __tag == "Fundamental":
        return RustcAttributeKindFundamental()
    if __tag == "Ignore":
        __fields = expect_object(__payload)
        span = span_of_json(ctx, __fields["span"])
        reason = option_of_json(string_of_json)(ctx, __fields["reason"])
        return RustcAttributeKindIgnore(span, reason)
    if __tag == "Inline":
        __items = expect_list(__payload, 2)
        _0 = rustc_inline_attr_of_json(ctx, __items[0])
        _1 = span_of_json(ctx, __items[1])
        return RustcAttributeKindInline(_0, _1)
    if __tag == "MayDangle":
        _0 = span_of_json(ctx, __payload)
        return RustcAttributeKindMayDangle(_0)
    if __tag == "Naked":
        _0 = span_of_json(ctx, __payload)
        return RustcAttributeKindNaked(_0)
    if __tag == "NoLink":
        return RustcAttributeKindNoLink()
    if __tag == "NoMangle":
        _0 = span_of_json(ctx, __payload)
        return RustcAttributeKindNoMangle(_0)
    if __tag == "NonExhaustive":
        _0 = span_of_json(ctx, __payload)
        return RustcAttributeKindNonExhaustive(_0)
    if __tag == "Optimize":
        __items = expect_list(__payload, 2)
        _0 = rustc_optimize_attr_of_json(ctx, __items[0])
        _1 = span_of_json(ctx, __items[1])
        return RustcAttributeKindOptimize(_0, _1)
    if __tag == "RustcAlign":
        __fields = expect_object(__payload)
        align = int_of_json(ctx, __fields["align"])
        span = span_of_json(ctx, __fields["span"])
        return RustcAttributeKindRustcAlign(align, span)
    if __tag == "RustcIntrinsic":
        return RustcAttributeKindRustcIntrinsic()
    if __tag == "RustcTestEntrypointMarker":
        return RustcAttributeKindRustcTestEntrypointMarker()
    if __tag == "ShouldPanic":
        __fields = expect_object(__payload)
        reason = option_of_json(string_of_json)(ctx, __fields["reason"])
        return RustcAttributeKindShouldPanic(reason)
    if __tag == "TargetFeature":
        __fields = expect_object(__payload)
        features = list_of_json(pair_of_json(string_of_json, span_of_json))(ctx, __fields["features"])
        attr_span = span_of_json(ctx, __fields["attr_span"])
        was_forced = bool_of_json(ctx, __fields["was_forced"])
        return RustcAttributeKindTargetFeature(features, attr_span, was_forced)
    if __tag == "TrackCaller":
        _0 = span_of_json(ctx, __payload)
        return RustcAttributeKindTrackCaller(_0)
    raise unknown_variant("RustcAttributeKind", __tag)

def binop_of_json(ctx: OfJsonCtx, js: Json) -> Binop:
    __tag, __payload = split_variant(js)
    if __tag == "BitXor":
        return BinopBitXor()
    if __tag == "BitAnd":
        return BinopBitAnd()
    if __tag == "BitOr":
        return BinopBitOr()
    if __tag == "Eq":
        return BinopEq()
    if __tag == "Lt":
        return BinopLt()
    if __tag == "Le":
        return BinopLe()
    if __tag == "Ne":
        return BinopNe()
    if __tag == "Ge":
        return BinopGe()
    if __tag == "Gt":
        return BinopGt()
    if __tag == "Add":
        _0 = overflow_mode_of_json(ctx, __payload)
        return BinopAdd(_0)
    if __tag == "Sub":
        _0 = overflow_mode_of_json(ctx, __payload)
        return BinopSub(_0)
    if __tag == "Mul":
        _0 = overflow_mode_of_json(ctx, __payload)
        return BinopMul(_0)
    if __tag == "Div":
        _0 = overflow_mode_of_json(ctx, __payload)
        return BinopDiv(_0)
    if __tag == "Rem":
        _0 = overflow_mode_of_json(ctx, __payload)
        return BinopRem(_0)
    if __tag == "AddChecked":
        return BinopAddChecked()
    if __tag == "SubChecked":
        return BinopSubChecked()
    if __tag == "MulChecked":
        return BinopMulChecked()
    if __tag == "Shl":
        _0 = overflow_mode_of_json(ctx, __payload)
        return BinopShl(_0)
    if __tag == "Shr":
        _0 = overflow_mode_of_json(ctx, __payload)
        return BinopShr(_0)
    if __tag == "Offset":
        return BinopOffset()
    if __tag == "Cmp":
        return BinopCmp()
    raise unknown_variant("Binop", __tag)

def binder_of_json(arg0_of_json: JsonDecoder[T0]) -> JsonDecoder[Binder[T0]]:
    def read(ctx: OfJsonCtx, js: Json) -> Binder[T0]:
        __fields = expect_object(js)
        binder_params = generic_params_of_json(ctx, __fields["params"])
        binder_value = arg0_of_json(ctx, __fields["skip_binder"])
        return Binder(binder_params, binder_value)
    return read

def binder_kind_of_json(ctx: OfJsonCtx, js: Json) -> BinderKind:
    __tag, __payload = split_variant(js)
    if __tag == "TraitType":
        __items = expect_list(__payload, 2)
        _0 = trait_decl_id_of_json(ctx, __items[0])
        _1 = assoc_type_id_of_json(ctx, __items[1])
        return BinderKindBKTraitType(_0, _1)
    if __tag == "TraitMethod":
        __items = expect_list(__payload, 2)
        _0 = trait_decl_id_of_json(ctx, __items[0])
        _1 = trait_method_id_of_json(ctx, __items[1])
        return BinderKindBKTraitMethod(_0, _1)
    if __tag == "InherentImplBlock":
        return BinderKindBKInherentImplBlock()
    if __tag == "Dyn":
        return BinderKindBKDyn()
    if __tag == "Other":
        return BinderKindBKOther()
    raise unknown_variant("BinderKind", __tag)

def llbc_block_of_json(ctx: OfJsonCtx, js: Json) -> LlbcBlock:
    __fields = expect_object(js)
    span = span_of_json(ctx, __fields["span"])
    block_id = llbc_block_id_of_json(ctx, __fields["id"])
    statements = list_of_json(llbc_statement_of_json)(ctx, __fields["statements"])
    return LlbcBlock(span, block_id, statements)

def ullbc_block_of_json(ctx: OfJsonCtx, js: Json) -> UllbcBlock:
    __fields = expect_object(js)
    statements = list_of_json(ullbc_statement_of_json)(ctx, __fields["statements"])
    terminator = terminator_of_json(ctx, __fields["terminator"])
    return UllbcBlock(statements, terminator)

def ullbc_block_id_of_json(ctx: OfJsonCtx, js: Json) -> UllbcBlockId:
    return UllbcBlockId(int_of_json(ctx, js))

def llbc_block_id_of_json(ctx: OfJsonCtx, js: Json) -> LlbcBlockId:
    return LlbcBlockId(int_of_json(ctx, js))

def body_of_json(ctx: OfJsonCtx, js: Json) -> Body:
    __tag, __payload = split_variant(js)
    if __tag == "Unstructured":
        _0 = gexpr_body_of_json(list_of_json(ullbc_block_of_json))(ctx, __payload)
        return BodyUnstructuredBody(_0)
    if __tag == "Structured":
        _0 = gexpr_body_of_json(llbc_block_of_json)(ctx, __payload)
        return BodyStructuredBody(_0)
    if __tag == "TargetDispatch":
        _0 = list_of_json(key_value_pair_of_json(string_of_json, fun_decl_ref_of_json))(ctx, __payload)
        return BodyTargetDispatchBody(_0)
    if __tag == "Extern":
        _0 = string_of_json(ctx, __payload)
        return BodyExternBody(_0)
    if __tag == "Intrinsic":
        __fields = expect_object(__payload)
        name = string_of_json(ctx, __fields["name"])
        arg_names = list_of_json(option_of_json(string_of_json))(ctx, __fields["arg_names"])
        return BodyIntrinsicBody(name, arg_names)
    if __tag == "Opaque":
        return BodyOpaqueBody()
    if __tag == "Missing":
        return BodyMissingBody()
    if __tag == "Error":
        _0 = error_of_json(ctx, __payload)
        return BodyErrorBody(_0)
    raise unknown_variant("Body", __tag)

def borrow_kind_of_json(ctx: OfJsonCtx, js: Json) -> BorrowKind:
    __tag, __payload = split_variant(js)
    if __tag == "Shared":
        return BorrowKindBShared()
    if __tag == "Mut":
        return BorrowKindBMut()
    if __tag == "TwoPhaseMut":
        return BorrowKindBTwoPhaseMut()
    if __tag == "Shallow":
        return BorrowKindBShallow()
    if __tag == "UniqueImmutable":
        return BorrowKindBUniqueImmutable()
    raise unknown_variant("BorrowKind", __tag)

def borrowck_statement_of_json(ctx: OfJsonCtx, js: Json) -> BorrowckStatement:
    __tag, __payload = split_variant(js)
    if __tag == "FakeRead":
        _0 = place_of_json(ctx, __payload)
        return BorrowckStatementFakeRead(_0)
    if __tag == "SetType":
        __fields = expect_object(__payload)
        place = place_of_json(ctx, __fields["place"])
        ty = ty_of_json(ctx, __fields["ty"])
        variance = variance_of_json(ctx, __fields["variance"])
        return BorrowckStatementSetType(place, ty, variance)
    if __tag == "SetOutlives":
        __items = expect_list(__payload, 2)
        _0 = ty_of_json(ctx, __items[0])
        _1 = region_of_json(ctx, __items[1])
        return BorrowckStatementSetOutlives(_0, _1)
    if __tag == "PredicateHolds":
        _0 = trait_ref_of_json(ctx, __payload)
        return BorrowckStatementPredicateHolds(_0)
    raise unknown_variant("BorrowckStatement", __tag)

def branch_id_of_json(ctx: OfJsonCtx, js: Json) -> BranchId:
    return BranchId(int_of_json(ctx, js))

def builtin_adt_of_json(ctx: OfJsonCtx, js: Json) -> BuiltinAdt:
    __tag, __payload = split_variant(js)
    if __tag == "Tuple":
        return BuiltinAdtTTuple()
    if __tag == "Box":
        return BuiltinAdtTBox()
    if __tag == "Str":
        return BuiltinAdtTStr()
    raise unknown_variant("BuiltinAdt", __tag)

def builtin_assert_kind_of_json(ctx: OfJsonCtx, js: Json) -> BuiltinAssertKind:
    __tag, __payload = split_variant(js)
    if __tag == "BoundsCheck":
        __fields = expect_object(__payload)
        len = operand_of_json(ctx, __fields["len"])
        index = operand_of_json(ctx, __fields["index"])
        return BuiltinAssertKindBoundsCheck(len, index)
    if __tag == "Overflow":
        __items = expect_list(__payload, 3)
        _0 = binop_of_json(ctx, __items[0])
        _1 = operand_of_json(ctx, __items[1])
        _2 = operand_of_json(ctx, __items[2])
        return BuiltinAssertKindOverflow(_0, _1, _2)
    if __tag == "OverflowNeg":
        _0 = operand_of_json(ctx, __payload)
        return BuiltinAssertKindOverflowNeg(_0)
    if __tag == "DivisionByZero":
        _0 = operand_of_json(ctx, __payload)
        return BuiltinAssertKindDivisionByZero(_0)
    if __tag == "RemainderByZero":
        _0 = operand_of_json(ctx, __payload)
        return BuiltinAssertKindRemainderByZero(_0)
    if __tag == "MisalignedPointerDereference":
        __fields = expect_object(__payload)
        required = operand_of_json(ctx, __fields["required"])
        found = operand_of_json(ctx, __fields["found"])
        return BuiltinAssertKindMisalignedPointerDereference(required, found)
    if __tag == "NullPointerDereference":
        return BuiltinAssertKindNullPointerDereference()
    if __tag == "NullReferenceCreated":
        return BuiltinAssertKindNullReferenceCreated()
    if __tag == "InvalidEnumConstruction":
        _0 = operand_of_json(ctx, __payload)
        return BuiltinAssertKindInvalidEnumConstruction(_0)
    if __tag == "ResumedAfterReturn":
        return BuiltinAssertKindResumedAfterReturn()
    if __tag == "ResumedAfterPanic":
        return BuiltinAssertKindResumedAfterPanic()
    if __tag == "ResumedAfterDrop":
        return BuiltinAssertKindResumedAfterDrop()
    raise unknown_variant("BuiltinAssertKind", __tag)

def builtin_impl_data_of_json(ctx: OfJsonCtx, js: Json) -> BuiltinImplData:
    __tag, __payload = split_variant(js)
    if __tag == "Auto":
        return BuiltinImplDataBuiltinAuto()
    if __tag == "Sized":
        return BuiltinImplDataBuiltinSized()
    if __tag == "MetaSized":
        return BuiltinImplDataBuiltinMetaSized()
    if __tag == "PointeeSized":
        return BuiltinImplDataBuiltinPointeeSized()
    if __tag == "Copy":
        return BuiltinImplDataBuiltinCopy()
    if __tag == "Clone":
        return BuiltinImplDataBuiltinClone()
    if __tag == "Tuple":
        return BuiltinImplDataBuiltinTuple()
    if __tag == "Transmute":
        return BuiltinImplDataBuiltinTransmute()
    if __tag == "Unsize":
        return BuiltinImplDataBuiltinUnsize()
    if __tag == "Pointee":
        return BuiltinImplDataBuiltinPointee()
    if __tag == "DiscriminantKind":
        return BuiltinImplDataBuiltinDiscriminantKind()
    if __tag == "Fn":
        return BuiltinImplDataBuiltinFn()
    if __tag == "FnMut":
        return BuiltinImplDataBuiltinFnMut()
    if __tag == "FnOnce":
        return BuiltinImplDataBuiltinFnOnce()
    if __tag == "FnPtr":
        return BuiltinImplDataBuiltinFnPtr()
    if __tag == "AsyncFn":
        return BuiltinImplDataBuiltinAsyncFn()
    if __tag == "AsyncFnMut":
        return BuiltinImplDataBuiltinAsyncFnMut()
    if __tag == "AsyncFnOnce":
        return BuiltinImplDataBuiltinAsyncFnOnce()
    if __tag == "Coroutine":
        return BuiltinImplDataBuiltinCoroutine()
    if __tag == "Future":
        return BuiltinImplDataBuiltinFuture()
    if __tag == "TryAsDynCompatible":
        return BuiltinImplDataBuiltinTryAsDynCompatible()
    if __tag == "NoopDestruct":
        return BuiltinImplDataBuiltinNoopDestruct()
    if __tag == "UntrackedDestruct":
        return BuiltinImplDataBuiltinUntrackedDestruct()
    if __tag == "RemovedAdtClause":
        return BuiltinImplDataBuiltinRemovedAdtClause()
    raise unknown_variant("BuiltinImplData", __tag)

def builtin_path_elem_of_json(ctx: OfJsonCtx, js: Json) -> BuiltinPathElem:
    __tag, __payload = split_variant(js)
    if __tag == "Tuple":
        _0 = int_of_json(ctx, __payload)
        return BuiltinPathElemPeTuple(_0)
    if __tag == "Str":
        return BuiltinPathElemPeStr()
    if __tag == "Closure":
        return BuiltinPathElemPeClosure()
    if __tag == "Use":
        return BuiltinPathElemPeUse()
    if __tag == "AnonConst":
        return BuiltinPathElemPeAnonConst()
    if __tag == "PromotedConst":
        return BuiltinPathElemPePromotedConst()
    if __tag == "ClosureAsFn":
        return BuiltinPathElemPeClosureAsFn()
    if __tag == "DropGlue":
        return BuiltinPathElemPeDropGlue()
    if __tag == "VTable":
        return BuiltinPathElemPeVTable()
    if __tag == "VTableMethod":
        return BuiltinPathElemPeVTableMethod()
    if __tag == "VTableDropShim":
        return BuiltinPathElemPeVTableDropShim()
    raise unknown_variant("BuiltinPathElem", __tag)

def byte_of_json(ctx: OfJsonCtx, js: Json) -> Byte:
    __tag, __payload = split_variant(js)
    if __tag == "Uninit":
        return ByteUninit()
    if __tag == "Value":
        _0 = int_of_json(ctx, __payload)
        return ByteValue(_0)
    if __tag == "Provenance":
        __items = expect_list(__payload, 2)
        _0 = provenance_of_json(ctx, __items[0])
        _1 = int_of_json(ctx, __items[1])
        return ByteProvenance(_0, _1)
    raise unknown_variant("Byte", __tag)

def call_of_json(ctx: OfJsonCtx, js: Json) -> Call:
    __fields = expect_object(js)
    func = fn_operand_of_json(ctx, __fields["func"])
    args = list_of_json(operand_of_json)(ctx, __fields["args"])
    dest = place_of_json(ctx, __fields["dest"])
    return Call(func, args, dest)

def cast_kind_of_json(ctx: OfJsonCtx, js: Json) -> CastKind:
    __tag, __payload = split_variant(js)
    if __tag == "Scalar":
        __items = expect_list(__payload, 2)
        _0 = scalar_type_of_json(ctx, __items[0])
        _1 = scalar_type_of_json(ctx, __items[1])
        return CastKindCastScalar(_0, _1)
    if __tag == "RawPtr":
        __items = expect_list(__payload, 2)
        _0 = ty_of_json(ctx, __items[0])
        _1 = ty_of_json(ctx, __items[1])
        return CastKindCastRawPtr(_0, _1)
    if __tag == "FnPtr":
        __items = expect_list(__payload, 2)
        _0 = ty_of_json(ctx, __items[0])
        _1 = ty_of_json(ctx, __items[1])
        return CastKindCastFnPtr(_0, _1)
    if __tag == "Unsize":
        __items = expect_list(__payload, 3)
        _0 = ty_of_json(ctx, __items[0])
        _1 = ty_of_json(ctx, __items[1])
        _2 = unsizing_metadata_of_json(ctx, __items[2])
        return CastKindCastUnsize(_0, _1, _2)
    if __tag == "Transmute":
        __items = expect_list(__payload, 2)
        _0 = ty_of_json(ctx, __items[0])
        _1 = ty_of_json(ctx, __items[1])
        return CastKindCastTransmute(_0, _1)
    if __tag == "Concretize":
        __items = expect_list(__payload, 2)
        _0 = ty_of_json(ctx, __items[0])
        _1 = ty_of_json(ctx, __items[1])
        return CastKindCastConcretize(_0, _1)
    raise unknown_variant("CastKind", __tag)

def cli_options_of_json(ctx: OfJsonCtx, js: Json) -> CliOptions:
    __fields = expect_object(js)
    ullbc = bool_of_json(ctx, __fields["ullbc"])
    precise_drops = bool_of_json(ctx, __fields["precise_drops"])
    mir = option_of_json(mir_level_of_json)(ctx, __fields["mir"])
    rustc_args = list_of_json(string_of_json)(ctx, __fields["rustc_args"])
    targets = list_of_json(string_of_json)(ctx, __fields["targets"])
    sysroot = option_of_json(string_of_json)(ctx, __fields["sysroot"])
    monomorphize = bool_of_json(ctx, __fields["monomorphize"])
    monomorphize_mut = option_of_json(monomorphize_mut_of_json)(ctx, __fields["monomorphize_mut"])
    start_from = list_of_json(string_of_json)(ctx, __fields["start_from"])
    start_from_if_exists = list_of_json(string_of_json)(ctx, __fields["start_from_if_exists"])
    start_from_attribute = list_of_json(string_of_json)(ctx, __fields["start_from_attribute"])
    start_from_pub = bool_of_json(ctx, __fields["start_from_pub"])
    included = list_of_json(string_of_json)(ctx, __fields["include"])
    opaque = list_of_json(string_of_json)(ctx, __fields["opaque"])
    exclude = list_of_json(string_of_json)(ctx, __fields["exclude"])
    extract_opaque_bodies = bool_of_json(ctx, __fields["extract_opaque_bodies"])
    translate_all_methods = bool_of_json(ctx, __fields["translate_all_methods"])
    duplicate_defaulted_methods = bool_of_json(ctx, __fields["duplicate_defaulted_methods"])
    lift_associated_types = list_of_json(string_of_json)(ctx, __fields["lift_associated_types"])
    hide_marker_traits = bool_of_json(ctx, __fields["hide_marker_traits"])
    hide_allocator = bool_of_json(ctx, __fields["hide_allocator"])
    remove_unused_clauses = bool_of_json(ctx, __fields["remove_unused_clauses"])
    remove_unused_self_clauses = bool_of_json(ctx, __fields["remove_unused_self_clauses"])
    remove_adt_clauses = bool_of_json(ctx, __fields["remove_adt_clauses"])
    desugar_drops = bool_of_json(ctx, __fields["desugar_drops"])
    ops_to_function_calls = bool_of_json(ctx, __fields["ops_to_function_calls"])
    index_to_function_calls = bool_of_json(ctx, __fields["index_to_function_calls"])
    treat_box_as_builtin = bool_of_json(ctx, __fields["treat_box_as_builtin"])
    no_gen_tuple_structs = bool_of_json(ctx, __fields["no_gen_tuple_structs"])
    raw_consts = bool_of_json(ctx, __fields["raw_consts"])
    consts = option_of_json(const_handling_of_json)(ctx, __fields["consts"])
    unsized_strings = bool_of_json(ctx, __fields["unsized_strings"])
    reconstruct_fallible_operations = bool_of_json(ctx, __fields["reconstruct_fallible_operations"])
    reconstruct_asserts = bool_of_json(ctx, __fields["reconstruct_asserts"])
    reconstruct_matches = bool_of_json(ctx, __fields["reconstruct_matches"])
    deallocate_all_locals = bool_of_json(ctx, __fields["deallocate_all_locals"])
    unbind_item_vars = bool_of_json(ctx, __fields["unbind_item_vars"])
    print_original_ullbc = bool_of_json(ctx, __fields["print_original_ullbc"])
    print_ullbc = bool_of_json(ctx, __fields["print_ullbc"])
    print_built_llbc = bool_of_json(ctx, __fields["print_built_llbc"])
    print_llbc = bool_of_json(ctx, __fields["print_llbc"])
    dest_dir = option_of_json(string_of_json)(ctx, __fields["dest_dir"])
    dest_file = option_of_json(string_of_json)(ctx, __fields["dest_file"])
    no_dedup_serialized_ast = bool_of_json(ctx, __fields["no_dedup_serialized_ast"])
    format = option_of_json(serialization_format_arg_of_json)(ctx, __fields["format"])
    no_serialize = bool_of_json(ctx, __fields["no_serialize"])
    skip_borrowck = bool_of_json(ctx, __fields["skip_borrowck"])
    no_typecheck = bool_of_json(ctx, __fields["no_typecheck"])
    no_normalize = bool_of_json(ctx, __fields["no_normalize"])
    no_reorder_decls = bool_of_json(ctx, __fields["no_reorder_decls"])
    abort_on_error = bool_of_json(ctx, __fields["abort_on_error"])
    error_on_warnings = bool_of_json(ctx, __fields["error_on_warnings"])
    preset = option_of_json(preset_of_json)(ctx, __fields["preset"])
    return CliOptions(ullbc, precise_drops, mir, rustc_args, targets, sysroot, monomorphize, monomorphize_mut, start_from, start_from_if_exists, start_from_attribute, start_from_pub, included, opaque, exclude, extract_opaque_bodies, translate_all_methods, duplicate_defaulted_methods, lift_associated_types, hide_marker_traits, hide_allocator, remove_unused_clauses, remove_unused_self_clauses, remove_adt_clauses, desugar_drops, ops_to_function_calls, index_to_function_calls, treat_box_as_builtin, no_gen_tuple_structs, raw_consts, consts, unsized_strings, reconstruct_fallible_operations, reconstruct_asserts, reconstruct_matches, deallocate_all_locals, unbind_item_vars, print_original_ullbc, print_ullbc, print_built_llbc, print_llbc, dest_dir, dest_file, no_dedup_serialized_ast, format, no_serialize, skip_borrowck, no_typecheck, no_normalize, no_reorder_decls, abort_on_error, error_on_warnings, preset)

def closure_info_of_json(ctx: OfJsonCtx, js: Json) -> ClosureInfo:
    __fields = expect_object(js)
    kind = closure_kind_of_json(ctx, __fields["kind"])
    fn_once_impl = region_binder_of_json(trait_impl_ref_of_json)(ctx, __fields["fn_once_impl"])
    fn_mut_impl = option_of_json(region_binder_of_json(trait_impl_ref_of_json))(ctx, __fields["fn_mut_impl"])
    fn_impl = option_of_json(region_binder_of_json(trait_impl_ref_of_json))(ctx, __fields["fn_impl"])
    signature = region_binder_of_json(fun_sig_of_json)(ctx, __fields["signature"])
    return ClosureInfo(kind, fn_once_impl, fn_mut_impl, fn_impl, signature)

def closure_kind_of_json(ctx: OfJsonCtx, js: Json) -> ClosureKind:
    __tag, __payload = split_variant(js)
    if __tag == "Fn":
        return ClosureKindFn()
    if __tag == "FnMut":
        return ClosureKindFnMut()
    if __tag == "FnOnce":
        return ClosureKindFnOnce()
    raise unknown_variant("ClosureKind", __tag)

def const_generic_param_of_json(ctx: OfJsonCtx, js: Json) -> ConstGenericParam:
    __fields = expect_object(js)
    index = const_generic_var_id_of_json(ctx, __fields["index"])
    name = string_of_json(ctx, __fields["name"])
    ty = ty_of_json(ctx, __fields["ty"])
    return ConstGenericParam(index, name, ty)

def const_generic_var_id_of_json(ctx: OfJsonCtx, js: Json) -> ConstGenericVarId:
    return ConstGenericVarId(int_of_json(ctx, js))

def const_handling_of_json(ctx: OfJsonCtx, js: Json) -> ConstHandling:
    __tag, __payload = split_variant(js)
    if __tag == "Initializers":
        return ConstHandlingInitializers()
    if __tag == "Values":
        return ConstHandlingValues()
    raise unknown_variant("ConstHandling", __tag)

def constant_expr_of_json(ctx: OfJsonCtx, js: Json) -> ConstantExpr:
    def read_contents(ctx: OfJsonCtx, js: Json) -> ConstantExpr:
        kind, ty = pair_of_json(constant_expr_kind_of_json, ty_of_json)(ctx, js)
        return ConstantExpr(kind=kind, ty=ty)

    return dedup_val_of_json(ctx.constant_expr_dedup, read_contents)(ctx, js)

def constant_expr_kind_of_json(ctx: OfJsonCtx, js: Json) -> ConstantExprKind:
    __tag, __payload = split_variant(js)
    if __tag == "Bool":
        _0 = bool_of_json(ctx, __payload)
        return ConstantExprKindCBool(_0)
    if __tag == "Integer":
        _0 = integer_value_of_json(ctx, __payload)
        return ConstantExprKindCInteger(_0)
    if __tag == "Char":
        _0 = char_of_json(ctx, __payload)
        return ConstantExprKindCChar(_0)
    if __tag == "Float":
        _0 = float_value_of_json(ctx, __payload)
        return ConstantExprKindCFloat(_0)
    if __tag == "Adt":
        __items = expect_list(__payload, 2)
        _0 = option_of_json(variant_id_of_json)(ctx, __items[0])
        _1 = list_of_json(constant_expr_of_json)(ctx, __items[1])
        return ConstantExprKindCAdt(_0, _1)
    if __tag == "Array":
        _0 = list_of_json(constant_expr_of_json)(ctx, __payload)
        return ConstantExprKindCArray(_0)
    if __tag == "Ref":
        __items = expect_list(__payload, 2)
        _0 = constant_expr_of_json(ctx, __items[0])
        _1 = option_of_json(unsizing_metadata_of_json)(ctx, __items[1])
        return ConstantExprKindCRef(_0, _1)
    if __tag == "Ptr":
        __items = expect_list(__payload, 3)
        _0 = ref_kind_of_json(ctx, __items[0])
        _1 = constant_expr_of_json(ctx, __items[1])
        _2 = option_of_json(unsizing_metadata_of_json)(ctx, __items[2])
        return ConstantExprKindCPtr(_0, _1, _2)
    if __tag == "Str":
        _0 = string_of_json(ctx, __payload)
        return ConstantExprKindCStr(_0)
    if __tag == "ByteStr":
        _0 = list_of_json(int_of_json)(ctx, __payload)
        return ConstantExprKindCByteStr(_0)
    if __tag == "FnDef":
        _0 = fn_ptr_of_json(ctx, __payload)
        return ConstantExprKindCFnDef(_0)
    if __tag == "FnPtr":
        _0 = fn_ptr_of_json(ctx, __payload)
        return ConstantExprKindCFnPtr(_0)
    if __tag == "PtrNoProvenance":
        _0 = big_int_of_json(ctx, __payload)
        return ConstantExprKindCPtrNoProvenance(_0)
    if __tag == "TypeId":
        _0 = ty_of_json(ctx, __payload)
        return ConstantExprKindCTypeId(_0)
    if __tag == "RawMemory":
        _0 = list_of_json(byte_of_json)(ctx, __payload)
        return ConstantExprKindCRawMemory(_0)
    if __tag == "Var":
        _0 = de_bruijn_var_of_json(const_generic_var_id_of_json)(ctx, __payload)
        return ConstantExprKindCVar(_0)
    if __tag == "Global":
        _0 = global_decl_ref_of_json(ctx, __payload)
        return ConstantExprKindCGlobal(_0)
    if __tag == "Call":
        __items = expect_list(__payload, 2)
        _0 = fn_ptr_of_json(ctx, __items[0])
        _1 = list_of_json(constant_expr_of_json)(ctx, __items[1])
        return ConstantExprKindCCall(_0, _1)
    if __tag == "TraitConst":
        __items = expect_list(__payload, 2)
        _0 = trait_ref_of_json(ctx, __items[0])
        _1 = assoc_const_id_of_json(ctx, __items[1])
        return ConstantExprKindCTraitConst(_0, _1)
    if __tag == "VTableRef":
        _0 = trait_ref_of_json(ctx, __payload)
        return ConstantExprKindCVTableRef(_0)
    if __tag == "Discriminant":
        __items = expect_list(__payload, 2)
        _0 = type_decl_ref_of_json(ctx, __items[0])
        _1 = variant_id_of_json(ctx, __items[1])
        return ConstantExprKindCDiscriminant(_0, _1)
    if __tag == "SizeOf":
        _0 = ty_of_json(ctx, __payload)
        return ConstantExprKindCSizeOf(_0)
    if __tag == "AlignOf":
        _0 = ty_of_json(ctx, __payload)
        return ConstantExprKindCAlignOf(_0)
    if __tag == "Opaque":
        _0 = string_of_json(ctx, __payload)
        return ConstantExprKindCOpaque(_0)
    raise unknown_variant("ConstantExprKind", __tag)

def de_bruijn_id_of_json(ctx: OfJsonCtx, js: Json) -> DeBruijnId:
    return int_of_json(ctx, js)

def de_bruijn_var_of_json(arg0_of_json: JsonDecoder[T0]) -> JsonDecoder[DeBruijnVar[T0]]:
    def read(ctx: OfJsonCtx, js: Json) -> DeBruijnVar[T0]:
        __tag, __payload = split_variant(js)
        if __tag == "Bound":
            __items = expect_list(__payload, 2)
            _0 = de_bruijn_id_of_json(ctx, __items[0])
            _1 = arg0_of_json(ctx, __items[1])
            return DeBruijnVarBound(_0, _1)
        if __tag == "Free":
            _0 = arg0_of_json(ctx, __payload)
            return DeBruijnVarFree(_0)
        raise unknown_variant("DeBruijnVar", __tag)
    return read

def declaration_group_of_json(ctx: OfJsonCtx, js: Json) -> DeclarationGroup:
    __tag, __payload = split_variant(js)
    if __tag == "Type":
        _0 = g_declaration_group_of_json(type_decl_id_of_json)(ctx, __payload)
        return DeclarationGroupTypeGroup(_0)
    if __tag == "Fun":
        _0 = g_declaration_group_of_json(fun_decl_id_of_json)(ctx, __payload)
        return DeclarationGroupFunGroup(_0)
    if __tag == "Global":
        _0 = g_declaration_group_of_json(global_decl_id_of_json)(ctx, __payload)
        return DeclarationGroupGlobalGroup(_0)
    if __tag == "TraitDecl":
        _0 = g_declaration_group_of_json(trait_decl_id_of_json)(ctx, __payload)
        return DeclarationGroupTraitDeclGroup(_0)
    if __tag == "TraitImpl":
        _0 = g_declaration_group_of_json(trait_impl_id_of_json)(ctx, __payload)
        return DeclarationGroupTraitImplGroup(_0)
    if __tag == "Mixed":
        _0 = g_declaration_group_of_json(item_id_of_json)(ctx, __payload)
        return DeclarationGroupMixedGroup(_0)
    raise unknown_variant("DeclarationGroup", __tag)

def rustc_deprecated_since_of_json(ctx: OfJsonCtx, js: Json) -> RustcDeprecatedSince:
    __tag, __payload = split_variant(js)
    if __tag == "RustcVersion":
        _0 = rustc_rustc_version_of_json(ctx, __payload)
        return RustcDeprecatedSinceRustcVersion(_0)
    if __tag == "Future":
        return RustcDeprecatedSinceFuture()
    if __tag == "NonStandard":
        _0 = string_of_json(ctx, __payload)
        return RustcDeprecatedSinceNonStandard(_0)
    if __tag == "Unspecified":
        return RustcDeprecatedSinceUnspecified()
    if __tag == "Err":
        return RustcDeprecatedSinceErr()
    raise unknown_variant("RustcDeprecatedSince", __tag)

def rustc_deprecation_of_json(ctx: OfJsonCtx, js: Json) -> RustcDeprecation:
    __fields = expect_object(js)
    since = rustc_deprecated_since_of_json(ctx, __fields["since"])
    note = option_of_json(rustc_ident_of_json)(ctx, __fields["note"])
    suggestion = option_of_json(string_of_json)(ctx, __fields["suggestion"])
    return RustcDeprecation(since, note, suggestion)

def disambiguator_of_json(ctx: OfJsonCtx, js: Json) -> Disambiguator:
    return Disambiguator(int_of_json(ctx, js))

def discriminator_of_json(ctx: OfJsonCtx, js: Json) -> Discriminator:
    __tag, __payload = split_variant(js)
    if __tag == "Known":
        _0 = variant_id_of_json(ctx, __payload)
        return DiscriminatorKnown(_0)
    if __tag == "Invalid":
        return DiscriminatorInvalid()
    if __tag == "Branch":
        __fields = expect_object(__payload)
        offset = offset_expr_of_json(ctx, __fields["offset"])
        int_ty = integer_type_of_json(ctx, __fields["int_ty"])
        children = list_of_json(pair_of_json(range_inclusive_of_json(integer_value_of_json), discriminator_of_json))(ctx, __fields["children"])
        fallback = box_of_json(discriminator_of_json)(ctx, __fields["fallback"])
        return DiscriminatorBranch(offset, int_ty, children, fallback)
    raise unknown_variant("Discriminator", __tag)

def drop_kind_of_json(ctx: OfJsonCtx, js: Json) -> DropKind:
    __tag, __payload = split_variant(js)
    if __tag == "Precise":
        return DropKindPrecise()
    if __tag == "Conditional":
        return DropKindConditional()
    raise unknown_variant("DropKind", __tag)

def dyn_predicate_of_json(ctx: OfJsonCtx, js: Json) -> DynPredicate:
    __fields = expect_object(js)
    binder = binder_of_json(ty_of_json)(ctx, __fields["binder"])
    return DynPredicate(binder)

def error_of_json(ctx: OfJsonCtx, js: Json) -> Error:
    __fields = expect_object(js)
    span = span_of_json(ctx, __fields["span"])
    msg = string_of_json(ctx, __fields["msg"])
    return Error(span, msg)

def exact_size_expr_of_json(ctx: OfJsonCtx, js: Json) -> ExactSizeExpr:
    return dedup_val_of_json(ctx.exact_size_expr_kind_dedup, exact_size_expr_kind_of_json)(ctx, js)

def exact_size_expr_kind_of_json(ctx: OfJsonCtx, js: Json) -> ExactSizeExprKind:
    __tag, __payload = split_variant(js)
    if __tag == "Constant":
        _0 = constant_expr_of_json(ctx, __payload)
        return ExactSizeExprKindExactSizeExprConstant(_0)
    if __tag == "FromMetadata":
        _0 = metadata_value_of_json(ctx, __payload)
        return ExactSizeExprKindExactSizeExprFromMetadata(_0)
    if __tag == "Max":
        _0 = list_of_json(exact_size_expr_of_json)(ctx, __payload)
        return ExactSizeExprKindExactSizeExprMax(_0)
    if __tag == "Min":
        _0 = list_of_json(exact_size_expr_of_json)(ctx, __payload)
        return ExactSizeExprKindExactSizeExprMin(_0)
    if __tag == "Plus":
        __items = expect_list(__payload, 2)
        _0 = exact_size_expr_of_json(ctx, __items[0])
        _1 = exact_size_expr_of_json(ctx, __items[1])
        return ExactSizeExprKindExactSizeExprPlus(_0, _1)
    if __tag == "Scale":
        __items = expect_list(__payload, 2)
        _0 = exact_size_expr_of_json(ctx, __items[0])
        _1 = constant_expr_of_json(ctx, __items[1])
        return ExactSizeExprKindExactSizeExprScale(_0, _1)
    if __tag == "AlignTo":
        __fields = expect_object(__payload)
        base = exact_size_expr_of_json(ctx, __fields["base"])
        target_align = exact_size_expr_of_json(ctx, __fields["target_align"])
        return ExactSizeExprKindExactSizeExprAlignTo(base, target_align)
    if __tag == "IfInhabited":
        __fields = expect_object(__payload)
        ty = ty_of_json(ctx, __fields["ty"])
        then_size = exact_size_expr_of_json(ctx, __fields["then_size"])
        else_size = exact_size_expr_of_json(ctx, __fields["else_size"])
        return ExactSizeExprKindExactSizeExprIfInhabited(ty, then_size, else_size)
    raise unknown_variant("ExactSizeExprKind", __tag)

def field_of_json(ctx: OfJsonCtx, js: Json) -> Field:
    __fields = expect_object(js)
    span = span_of_json(ctx, __fields["span"])
    attr_info = attr_info_of_json(ctx, __fields["attr_info"])
    field_name = string_of_json(ctx, __fields["name"])
    is_positional = bool_of_json(ctx, __fields["is_positional"])
    field_ty = ty_of_json(ctx, __fields["ty"])
    return Field(span, attr_info, field_name, is_positional, field_ty)

def field_id_of_json(ctx: OfJsonCtx, js: Json) -> FieldId:
    return FieldId(int_of_json(ctx, js))

def file_of_json(ctx: OfJsonCtx, js: Json) -> File:
    __fields = expect_object(js)
    __file_id = int_of_json(ctx, __fields["id"])
    __file = File(
        name=file_name_of_json(ctx, __fields["name"]),
        crate_name=string_of_json(ctx, __fields["crate_name"]),
        contents=option_of_json(string_of_json)(ctx, __fields["contents"]),
    )
    ctx.files[__file_id] = __file
    return __file

def file_id_of_json(ctx: OfJsonCtx, js: Json) -> FileId:
    __file_id = int_of_json(ctx, js)
    try:
        return ctx.files[__file_id]
    except KeyError:
        raise DeserializeError(f"unknown file id: {__file_id}") from None

def file_name_of_json(ctx: OfJsonCtx, js: Json) -> FileName:
    __tag, __payload = split_variant(js)
    if __tag == "Virtual":
        _0 = string_of_json(ctx, __payload)
        return FileNameVirtual(_0)
    if __tag == "Local":
        _0 = string_of_json(ctx, __payload)
        return FileNameLocal(_0)
    if __tag == "NotReal":
        _0 = string_of_json(ctx, __payload)
        return FileNameNotReal(_0)
    raise unknown_variant("FileName", __tag)

def float_type_of_json(ctx: OfJsonCtx, js: Json) -> FloatType:
    __tag, __payload = split_variant(js)
    if __tag == "F16":
        return FloatTypeF16()
    if __tag == "F32":
        return FloatTypeF32()
    if __tag == "F64":
        return FloatTypeF64()
    if __tag == "F128":
        return FloatTypeF128()
    raise unknown_variant("FloatType", __tag)

def float_value_of_json(ctx: OfJsonCtx, js: Json) -> FloatValue:
    __fields = expect_object(js)
    float_value = string_of_json(ctx, __fields["value"])
    float_ty = float_type_of_json(ctx, __fields["ty"])
    return FloatValue(float_value, float_ty)

def fn_operand_of_json(ctx: OfJsonCtx, js: Json) -> FnOperand:
    __tag, __payload = split_variant(js)
    if __tag == "Regular":
        _0 = fn_ptr_of_json(ctx, __payload)
        return FnOperandFnOpRegular(_0)
    if __tag == "Dynamic":
        _0 = operand_of_json(ctx, __payload)
        return FnOperandFnOpDynamic(_0)
    raise unknown_variant("FnOperand", __tag)

def fn_ptr_of_json(ctx: OfJsonCtx, js: Json) -> FnPtr:
    __fields = expect_object(js)
    kind = box_of_json(fn_ptr_kind_of_json)(ctx, __fields["kind"])
    generics = box_of_json(generic_args_of_json)(ctx, __fields["generics"])
    return FnPtr(kind, generics)

def fn_ptr_kind_of_json(ctx: OfJsonCtx, js: Json) -> FnPtrKind:
    __tag, __payload = split_variant(js)
    if __tag == "Fun":
        _0 = fun_decl_id_of_json(ctx, __payload)
        return FnPtrKindFun(_0)
    if __tag == "Trait":
        __items = expect_list(__payload, 2)
        _0 = trait_ref_of_json(ctx, __items[0])
        _1 = trait_method_id_of_json(ctx, __items[1])
        return FnPtrKindTraitMethod(_0, _1)
    raise unknown_variant("FnPtrKind", __tag)

def fun_decl_of_json(ctx: OfJsonCtx, js: Json) -> FunDecl:
    __fields = expect_object(js)
    def_id = fun_decl_id_of_json(ctx, __fields["def_id"])
    item_meta = item_meta_of_json(ctx, __fields["item_meta"])
    generics = generic_params_of_json(ctx, __fields["generics"])
    signature = box_of_json(fun_sig_of_json)(ctx, __fields["signature"])
    src = fun_source_of_json(ctx, __fields["src"])
    body = body_of_json(ctx, __fields["body"])
    return FunDecl(def_id, item_meta, generics, signature, src, body)

def fun_decl_id_of_json(ctx: OfJsonCtx, js: Json) -> FunDeclId:
    return FunDeclId(int_of_json(ctx, js))

def fun_decl_ref_of_json(ctx: OfJsonCtx, js: Json) -> FunDeclRef:
    __fields = expect_object(js)
    id = fun_decl_id_of_json(ctx, __fields["id"])
    generics = box_of_json(generic_args_of_json)(ctx, __fields["generics"])
    return FunDeclRef(id, generics)

def fun_sig_of_json(ctx: OfJsonCtx, js: Json) -> FunSig:
    __fields = expect_object(js)
    is_unsafe = bool_of_json(ctx, __fields["is_unsafe"])
    abi = abi_of_json(ctx, __fields["abi"])
    is_variadic = bool_of_json(ctx, __fields["is_variadic"])
    inputs = list_of_json(ty_of_json)(ctx, __fields["inputs"])
    output = ty_of_json(ctx, __fields["output"])
    return FunSig(is_unsafe, abi, is_variadic, inputs, output)

def fun_source_of_json(ctx: OfJsonCtx, js: Json) -> FunSource:
    __tag, __payload = split_variant(js)
    if __tag == "Normal":
        return FunSourceNormalFun()
    if __tag == "AdtConstructor":
        return FunSourceAdtConstructorFun()
    if __tag == "TraitDefault":
        __fields = expect_object(__payload)
        trait_ref = trait_decl_ref_of_json(ctx, __fields["trait_ref"])
        item_id = trait_method_id_of_json(ctx, __fields["item_id"])
        return FunSourceTraitDefaultFun(trait_ref, item_id)
    if __tag == "TraitImpl":
        __fields = expect_object(__payload)
        impl_ref = trait_impl_ref_of_json(ctx, __fields["impl_ref"])
        trait_ref = trait_decl_ref_of_json(ctx, __fields["trait_ref"])
        item_id = trait_method_id_of_json(ctx, __fields["item_id"])
        reuses_default = bool_of_json(ctx, __fields["reuses_default"])
        return FunSourceTraitImplFun(impl_ref, trait_ref, item_id, reuses_default)
    if __tag == "VTableShim":
        return FunSourceVTableShimFun()
    if __tag == "GlobalInitializer":
        _0 = global_decl_ref_of_json(ctx, __payload)
        return FunSourceGlobalInitializerFun(_0)
    if __tag == "TargetDependent":
        __fields = expect_object(__payload)
        dispatcher = fun_decl_ref_of_json(ctx, __fields["dispatcher"])
        return FunSourceTargetDependentFun(dispatcher)
    raise unknown_variant("FunSource", __tag)

def g_declaration_group_of_json(arg0_of_json: JsonDecoder[T0]) -> JsonDecoder[GDeclarationGroup[T0]]:
    def read(ctx: OfJsonCtx, js: Json) -> GDeclarationGroup[T0]:
        __tag, __payload = split_variant(js)
        if __tag == "NonRec":
            _0 = arg0_of_json(ctx, __payload)
            return GDeclarationGroupNonRecGroup(_0)
        if __tag == "Rec":
            _0 = list_of_json(arg0_of_json)(ctx, __payload)
            return GDeclarationGroupRecGroup(_0)
        raise unknown_variant("GDeclarationGroup", __tag)
    return read

def gexpr_body_of_json(arg0_of_json: JsonDecoder[T0]) -> JsonDecoder[GexprBody[T0]]:
    def read(ctx: OfJsonCtx, js: Json) -> GexprBody[T0]:
        __fields = expect_object(js)
        span = span_of_json(ctx, __fields["span"])
        bound_body_regions = int_of_json(ctx, __fields["bound_body_regions"])
        locals = locals_of_json(ctx, __fields["locals"])
        body = arg0_of_json(ctx, __fields["body"])
        return GexprBody(span, bound_body_regions, locals, body)
    return read

def generic_args_of_json(ctx: OfJsonCtx, js: Json) -> GenericArgs:
    __fields = expect_object(js)
    regions = list_of_json(region_of_json)(ctx, __fields["regions"])
    types = list_of_json(ty_of_json)(ctx, __fields["types"])
    const_generics = list_of_json(constant_expr_of_json)(ctx, __fields["const_generics"])
    trait_refs = list_of_json(trait_ref_of_json)(ctx, __fields["trait_refs"])
    return GenericArgs(regions, types, const_generics, trait_refs)

def generic_params_of_json(ctx: OfJsonCtx, js: Json) -> GenericParams:
    __fields = expect_object(js)
    regions = list_of_json(region_param_of_json)(ctx, __fields["regions"])
    types = list_of_json(type_param_of_json)(ctx, __fields["types"])
    const_generics = list_of_json(const_generic_param_of_json)(ctx, __fields["const_generics"])
    trait_clauses = list_of_json(trait_param_of_json)(ctx, __fields["trait_clauses"])
    regions_outlive = list_of_json(region_binder_of_json(outlives_pred_of_json(region_of_json, region_of_json)))(ctx, __fields["regions_outlive"])
    types_outlive = list_of_json(region_binder_of_json(outlives_pred_of_json(ty_of_json, region_of_json)))(ctx, __fields["types_outlive"])
    trait_type_constraints = list_of_json(region_binder_of_json(trait_type_constraint_of_json))(ctx, __fields["trait_type_constraints"])
    return GenericParams(regions, types, const_generics, trait_clauses, regions_outlive, types_outlive, trait_type_constraints)

def global_decl_of_json(ctx: OfJsonCtx, js: Json) -> GlobalDecl:
    __fields = expect_object(js)
    def_id = global_decl_id_of_json(ctx, __fields["def_id"])
    item_meta = item_meta_of_json(ctx, __fields["item_meta"])
    generics = generic_params_of_json(ctx, __fields["generics"])
    ty = ty_of_json(ctx, __fields["ty"])
    src = global_source_of_json(ctx, __fields["src"])
    global_kind = global_kind_of_json(ctx, __fields["global_kind"])
    value = constant_expr_of_json(ctx, __fields["value"])
    return GlobalDecl(def_id, item_meta, generics, ty, src, global_kind, value)

def global_decl_id_of_json(ctx: OfJsonCtx, js: Json) -> GlobalDeclId:
    return GlobalDeclId(int_of_json(ctx, js))

def global_decl_ref_of_json(ctx: OfJsonCtx, js: Json) -> GlobalDeclRef:
    __fields = expect_object(js)
    id = global_decl_id_of_json(ctx, __fields["id"])
    generics = box_of_json(generic_args_of_json)(ctx, __fields["generics"])
    return GlobalDeclRef(id, generics)

def global_kind_of_json(ctx: OfJsonCtx, js: Json) -> GlobalKind:
    __tag, __payload = split_variant(js)
    if __tag == "Static":
        return GlobalKindStatic()
    if __tag == "ThreadLocal":
        return GlobalKindThreadLocal()
    if __tag == "NamedConst":
        return GlobalKindNamedConst()
    if __tag == "AnonConst":
        return GlobalKindAnonConst()
    raise unknown_variant("GlobalKind", __tag)

def global_source_of_json(ctx: OfJsonCtx, js: Json) -> GlobalSource:
    __tag, __payload = split_variant(js)
    if __tag == "Normal":
        return GlobalSourceNormalGlobal()
    if __tag == "TraitDefault":
        __fields = expect_object(__payload)
        trait_ref = trait_decl_ref_of_json(ctx, __fields["trait_ref"])
        item_id = assoc_const_id_of_json(ctx, __fields["item_id"])
        return GlobalSourceTraitDefaultGlobal(trait_ref, item_id)
    if __tag == "TraitImpl":
        __fields = expect_object(__payload)
        impl_ref = trait_impl_ref_of_json(ctx, __fields["impl_ref"])
        trait_ref = trait_decl_ref_of_json(ctx, __fields["trait_ref"])
        item_id = assoc_const_id_of_json(ctx, __fields["item_id"])
        reuses_default = bool_of_json(ctx, __fields["reuses_default"])
        return GlobalSourceTraitImplGlobal(impl_ref, trait_ref, item_id, reuses_default)
    if __tag == "VTableInstance":
        __fields = expect_object(__payload)
        impl_ref = option_of_json(trait_impl_ref_of_json)(ctx, __fields["impl_ref"])
        return GlobalSourceVTableInstanceGlobal(impl_ref)
    raise unknown_variant("GlobalSource", __tag)

def rustc_ident_of_json(ctx: OfJsonCtx, js: Json) -> RustcIdent:
    __fields = expect_object(js)
    name = string_of_json(ctx, __fields["name"])
    span = span_of_json(ctx, __fields["span"])
    return RustcIdent(name, span)

def impl_elem_of_json(ctx: OfJsonCtx, js: Json) -> ImplElem:
    __tag, __payload = split_variant(js)
    if __tag == "Ty":
        _0 = box_of_json(binder_of_json(ty_of_json))(ctx, __payload)
        return ImplElemTy(_0)
    if __tag == "Trait":
        _0 = trait_impl_id_of_json(ctx, __payload)
        return ImplElemTrait(_0)
    raise unknown_variant("ImplElem", __tag)

def inline_attr_of_json(ctx: OfJsonCtx, js: Json) -> InlineAttr:
    __tag, __payload = split_variant(js)
    if __tag == "Hint":
        return InlineAttrHint()
    if __tag == "Never":
        return InlineAttrNever()
    if __tag == "Always":
        return InlineAttrAlways()
    raise unknown_variant("InlineAttr", __tag)

def rustc_inline_attr_of_json(ctx: OfJsonCtx, js: Json) -> RustcInlineAttr:
    __tag, __payload = split_variant(js)
    if __tag == "None":
        return RustcInlineAttrNone()
    if __tag == "Hint":
        return RustcInlineAttrHint()
    if __tag == "Always":
        return RustcInlineAttrAlways()
    if __tag == "Never":
        return RustcInlineAttrNever()
    if __tag == "Force":
        __fields = expect_object(__payload)
        attr_span = span_of_json(ctx, __fields["attr_span"])
        reason = option_of_json(string_of_json)(ctx, __fields["reason"])
        return RustcInlineAttrForce(attr_span, reason)
    raise unknown_variant("RustcInlineAttr", __tag)

def int_ty_of_json(ctx: OfJsonCtx, js: Json) -> IntTy:
    __tag, __payload = split_variant(js)
    if __tag == "Isize":
        return IntTyIsize()
    if __tag == "I8":
        return IntTyI8()
    if __tag == "I16":
        return IntTyI16()
    if __tag == "I32":
        return IntTyI32()
    if __tag == "I64":
        return IntTyI64()
    if __tag == "I128":
        return IntTyI128()
    raise unknown_variant("IntTy", __tag)

def integer_type_of_json(ctx: OfJsonCtx, js: Json) -> IntegerType:
    __tag, __payload = split_variant(js)
    if __tag == "Signed":
        _0 = int_ty_of_json(ctx, __payload)
        return IntegerTypeSigned(_0)
    if __tag == "Unsigned":
        _0 = u_int_ty_of_json(ctx, __payload)
        return IntegerTypeUnsigned(_0)
    raise unknown_variant("IntegerType", __tag)

def integer_value_of_json(ctx: OfJsonCtx, js: Json) -> IntegerValue:
    __tag, __payload = split_variant(js)
    if __tag == "Unsigned":
        __items = expect_list(__payload, 2)
        _0 = u_int_ty_of_json(ctx, __items[0])
        _1 = big_int_of_json(ctx, __items[1])
        return IntegerValueUnsignedInteger(_0, _1)
    if __tag == "Signed":
        __items = expect_list(__payload, 2)
        _0 = int_ty_of_json(ctx, __items[0])
        _1 = big_int_of_json(ctx, __items[1])
        return IntegerValueSignedInteger(_0, _1)
    raise unknown_variant("IntegerValue", __tag)

def item_id_of_json(ctx: OfJsonCtx, js: Json) -> ItemId:
    __tag, __payload = split_variant(js)
    if __tag == "Type":
        _0 = type_decl_id_of_json(ctx, __payload)
        return ItemIdIdType(_0)
    if __tag == "TraitDecl":
        _0 = trait_decl_id_of_json(ctx, __payload)
        return ItemIdIdTraitDecl(_0)
    if __tag == "TraitImpl":
        _0 = trait_impl_id_of_json(ctx, __payload)
        return ItemIdIdTraitImpl(_0)
    if __tag == "Fun":
        _0 = fun_decl_id_of_json(ctx, __payload)
        return ItemIdIdFun(_0)
    if __tag == "Global":
        _0 = global_decl_id_of_json(ctx, __payload)
        return ItemIdIdGlobal(_0)
    raise unknown_variant("ItemId", __tag)

def item_meta_of_json(ctx: OfJsonCtx, js: Json) -> ItemMeta:
    __fields = expect_object(js)
    name = name_of_json(ctx, __fields["name"])
    span = span_of_json(ctx, __fields["span"])
    source_text = option_of_json(string_of_json)(ctx, __fields["source_text"])
    attr_info = attr_info_of_json(ctx, __fields["attr_info"])
    is_local = bool_of_json(ctx, __fields["is_local"])
    opacity = item_opacity_of_json(ctx, __fields["opacity"])
    lang_item = option_of_json(rustc_lang_item_of_json)(ctx, __fields["lang_item"])
    diagnostic_item = option_of_json(string_of_json)(ctx, __fields["diagnostic_item"])
    return ItemMeta(name, span, source_text, attr_info, is_local, opacity, lang_item, diagnostic_item)

def item_opacity_of_json(ctx: OfJsonCtx, js: Json) -> ItemOpacity:
    __tag, __payload = split_variant(js)
    if __tag == "Transparent":
        return ItemOpacityTransparent()
    if __tag == "Foreign":
        return ItemOpacityForeign()
    if __tag == "Opaque":
        return ItemOpacityItemOpaque()
    if __tag == "Invisible":
        return ItemOpacityInvisible()
    raise unknown_variant("ItemOpacity", __tag)

def rustc_lang_item_of_json(ctx: OfJsonCtx, js: Json) -> RustcLangItem:
    __tag, __payload = split_variant(js)
    if __tag == "Sized":
        return RustcLangItemSized()
    if __tag == "MetaSized":
        return RustcLangItemMetaSized()
    if __tag == "PointeeSized":
        return RustcLangItemPointeeSized()
    if __tag == "Unsize":
        return RustcLangItemUnsize()
    if __tag == "AlignOf":
        return RustcLangItemAlignOf()
    if __tag == "SizeOf":
        return RustcLangItemSizeOf()
    if __tag == "OffsetOf":
        return RustcLangItemOffsetOf()
    if __tag == "StructuralPeq":
        return RustcLangItemStructuralPeq()
    if __tag == "Copy":
        return RustcLangItemCopy()
    if __tag == "Clone":
        return RustcLangItemClone()
    if __tag == "CloneFn":
        return RustcLangItemCloneFn()
    if __tag == "UseCloned":
        return RustcLangItemUseCloned()
    if __tag == "TrivialClone":
        return RustcLangItemTrivialClone()
    if __tag == "Sync":
        return RustcLangItemSync()
    if __tag == "DiscriminantKind":
        return RustcLangItemDiscriminantKind()
    if __tag == "Discriminant":
        return RustcLangItemDiscriminant()
    if __tag == "PointeeTrait":
        return RustcLangItemPointeeTrait()
    if __tag == "Metadata":
        return RustcLangItemMetadata()
    if __tag == "DynMetadata":
        return RustcLangItemDynMetadata()
    if __tag == "Freeze":
        return RustcLangItemFreeze()
    if __tag == "UnsafeUnpin":
        return RustcLangItemUnsafeUnpin()
    if __tag == "FnPtrTrait":
        return RustcLangItemFnPtrTrait()
    if __tag == "FnPtrAddr":
        return RustcLangItemFnPtrAddr()
    if __tag == "Drop":
        return RustcLangItemDrop()
    if __tag == "Destruct":
        return RustcLangItemDestruct()
    if __tag == "AsyncDrop":
        return RustcLangItemAsyncDrop()
    if __tag == "AsyncDropInPlace":
        return RustcLangItemAsyncDropInPlace()
    if __tag == "CoerceUnsized":
        return RustcLangItemCoerceUnsized()
    if __tag == "DispatchFromDyn":
        return RustcLangItemDispatchFromDyn()
    if __tag == "TryAsDyn":
        return RustcLangItemTryAsDyn()
    if __tag == "TransmuteOpts":
        return RustcLangItemTransmuteOpts()
    if __tag == "TransmuteTrait":
        return RustcLangItemTransmuteTrait()
    if __tag == "Add":
        return RustcLangItemAdd()
    if __tag == "Sub":
        return RustcLangItemSub()
    if __tag == "Mul":
        return RustcLangItemMul()
    if __tag == "Div":
        return RustcLangItemDiv()
    if __tag == "Rem":
        return RustcLangItemRem()
    if __tag == "Neg":
        return RustcLangItemNeg()
    if __tag == "Not":
        return RustcLangItemNot()
    if __tag == "BitXor":
        return RustcLangItemBitXor()
    if __tag == "BitAnd":
        return RustcLangItemBitAnd()
    if __tag == "BitOr":
        return RustcLangItemBitOr()
    if __tag == "Shl":
        return RustcLangItemShl()
    if __tag == "Shr":
        return RustcLangItemShr()
    if __tag == "AddAssign":
        return RustcLangItemAddAssign()
    if __tag == "SubAssign":
        return RustcLangItemSubAssign()
    if __tag == "MulAssign":
        return RustcLangItemMulAssign()
    if __tag == "DivAssign":
        return RustcLangItemDivAssign()
    if __tag == "RemAssign":
        return RustcLangItemRemAssign()
    if __tag == "BitXorAssign":
        return RustcLangItemBitXorAssign()
    if __tag == "BitAndAssign":
        return RustcLangItemBitAndAssign()
    if __tag == "BitOrAssign":
        return RustcLangItemBitOrAssign()
    if __tag == "ShlAssign":
        return RustcLangItemShlAssign()
    if __tag == "ShrAssign":
        return RustcLangItemShrAssign()
    if __tag == "Index":
        return RustcLangItemIndex()
    if __tag == "IndexMut":
        return RustcLangItemIndexMut()
    if __tag == "UnsafeCell":
        return RustcLangItemUnsafeCell()
    if __tag == "CovariantUnsafeCell":
        return RustcLangItemCovariantUnsafeCell()
    if __tag == "UnsafePinned":
        return RustcLangItemUnsafePinned()
    if __tag == "VaArgSafe":
        return RustcLangItemVaArgSafe()
    if __tag == "VaList":
        return RustcLangItemVaList()
    if __tag == "Complex":
        return RustcLangItemComplex()
    if __tag == "Deref":
        return RustcLangItemDeref()
    if __tag == "DerefMut":
        return RustcLangItemDerefMut()
    if __tag == "DerefPure":
        return RustcLangItemDerefPure()
    if __tag == "DerefTarget":
        return RustcLangItemDerefTarget()
    if __tag == "Receiver":
        return RustcLangItemReceiver()
    if __tag == "ReceiverTarget":
        return RustcLangItemReceiverTarget()
    if __tag == "LegacyReceiver":
        return RustcLangItemLegacyReceiver()
    if __tag == "Fn":
        return RustcLangItemFn()
    if __tag == "FnMut":
        return RustcLangItemFnMut()
    if __tag == "FnOnce":
        return RustcLangItemFnOnce()
    if __tag == "AsyncFn":
        return RustcLangItemAsyncFn()
    if __tag == "AsyncFnMut":
        return RustcLangItemAsyncFnMut()
    if __tag == "AsyncFnOnce":
        return RustcLangItemAsyncFnOnce()
    if __tag == "AsyncFnOnceOutput":
        return RustcLangItemAsyncFnOnceOutput()
    if __tag == "CallOnceFuture":
        return RustcLangItemCallOnceFuture()
    if __tag == "CallRefFuture":
        return RustcLangItemCallRefFuture()
    if __tag == "AsyncFnKindHelper":
        return RustcLangItemAsyncFnKindHelper()
    if __tag == "AsyncFnKindUpvars":
        return RustcLangItemAsyncFnKindUpvars()
    if __tag == "FnOnceOutput":
        return RustcLangItemFnOnceOutput()
    if __tag == "Iterator":
        return RustcLangItemIterator()
    if __tag == "FusedIterator":
        return RustcLangItemFusedIterator()
    if __tag == "Future":
        return RustcLangItemFuture()
    if __tag == "FutureOutput":
        return RustcLangItemFutureOutput()
    if __tag == "AsyncIterator":
        return RustcLangItemAsyncIterator()
    if __tag == "CoroutineState":
        return RustcLangItemCoroutineState()
    if __tag == "Coroutine":
        return RustcLangItemCoroutine()
    if __tag == "CoroutineReturn":
        return RustcLangItemCoroutineReturn()
    if __tag == "CoroutineYield":
        return RustcLangItemCoroutineYield()
    if __tag == "CoroutineResume":
        return RustcLangItemCoroutineResume()
    if __tag == "Unpin":
        return RustcLangItemUnpin()
    if __tag == "Pin":
        return RustcLangItemPin()
    if __tag == "OrderingEnum":
        return RustcLangItemOrderingEnum()
    if __tag == "PartialEq":
        return RustcLangItemPartialEq()
    if __tag == "PartialOrd":
        return RustcLangItemPartialOrd()
    if __tag == "CVoid":
        return RustcLangItemCVoid()
    if __tag == "Type":
        return RustcLangItemType()
    if __tag == "TypeGeneric":
        return RustcLangItemTypeGeneric()
    if __tag == "TypeId":
        return RustcLangItemTypeId()
    if __tag == "Panic":
        return RustcLangItemPanic()
    if __tag == "PanicNounwind":
        return RustcLangItemPanicNounwind()
    if __tag == "PanicFmt":
        return RustcLangItemPanicFmt()
    if __tag == "PanicDisplay":
        return RustcLangItemPanicDisplay()
    if __tag == "ConstPanicFmt":
        return RustcLangItemConstPanicFmt()
    if __tag == "PanicBoundsCheck":
        return RustcLangItemPanicBoundsCheck()
    if __tag == "PanicMisalignedPointerDereference":
        return RustcLangItemPanicMisalignedPointerDereference()
    if __tag == "PanicInfo":
        return RustcLangItemPanicInfo()
    if __tag == "PanicLocation":
        return RustcLangItemPanicLocation()
    if __tag == "PanicImpl":
        return RustcLangItemPanicImpl()
    if __tag == "PanicCannotUnwind":
        return RustcLangItemPanicCannotUnwind()
    if __tag == "PanicInCleanup":
        return RustcLangItemPanicInCleanup()
    if __tag == "PanicAddOverflow":
        return RustcLangItemPanicAddOverflow()
    if __tag == "PanicSubOverflow":
        return RustcLangItemPanicSubOverflow()
    if __tag == "PanicMulOverflow":
        return RustcLangItemPanicMulOverflow()
    if __tag == "PanicDivOverflow":
        return RustcLangItemPanicDivOverflow()
    if __tag == "PanicRemOverflow":
        return RustcLangItemPanicRemOverflow()
    if __tag == "PanicNegOverflow":
        return RustcLangItemPanicNegOverflow()
    if __tag == "PanicShrOverflow":
        return RustcLangItemPanicShrOverflow()
    if __tag == "PanicShlOverflow":
        return RustcLangItemPanicShlOverflow()
    if __tag == "PanicDivZero":
        return RustcLangItemPanicDivZero()
    if __tag == "PanicRemZero":
        return RustcLangItemPanicRemZero()
    if __tag == "PanicCoroutineResumed":
        return RustcLangItemPanicCoroutineResumed()
    if __tag == "PanicAsyncFnResumed":
        return RustcLangItemPanicAsyncFnResumed()
    if __tag == "PanicAsyncGenFnResumed":
        return RustcLangItemPanicAsyncGenFnResumed()
    if __tag == "PanicGenFnNone":
        return RustcLangItemPanicGenFnNone()
    if __tag == "PanicCoroutineResumedPanic":
        return RustcLangItemPanicCoroutineResumedPanic()
    if __tag == "PanicAsyncFnResumedPanic":
        return RustcLangItemPanicAsyncFnResumedPanic()
    if __tag == "PanicAsyncGenFnResumedPanic":
        return RustcLangItemPanicAsyncGenFnResumedPanic()
    if __tag == "PanicGenFnNonePanic":
        return RustcLangItemPanicGenFnNonePanic()
    if __tag == "PanicNullPointerDereference":
        return RustcLangItemPanicNullPointerDereference()
    if __tag == "PanicNullReferenceConstructed":
        return RustcLangItemPanicNullReferenceConstructed()
    if __tag == "PanicInvalidEnumConstruction":
        return RustcLangItemPanicInvalidEnumConstruction()
    if __tag == "PanicCoroutineResumedDrop":
        return RustcLangItemPanicCoroutineResumedDrop()
    if __tag == "PanicAsyncFnResumedDrop":
        return RustcLangItemPanicAsyncFnResumedDrop()
    if __tag == "PanicAsyncGenFnResumedDrop":
        return RustcLangItemPanicAsyncGenFnResumedDrop()
    if __tag == "PanicGenFnNoneDrop":
        return RustcLangItemPanicGenFnNoneDrop()
    if __tag == "BeginPanic":
        return RustcLangItemBeginPanic()
    if __tag == "FormatArgument":
        return RustcLangItemFormatArgument()
    if __tag == "FormatArguments":
        return RustcLangItemFormatArguments()
    if __tag == "DropGlue":
        return RustcLangItemDropGlue()
    if __tag == "AllocLayout":
        return RustcLangItemAllocLayout()
    if __tag == "Start":
        return RustcLangItemStart()
    if __tag == "EhPersonality":
        return RustcLangItemEhPersonality()
    if __tag == "CompilerMove":
        return RustcLangItemCompilerMove()
    if __tag == "CompilerCopy":
        return RustcLangItemCompilerCopy()
    if __tag == "OwnedBox":
        return RustcLangItemOwnedBox()
    if __tag == "GlobalAlloc":
        return RustcLangItemGlobalAlloc()
    if __tag == "PhantomData":
        return RustcLangItemPhantomData()
    if __tag == "ManuallyDrop":
        return RustcLangItemManuallyDrop()
    if __tag == "MaybeDangling":
        return RustcLangItemMaybeDangling()
    if __tag == "BikeshedGuaranteedNoDrop":
        return RustcLangItemBikeshedGuaranteedNoDrop()
    if __tag == "MaybeUninit":
        return RustcLangItemMaybeUninit()
    if __tag == "Termination":
        return RustcLangItemTermination()
    if __tag == "Try":
        return RustcLangItemTry()
    if __tag == "Tuple":
        return RustcLangItemTuple()
    if __tag == "SliceLen":
        return RustcLangItemSliceLen()
    if __tag == "TryTraitFromResidual":
        return RustcLangItemTryTraitFromResidual()
    if __tag == "TryTraitFromOutput":
        return RustcLangItemTryTraitFromOutput()
    if __tag == "TryTraitBranch":
        return RustcLangItemTryTraitBranch()
    if __tag == "TryTraitFromYeet":
        return RustcLangItemTryTraitFromYeet()
    if __tag == "ResidualIntoTryType":
        return RustcLangItemResidualIntoTryType()
    if __tag == "CoercePointeeValidated":
        return RustcLangItemCoercePointeeValidated()
    if __tag == "ConstParamTy":
        return RustcLangItemConstParamTy()
    if __tag == "Poll":
        return RustcLangItemPoll()
    if __tag == "PollReady":
        return RustcLangItemPollReady()
    if __tag == "PollPending":
        return RustcLangItemPollPending()
    if __tag == "AsyncGenReady":
        return RustcLangItemAsyncGenReady()
    if __tag == "AsyncGenPending":
        return RustcLangItemAsyncGenPending()
    if __tag == "AsyncGenFinished":
        return RustcLangItemAsyncGenFinished()
    if __tag == "ResumeTy":
        return RustcLangItemResumeTy()
    if __tag == "GetContext":
        return RustcLangItemGetContext()
    if __tag == "Context":
        return RustcLangItemContext()
    if __tag == "FuturePoll":
        return RustcLangItemFuturePoll()
    if __tag == "AsyncIteratorPollNext":
        return RustcLangItemAsyncIteratorPollNext()
    if __tag == "IntoAsyncIterIntoIter":
        return RustcLangItemIntoAsyncIterIntoIter()
    if __tag == "Option":
        return RustcLangItemOption()
    if __tag == "OptionSome":
        return RustcLangItemOptionSome()
    if __tag == "OptionNone":
        return RustcLangItemOptionNone()
    if __tag == "ResultOk":
        return RustcLangItemResultOk()
    if __tag == "ResultErr":
        return RustcLangItemResultErr()
    if __tag == "ControlFlowContinue":
        return RustcLangItemControlFlowContinue()
    if __tag == "ControlFlowBreak":
        return RustcLangItemControlFlowBreak()
    if __tag == "IntoFutureIntoFuture":
        return RustcLangItemIntoFutureIntoFuture()
    if __tag == "IntoIterIntoIter":
        return RustcLangItemIntoIterIntoIter()
    if __tag == "IteratorNext":
        return RustcLangItemIteratorNext()
    if __tag == "PinNewUnchecked":
        return RustcLangItemPinNewUnchecked()
    if __tag == "RangeFrom":
        return RustcLangItemRangeFrom()
    if __tag == "RangeFull":
        return RustcLangItemRangeFull()
    if __tag == "RangeInclusiveStruct":
        return RustcLangItemRangeInclusiveStruct()
    if __tag == "RangeInclusiveNew":
        return RustcLangItemRangeInclusiveNew()
    if __tag == "Range":
        return RustcLangItemRange()
    if __tag == "RangeToInclusive":
        return RustcLangItemRangeToInclusive()
    if __tag == "RangeTo":
        return RustcLangItemRangeTo()
    if __tag == "RangeMax":
        return RustcLangItemRangeMax()
    if __tag == "RangeMin":
        return RustcLangItemRangeMin()
    if __tag == "RangeSub":
        return RustcLangItemRangeSub()
    if __tag == "RangeFromCopy":
        return RustcLangItemRangeFromCopy()
    if __tag == "RangeCopy":
        return RustcLangItemRangeCopy()
    if __tag == "RangeInclusiveCopy":
        return RustcLangItemRangeInclusiveCopy()
    if __tag == "RangeToInclusiveCopy":
        return RustcLangItemRangeToInclusiveCopy()
    if __tag == "String":
        return RustcLangItemString()
    if __tag == "CStr":
        return RustcLangItemCStr()
    if __tag == "ContractBuildCheckEnsures":
        return RustcLangItemContractBuildCheckEnsures()
    if __tag == "ContractCheckRequires":
        return RustcLangItemContractCheckRequires()
    if __tag == "DefaultTrait4":
        return RustcLangItemDefaultTrait4()
    if __tag == "DefaultTrait3":
        return RustcLangItemDefaultTrait3()
    if __tag == "DefaultTrait2":
        return RustcLangItemDefaultTrait2()
    if __tag == "DefaultTrait1":
        return RustcLangItemDefaultTrait1()
    if __tag == "ContractCheckEnsures":
        return RustcLangItemContractCheckEnsures()
    if __tag == "Reborrow":
        return RustcLangItemReborrow()
    if __tag == "CoerceShared":
        return RustcLangItemCoerceShared()
    if __tag == "FieldRepresentingType":
        return RustcLangItemFieldRepresentingType()
    if __tag == "Field":
        return RustcLangItemField()
    if __tag == "FieldBase":
        return RustcLangItemFieldBase()
    if __tag == "FieldType":
        return RustcLangItemFieldType()
    if __tag == "FieldOffset":
        return RustcLangItemFieldOffset()
    if __tag == "From":
        return RustcLangItemFrom()
    if __tag == "FromFn":
        return RustcLangItemFromFn()
    raise unknown_variant("RustcLangItem", __tag)

def layout_of_json(ctx: OfJsonCtx, js: Json) -> Layout:
    __fields = expect_object(js)
    size = size_expr_of_json(ctx, __fields["size"])
    align = size_expr_of_json(ctx, __fields["align"])
    discriminator = option_of_json(discriminator_of_json)(ctx, __fields["discriminator"])
    uninhabited = bool_of_json(ctx, __fields["uninhabited"])
    variant_layouts = list_of_json(option_of_json(variant_layout_of_json))(ctx, __fields["variant_layouts"])
    repr = repr_options_of_json(ctx, __fields["repr"])
    return Layout(size, align, discriminator, uninhabited, variant_layouts, repr)

def lifetime_mutability_of_json(ctx: OfJsonCtx, js: Json) -> LifetimeMutability:
    __tag, __payload = split_variant(js)
    if __tag == "Mutable":
        return LifetimeMutabilityLtMutable()
    if __tag == "Shared":
        return LifetimeMutabilityLtShared()
    if __tag == "Unknown":
        return LifetimeMutabilityLtUnknown()
    raise unknown_variant("LifetimeMutability", __tag)

def loc_of_json(ctx: OfJsonCtx, js: Json) -> Loc:
    __fields = expect_object(js)
    line = int_of_json(ctx, __fields["line"])
    col = int_of_json(ctx, __fields["col"])
    return Loc(line, col)

def local_of_json(ctx: OfJsonCtx, js: Json) -> Local:
    __fields = expect_object(js)
    index = local_id_of_json(ctx, __fields["index"])
    name = option_of_json(string_of_json)(ctx, __fields["name"])
    span = span_of_json(ctx, __fields["span"])
    local_ty = ty_of_json(ctx, __fields["ty"])
    return Local(index, name, span, local_ty)

def local_id_of_json(ctx: OfJsonCtx, js: Json) -> LocalId:
    return LocalId(int_of_json(ctx, js))

def locals_of_json(ctx: OfJsonCtx, js: Json) -> Locals:
    __fields = expect_object(js)
    arg_count = int_of_json(ctx, __fields["arg_count"])
    locals = list_of_json(local_of_json)(ctx, __fields["locals"])
    return Locals(arg_count, locals)

def maybe_assoc_item_id_of_json(ctx: OfJsonCtx, js: Json) -> MaybeAssocItemId:
    __tag, __payload = split_variant(js)
    if __tag == "Free":
        _0 = item_id_of_json(ctx, __payload)
        return MaybeAssocItemIdItemFree(_0)
    if __tag == "Assoc":
        __items = expect_list(__payload, 2)
        _0 = trait_decl_id_of_json(ctx, __items[0])
        _1 = assoc_item_id_of_json(ctx, __items[1])
        return MaybeAssocItemIdItemAssoc(_0, _1)
    raise unknown_variant("MaybeAssocItemId", __tag)

def metadata_value_of_json(ctx: OfJsonCtx, js: Json) -> MetadataValue:
    __tag, __payload = split_variant(js)
    if __tag == "DynSize":
        return MetadataValueDynSize()
    if __tag == "DynAlign":
        return MetadataValueDynAlign()
    if __tag == "SliceLength":
        return MetadataValueSliceLength()
    raise unknown_variant("MetadataValue", __tag)

def mir_level_of_json(ctx: OfJsonCtx, js: Json) -> MirLevel:
    __tag, __payload = split_variant(js)
    if __tag == "Built":
        return MirLevelBuilt()
    if __tag == "Promoted":
        return MirLevelPromoted()
    if __tag == "Elaborated":
        return MirLevelElaborated()
    if __tag == "Optimized":
        return MirLevelOptimized()
    raise unknown_variant("MirLevel", __tag)

def monomorphize_mut_of_json(ctx: OfJsonCtx, js: Json) -> MonomorphizeMut:
    __tag, __payload = split_variant(js)
    if __tag == "All":
        return MonomorphizeMutAll()
    if __tag == "ExceptTypes":
        return MonomorphizeMutExceptTypes()
    raise unknown_variant("MonomorphizeMut", __tag)

def name_of_json(ctx: OfJsonCtx, js: Json) -> Name:
    return list_of_json(path_elem_of_json)(ctx, js)

def nullop_of_json(ctx: OfJsonCtx, js: Json) -> Nullop:
    __tag, __payload = split_variant(js)
    if __tag == "SizeOf":
        return NullopSizeOf()
    if __tag == "AlignOf":
        return NullopAlignOf()
    if __tag == "OffsetOf":
        __items = expect_list(__payload, 3)
        _0 = type_decl_ref_of_json(ctx, __items[0])
        _1 = option_of_json(variant_id_of_json)(ctx, __items[1])
        _2 = field_id_of_json(ctx, __items[2])
        return NullopOffsetOf(_0, _1, _2)
    if __tag == "UbChecks":
        return NullopUbChecks()
    if __tag == "OverflowChecks":
        return NullopOverflowChecks()
    if __tag == "ContractChecks":
        return NullopContractChecks()
    raise unknown_variant("Nullop", __tag)

def offset_expr_of_json(ctx: OfJsonCtx, js: Json) -> OffsetExpr:
    __fields = expect_object(js)
    guarantee = option_of_json(offset_guarantee_of_json)(ctx, __fields["guarantee"])
    chosen = option_of_json(int_of_json)(ctx, __fields["chosen"])
    return OffsetExpr(guarantee, chosen)

def offset_guarantee_of_json(ctx: OfJsonCtx, js: Json) -> OffsetGuarantee:
    __tag, __payload = split_variant(js)
    if __tag == "AtOffsetZero":
        return OffsetGuaranteeAtOffsetZero()
    if __tag == "GuaranteedAlignment":
        _0 = exact_size_expr_of_json(ctx, __payload)
        return OffsetGuaranteeGuaranteedAlignment(_0)
    if __tag == "ReprCField":
        __fields = expect_object(__payload)
        predecessor = option_of_json(field_id_of_json)(ctx, __fields["predecessor"])
        return OffsetGuaranteeReprCField(predecessor)
    raise unknown_variant("OffsetGuarantee", __tag)

def operand_of_json(ctx: OfJsonCtx, js: Json) -> Operand:
    __tag, __payload = split_variant(js)
    if __tag == "Copy":
        _0 = place_of_json(ctx, __payload)
        return OperandCopy(_0)
    if __tag == "Move":
        _0 = place_of_json(ctx, __payload)
        return OperandMove(_0)
    if __tag == "Const":
        _0 = constant_expr_of_json(ctx, __payload)
        return OperandConstant(_0)
    raise unknown_variant("Operand", __tag)

def rustc_optimize_attr_of_json(ctx: OfJsonCtx, js: Json) -> RustcOptimizeAttr:
    __tag, __payload = split_variant(js)
    if __tag == "Default":
        return RustcOptimizeAttrDefault()
    if __tag == "DoNotOptimize":
        return RustcOptimizeAttrDoNotOptimize()
    if __tag == "Speed":
        return RustcOptimizeAttrSpeed()
    if __tag == "Size":
        return RustcOptimizeAttrSize()
    raise unknown_variant("RustcOptimizeAttr", __tag)

def outlives_pred_of_json(arg0_of_json: JsonDecoder[T0], arg1_of_json: JsonDecoder[T1]) -> JsonDecoder[OutlivesPred[T0, T1]]:
    def read(ctx: OfJsonCtx, js: Json) -> OutlivesPred[T0, T1]:
        __items = expect_list(js, 2)
        _0 = arg0_of_json(ctx, __items[0])
        _1 = arg1_of_json(ctx, __items[1])
        return OutlivesPred(_0, _1)
    return read

def overflow_mode_of_json(ctx: OfJsonCtx, js: Json) -> OverflowMode:
    __tag, __payload = split_variant(js)
    if __tag == "Panic":
        return OverflowModeOPanic()
    if __tag == "UB":
        return OverflowModeOUB()
    if __tag == "Wrap":
        return OverflowModeOWrap()
    raise unknown_variant("OverflowMode", __tag)

def path_elem_of_json(ctx: OfJsonCtx, js: Json) -> PathElem:
    __tag, __payload = split_variant(js)
    if __tag == "Ident":
        __items = expect_list(__payload, 2)
        _0 = string_of_json(ctx, __items[0])
        _1 = disambiguator_of_json(ctx, __items[1])
        return PathElemPeIdent(_0, _1)
    if __tag == "Impl":
        _0 = impl_elem_of_json(ctx, __payload)
        return PathElemPeImpl(_0)
    if __tag == "Instantiated":
        _0 = box_of_json(binder_of_json(generic_args_of_json))(ctx, __payload)
        return PathElemPeInstantiated(_0)
    if __tag == "Target":
        _0 = string_of_json(ctx, __payload)
        return PathElemPeTarget(_0)
    if __tag == "Builtin":
        __items = expect_list(__payload, 2)
        _0 = builtin_path_elem_of_json(ctx, __items[0])
        _1 = disambiguator_of_json(ctx, __items[1])
        return PathElemPeBuiltin(_0, _1)
    raise unknown_variant("PathElem", __tag)

def place_of_json(ctx: OfJsonCtx, js: Json) -> Place:
    __fields = expect_object(js)
    kind = place_kind_of_json(ctx, __fields["kind"])
    ty = ty_of_json(ctx, __fields["ty"])
    return Place(kind, ty)

def place_kind_of_json(ctx: OfJsonCtx, js: Json) -> PlaceKind:
    __tag, __payload = split_variant(js)
    if __tag == "Local":
        _0 = local_id_of_json(ctx, __payload)
        return PlaceKindPlaceLocal(_0)
    if __tag == "Projection":
        __items = expect_list(__payload, 2)
        _0 = box_of_json(place_of_json)(ctx, __items[0])
        _1 = projection_elem_of_json(ctx, __items[1])
        return PlaceKindPlaceProjection(_0, _1)
    if __tag == "Global":
        _0 = global_decl_ref_of_json(ctx, __payload)
        return PlaceKindPlaceGlobal(_0)
    raise unknown_variant("PlaceKind", __tag)

def predicate_origin_of_json(ctx: OfJsonCtx, js: Json) -> PredicateOrigin:
    __tag, __payload = split_variant(js)
    if __tag == "WhereClauseOnFn":
        return PredicateOriginWhereClauseOnFn()
    if __tag == "WhereClauseOnType":
        return PredicateOriginWhereClauseOnType()
    if __tag == "WhereClauseOnImpl":
        return PredicateOriginWhereClauseOnImpl()
    if __tag == "TraitSelf":
        return PredicateOriginTraitSelf()
    if __tag == "WhereClauseOnTrait":
        return PredicateOriginWhereClauseOnTrait()
    if __tag == "TraitItem":
        _0 = assoc_type_id_of_json(ctx, __payload)
        return PredicateOriginTraitItem(_0)
    if __tag == "Dyn":
        return PredicateOriginOriginDyn()
    raise unknown_variant("PredicateOrigin", __tag)

def preset_of_json(ctx: OfJsonCtx, js: Json) -> Preset:
    __tag, __payload = split_variant(js)
    if __tag == "OldDefaults":
        return PresetOldDefaults()
    if __tag == "RawMir":
        return PresetRawMir()
    if __tag == "Fast":
        return PresetFast()
    if __tag == "Aeneas":
        return PresetAeneas()
    if __tag == "Eurydice":
        return PresetEurydice()
    if __tag == "Soteria":
        return PresetSoteria()
    if __tag == "Tests":
        return PresetTests()
    raise unknown_variant("Preset", __tag)

def projection_elem_of_json(ctx: OfJsonCtx, js: Json) -> ProjectionElem:
    __tag, __payload = split_variant(js)
    if __tag == "Deref":
        return ProjectionElemDeref()
    if __tag == "Field":
        __items = expect_list(__payload, 2)
        _0 = option_of_json(variant_id_of_json)(ctx, __items[0])
        _1 = field_id_of_json(ctx, __items[1])
        return ProjectionElemField(_0, _1)
    if __tag == "PtrMetadata":
        return ProjectionElemPtrMetadata()
    if __tag == "Index":
        __fields = expect_object(__payload)
        offset = box_of_json(operand_of_json)(ctx, __fields["offset"])
        from_end = bool_of_json(ctx, __fields["from_end"])
        return ProjectionElemProjIndex(offset, from_end)
    if __tag == "Subslice":
        __fields = expect_object(__payload)
        from_ = box_of_json(operand_of_json)(ctx, __fields["from"])
        to = box_of_json(operand_of_json)(ctx, __fields["to"])
        from_end = bool_of_json(ctx, __fields["from_end"])
        return ProjectionElemSubslice(from_, to, from_end)
    raise unknown_variant("ProjectionElem", __tag)

def provenance_of_json(ctx: OfJsonCtx, js: Json) -> Provenance:
    __tag, __payload = split_variant(js)
    if __tag == "Global":
        _0 = global_decl_ref_of_json(ctx, __payload)
        return ProvenanceProvGlobal(_0)
    if __tag == "Function":
        _0 = fun_decl_ref_of_json(ctx, __payload)
        return ProvenanceProvFunction(_0)
    if __tag == "Unknown":
        return ProvenanceProvUnknown()
    raise unknown_variant("Provenance", __tag)

def ptr_metadata_of_json(ctx: OfJsonCtx, js: Json) -> PtrMetadata:
    __tag, __payload = split_variant(js)
    if __tag == "None":
        return PtrMetadataNoMetadata()
    if __tag == "Length":
        return PtrMetadataLength()
    if __tag == "VTable":
        _0 = type_decl_ref_of_json(ctx, __payload)
        return PtrMetadataVTable(_0)
    if __tag == "InheritFrom":
        _0 = ty_of_json(ctx, __payload)
        return PtrMetadataInheritFrom(_0)
    raise unknown_variant("PtrMetadata", __tag)

def raw_attribute_of_json(ctx: OfJsonCtx, js: Json) -> RawAttribute:
    __fields = expect_object(js)
    path = string_of_json(ctx, __fields["path"])
    args = option_of_json(string_of_json)(ctx, __fields["args"])
    return RawAttribute(path, args)

def ref_kind_of_json(ctx: OfJsonCtx, js: Json) -> RefKind:
    __tag, __payload = split_variant(js)
    if __tag == "Mut":
        return RefKindRMut()
    if __tag == "Shared":
        return RefKindRShared()
    raise unknown_variant("RefKind", __tag)

def region_of_json(ctx: OfJsonCtx, js: Json) -> Region:
    __tag, __payload = split_variant(js)
    if __tag == "Var":
        _0 = de_bruijn_var_of_json(region_id_of_json)(ctx, __payload)
        return RegionRVar(_0)
    if __tag == "Static":
        return RegionRStatic()
    if __tag == "Body":
        _0 = region_id_of_json(ctx, __payload)
        return RegionRBody(_0)
    if __tag == "Erased":
        return RegionRErased()
    raise unknown_variant("Region", __tag)

def region_binder_of_json(arg0_of_json: JsonDecoder[T0]) -> JsonDecoder[RegionBinder[T0]]:
    def read(ctx: OfJsonCtx, js: Json) -> RegionBinder[T0]:
        __fields = expect_object(js)
        binder_regions = list_of_json(region_param_of_json)(ctx, __fields["regions"])
        binder_value = arg0_of_json(ctx, __fields["skip_binder"])
        return RegionBinder(binder_regions, binder_value)
    return read

def region_id_of_json(ctx: OfJsonCtx, js: Json) -> RegionId:
    return RegionId(int_of_json(ctx, js))

def region_param_of_json(ctx: OfJsonCtx, js: Json) -> RegionParam:
    __fields = expect_object(js)
    index = region_id_of_json(ctx, __fields["index"])
    name = option_of_json(string_of_json)(ctx, __fields["name"])
    variance = variance_of_json(ctx, __fields["variance"])
    mutability = lifetime_mutability_of_json(ctx, __fields["mutability"])
    return RegionParam(index, name, variance, mutability)

def repr_algorithm_of_json(ctx: OfJsonCtx, js: Json) -> ReprAlgorithm:
    __tag, __payload = split_variant(js)
    if __tag == "Rust":
        return ReprAlgorithmRust()
    if __tag == "C":
        return ReprAlgorithmC()
    raise unknown_variant("ReprAlgorithm", __tag)

def repr_options_of_json(ctx: OfJsonCtx, js: Json) -> ReprOptions:
    __fields = expect_object(js)
    repr_algo = repr_algorithm_of_json(ctx, __fields["repr_algo"])
    align_modif = option_of_json(alignment_modifier_of_json)(ctx, __fields["align_modif"])
    transparent = bool_of_json(ctx, __fields["transparent"])
    explicit_discr_type = option_of_json(integer_type_of_json)(ctx, __fields["explicit_discr_type"])
    return ReprOptions(repr_algo, align_modif, transparent, explicit_discr_type)

def rustc_rustc_version_of_json(ctx: OfJsonCtx, js: Json) -> RustcRustcVersion:
    __fields = expect_object(js)
    major = int_of_json(ctx, __fields["major"])
    minor = int_of_json(ctx, __fields["minor"])
    patch = int_of_json(ctx, __fields["patch"])
    return RustcRustcVersion(major, minor, patch)

def rvalue_of_json(ctx: OfJsonCtx, js: Json) -> Rvalue:
    __tag, __payload = split_variant(js)
    if __tag == "Use":
        __items = expect_list(__payload, 2)
        _0 = operand_of_json(ctx, __items[0])
        _1 = with_retag_of_json(ctx, __items[1])
        return RvalueUse(_0, _1)
    if __tag == "Ref":
        __fields = expect_object(__payload)
        place = place_of_json(ctx, __fields["place"])
        kind = borrow_kind_of_json(ctx, __fields["kind"])
        ptr_metadata = operand_of_json(ctx, __fields["ptr_metadata"])
        return RvalueRvRef(place, kind, ptr_metadata)
    if __tag == "RawPtr":
        __fields = expect_object(__payload)
        place = place_of_json(ctx, __fields["place"])
        kind = ref_kind_of_json(ctx, __fields["kind"])
        ptr_metadata = operand_of_json(ctx, __fields["ptr_metadata"])
        return RvalueRawPtr(place, kind, ptr_metadata)
    if __tag == "BinaryOp":
        __items = expect_list(__payload, 3)
        _0 = binop_of_json(ctx, __items[0])
        _1 = operand_of_json(ctx, __items[1])
        _2 = operand_of_json(ctx, __items[2])
        return RvalueBinaryOp(_0, _1, _2)
    if __tag == "UnaryOp":
        __items = expect_list(__payload, 2)
        _0 = unop_of_json(ctx, __items[0])
        _1 = operand_of_json(ctx, __items[1])
        return RvalueUnaryOp(_0, _1)
    if __tag == "NullaryOp":
        __items = expect_list(__payload, 2)
        _0 = nullop_of_json(ctx, __items[0])
        _1 = ty_of_json(ctx, __items[1])
        return RvalueNullaryOp(_0, _1)
    if __tag == "Discriminant":
        _0 = place_of_json(ctx, __payload)
        return RvalueDiscriminant(_0)
    if __tag == "Aggregate":
        __items = expect_list(__payload, 2)
        _0 = aggregate_kind_of_json(ctx, __items[0])
        _1 = list_of_json(operand_of_json)(ctx, __items[1])
        return RvalueAggregate(_0, _1)
    if __tag == "Len":
        __items = expect_list(__payload, 3)
        _0 = place_of_json(ctx, __items[0])
        _1 = ty_of_json(ctx, __items[1])
        _2 = option_of_json(constant_expr_of_json)(ctx, __items[2])
        return RvalueLen(_0, _1, _2)
    if __tag == "Repeat":
        __items = expect_list(__payload, 4)
        _0 = operand_of_json(ctx, __items[0])
        _1 = ty_of_json(ctx, __items[1])
        _2 = constant_expr_of_json(ctx, __items[2])
        _3 = trait_ref_of_json(ctx, __items[3])
        return RvalueRepeat(_0, _1, _2, _3)
    raise unknown_variant("Rvalue", __tag)

def scalar_type_of_json(ctx: OfJsonCtx, js: Json) -> ScalarType:
    __tag, __payload = split_variant(js)
    if __tag == "Integer":
        _0 = integer_type_of_json(ctx, __payload)
        return ScalarTypeTInteger(_0)
    if __tag == "Float":
        _0 = float_type_of_json(ctx, __payload)
        return ScalarTypeTFloat(_0)
    if __tag == "Bool":
        return ScalarTypeTBool()
    if __tag == "Char":
        return ScalarTypeTChar()
    raise unknown_variant("ScalarType", __tag)

def serialization_format_arg_of_json(ctx: OfJsonCtx, js: Json) -> SerializationFormatArg:
    __tag, __payload = split_variant(js)
    if __tag == "Json":
        return SerializationFormatArgJson()
    if __tag == "Postcard":
        return SerializationFormatArgPostcard()
    if __tag == "All":
        return SerializationFormatArgAllFormats()
    raise unknown_variant("SerializationFormatArg", __tag)

def size_expr_of_json(ctx: OfJsonCtx, js: Json) -> SizeExpr:
    __fields = expect_object(js)
    guarantee = option_of_json(size_guarantee_of_json)(ctx, __fields["guarantee"])
    chosen = option_of_json(int_of_json)(ctx, __fields["chosen"])
    return SizeExpr(guarantee, chosen)

def size_guarantee_of_json(ctx: OfJsonCtx, js: Json) -> SizeGuarantee:
    __tag, __payload = split_variant(js)
    if __tag == "Equals":
        _0 = exact_size_expr_of_json(ctx, __payload)
        return SizeGuaranteeEquals(_0)
    if __tag == "AtLeast":
        _0 = exact_size_expr_of_json(ctx, __payload)
        return SizeGuaranteeAtLeast(_0)
    raise unknown_variant("SizeGuarantee", __tag)

def span_of_json(ctx: OfJsonCtx, js: Json) -> Span:
    def read_contents(ctx: OfJsonCtx, js: Json) -> Span:
        __fields = expect_object(js)
        return Span(
            data=span_data_of_json(ctx, __fields["data"]),
            generated_from_span=option_of_json(span_data_of_json)(
                ctx, __fields["generated_from_span"]
            ),
        )

    return dedup_val_of_json(ctx.span_dedup, read_contents)(ctx, js)

def span_data_of_json(ctx: OfJsonCtx, js: Json) -> SpanData:
    __fields = expect_object(js)
    file = file_id_of_json(ctx, __fields["file_id"])
    beg_loc = loc_of_json(ctx, __fields["beg"])
    end_loc = loc_of_json(ctx, __fields["end"])
    return SpanData(file, beg_loc, end_loc)

def ullbc_statement_of_json(ctx: OfJsonCtx, js: Json) -> UllbcStatement:
    __fields = expect_object(js)
    span = span_of_json(ctx, __fields["span"])
    kind = ullbc_statement_kind_of_json(ctx, __fields["kind"])
    comments_before = list_of_json(string_of_json)(ctx, __fields["comments_before"])
    return UllbcStatement(span, kind, comments_before)

def llbc_statement_of_json(ctx: OfJsonCtx, js: Json) -> LlbcStatement:
    __fields = expect_object(js)
    span = span_of_json(ctx, __fields["span"])
    statement_id = statement_id_of_json(ctx, __fields["id"])
    kind = llbc_statement_kind_of_json(ctx, __fields["kind"])
    comments_before = list_of_json(string_of_json)(ctx, __fields["comments_before"])
    return LlbcStatement(span, statement_id, kind, comments_before)

def statement_id_of_json(ctx: OfJsonCtx, js: Json) -> StatementId:
    return StatementId(int_of_json(ctx, js))

def ullbc_statement_kind_of_json(ctx: OfJsonCtx, js: Json) -> UllbcStatementKind:
    __tag, __payload = split_variant(js)
    if __tag == "Assign":
        __items = expect_list(__payload, 2)
        _0 = place_of_json(ctx, __items[0])
        _1 = rvalue_of_json(ctx, __items[1])
        return UllbcStatementKindAssign(_0, _1)
    if __tag == "SetDiscriminant":
        __items = expect_list(__payload, 2)
        _0 = place_of_json(ctx, __items[0])
        _1 = variant_id_of_json(ctx, __items[1])
        return UllbcStatementKindSetDiscriminant(_0, _1)
    if __tag == "StorageLive":
        _0 = local_id_of_json(ctx, __payload)
        return UllbcStatementKindStorageLive(_0)
    if __tag == "StorageDead":
        _0 = local_id_of_json(ctx, __payload)
        return UllbcStatementKindStorageDead(_0)
    if __tag == "PlaceMention":
        _0 = place_of_json(ctx, __payload)
        return UllbcStatementKindPlaceMention(_0)
    if __tag == "Borrowck":
        _0 = borrowck_statement_of_json(ctx, __payload)
        return UllbcStatementKindBorrowck(_0)
    if __tag == "Assert":
        __fields = expect_object(__payload)
        assert_ = assertion_of_json(ctx, __fields["assert"])
        on_failure = abort_kind_of_json(ctx, __fields["on_failure"])
        return UllbcStatementKindAssert(assert_, on_failure)
    if __tag == "Nop":
        return UllbcStatementKindNop()
    raise unknown_variant("UllbcStatementKind", __tag)

def llbc_statement_kind_of_json(ctx: OfJsonCtx, js: Json) -> LlbcStatementKind:
    __tag, __payload = split_variant(js)
    if __tag == "Assign":
        __items = expect_list(__payload, 2)
        _0 = place_of_json(ctx, __items[0])
        _1 = rvalue_of_json(ctx, __items[1])
        return LlbcStatementKindAssign(_0, _1)
    if __tag == "SetDiscriminant":
        __items = expect_list(__payload, 2)
        _0 = place_of_json(ctx, __items[0])
        _1 = variant_id_of_json(ctx, __items[1])
        return LlbcStatementKindSetDiscriminant(_0, _1)
    if __tag == "StorageLive":
        _0 = local_id_of_json(ctx, __payload)
        return LlbcStatementKindStorageLive(_0)
    if __tag == "StorageDead":
        _0 = local_id_of_json(ctx, __payload)
        return LlbcStatementKindStorageDead(_0)
    if __tag == "PlaceMention":
        _0 = place_of_json(ctx, __payload)
        return LlbcStatementKindPlaceMention(_0)
    if __tag == "Borrowck":
        _0 = borrowck_statement_of_json(ctx, __payload)
        return LlbcStatementKindBorrowck(_0)
    if __tag == "Drop":
        __fields = expect_object(__payload)
        place = place_of_json(ctx, __fields["place"])
        fn_ptr = fn_ptr_of_json(ctx, __fields["fn_ptr"])
        kind = drop_kind_of_json(ctx, __fields["kind"])
        on_unwind = llbc_block_of_json(ctx, __fields["on_unwind"])
        return LlbcStatementKindDrop(place, fn_ptr, kind, on_unwind)
    if __tag == "Assert":
        __fields = expect_object(__payload)
        assert_ = assertion_of_json(ctx, __fields["assert"])
        on_failure = abort_kind_of_json(ctx, __fields["on_failure"])
        on_unwind = llbc_block_of_json(ctx, __fields["on_unwind"])
        return LlbcStatementKindAssert(assert_, on_failure, on_unwind)
    if __tag == "InlineAsm":
        __fields = expect_object(__payload)
        asm = string_of_json(ctx, __fields["asm"])
        targets = list_of_json(llbc_block_of_json)(ctx, __fields["targets"])
        on_unwind = llbc_block_of_json(ctx, __fields["on_unwind"])
        return LlbcStatementKindInlineAsm(asm, targets, on_unwind)
    if __tag == "Call":
        __fields = expect_object(__payload)
        call = call_of_json(ctx, __fields["call"])
        on_unwind = llbc_block_of_json(ctx, __fields["on_unwind"])
        return LlbcStatementKindCall(call, on_unwind)
    if __tag == "Abort":
        _0 = abort_kind_of_json(ctx, __payload)
        return LlbcStatementKindAbort(_0)
    if __tag == "Return":
        return LlbcStatementKindReturn()
    if __tag == "UnwindResume":
        return LlbcStatementKindUnwindResume()
    if __tag == "Break":
        _0 = int_of_json(ctx, __payload)
        return LlbcStatementKindBreak(_0)
    if __tag == "Continue":
        _0 = int_of_json(ctx, __payload)
        return LlbcStatementKindContinue(_0)
    if __tag == "Nop":
        return LlbcStatementKindNop()
    if __tag == "Switch":
        __fields = expect_object(__payload)
        data = switch_data_of_json(ctx, __fields["data"])
        branches = list_of_json(llbc_block_of_json)(ctx, __fields["branches"])
        return LlbcStatementKindSwitch(data, branches)
    if __tag == "Loop":
        _0 = llbc_block_of_json(ctx, __payload)
        return LlbcStatementKindLoop(_0)
    if __tag == "Error":
        _0 = string_of_json(ctx, __payload)
        return LlbcStatementKindError(_0)
    raise unknown_variant("LlbcStatementKind", __tag)

def switch_data_of_json(ctx: OfJsonCtx, js: Json) -> SwitchData:
    __fields = expect_object(js)
    scrutinee = switch_scrutinee_of_json(ctx, __fields["scrutinee"])
    branches = list_of_json(pair_of_json(constant_expr_of_json, branch_id_of_json))(ctx, __fields["branches"])
    fallback = option_of_json(branch_id_of_json)(ctx, __fields["fallback"])
    return SwitchData(scrutinee, branches, fallback)

def switch_scrutinee_of_json(ctx: OfJsonCtx, js: Json) -> SwitchScrutinee:
    __tag, __payload = split_variant(js)
    if __tag == "Value":
        _0 = operand_of_json(ctx, __payload)
        return SwitchScrutineeSwitchValue(_0)
    if __tag == "Discriminant":
        _0 = place_of_json(ctx, __payload)
        return SwitchScrutineeSwitchDiscriminant(_0)
    raise unknown_variant("SwitchScrutinee", __tag)

def target_info_of_json(ctx: OfJsonCtx, js: Json) -> TargetInfo:
    __fields = expect_object(js)
    target_pointer_size = int_of_json(ctx, __fields["target_pointer_size"])
    is_little_endian = bool_of_json(ctx, __fields["is_little_endian"])
    c_enum_smallest_repr_ty = int_ty_of_json(ctx, __fields["c_enum_smallest_repr_ty"])
    primitive_alignments = list_of_json(key_value_pair_of_json(scalar_type_of_json, int_of_json))(ctx, __fields["primitive_alignments"])
    return TargetInfo(target_pointer_size, is_little_endian, c_enum_smallest_repr_ty, primitive_alignments)

def terminator_of_json(ctx: OfJsonCtx, js: Json) -> Terminator:
    __fields = expect_object(js)
    span = span_of_json(ctx, __fields["span"])
    kind = terminator_kind_of_json(ctx, __fields["kind"])
    comments_before = list_of_json(string_of_json)(ctx, __fields["comments_before"])
    return Terminator(span, kind, comments_before)

def terminator_kind_of_json(ctx: OfJsonCtx, js: Json) -> TerminatorKind:
    __tag, __payload = split_variant(js)
    if __tag == "Goto":
        __fields = expect_object(__payload)
        target = ullbc_block_id_of_json(ctx, __fields["target"])
        return TerminatorKindGoto(target)
    if __tag == "Switch":
        __fields = expect_object(__payload)
        data = switch_data_of_json(ctx, __fields["data"])
        branches = list_of_json(ullbc_block_id_of_json)(ctx, __fields["branches"])
        return TerminatorKindSwitch(data, branches)
    if __tag == "Call":
        __fields = expect_object(__payload)
        call = call_of_json(ctx, __fields["call"])
        target = ullbc_block_id_of_json(ctx, __fields["target"])
        on_unwind = ullbc_block_id_of_json(ctx, __fields["on_unwind"])
        return TerminatorKindCall(call, target, on_unwind)
    if __tag == "Drop":
        __fields = expect_object(__payload)
        kind = drop_kind_of_json(ctx, __fields["kind"])
        place = place_of_json(ctx, __fields["place"])
        fn_ptr = fn_ptr_of_json(ctx, __fields["fn_ptr"])
        target = ullbc_block_id_of_json(ctx, __fields["target"])
        on_unwind = ullbc_block_id_of_json(ctx, __fields["on_unwind"])
        return TerminatorKindDrop(kind, place, fn_ptr, target, on_unwind)
    if __tag == "Assert":
        __fields = expect_object(__payload)
        assert_ = assertion_of_json(ctx, __fields["assert"])
        target = ullbc_block_id_of_json(ctx, __fields["target"])
        on_unwind = ullbc_block_id_of_json(ctx, __fields["on_unwind"])
        return TerminatorKindTAssert(assert_, target, on_unwind)
    if __tag == "InlineAsm":
        __fields = expect_object(__payload)
        asm = string_of_json(ctx, __fields["asm"])
        targets = list_of_json(ullbc_block_id_of_json)(ctx, __fields["targets"])
        on_unwind = ullbc_block_id_of_json(ctx, __fields["on_unwind"])
        return TerminatorKindInlineAsm(asm, targets, on_unwind)
    if __tag == "Abort":
        _0 = abort_kind_of_json(ctx, __payload)
        return TerminatorKindAbort(_0)
    if __tag == "Return":
        return TerminatorKindReturn()
    if __tag == "UnwindResume":
        return TerminatorKindUnwindResume()
    raise unknown_variant("TerminatorKind", __tag)

def trait_assoc_const_of_json(ctx: OfJsonCtx, js: Json) -> TraitAssocConst:
    __fields = expect_object(js)
    name = trait_item_name_of_json(ctx, __fields["name"])
    attr_info = attr_info_of_json(ctx, __fields["attr_info"])
    ty = ty_of_json(ctx, __fields["ty"])
    default = option_of_json(global_decl_ref_of_json)(ctx, __fields["default"])
    return TraitAssocConst(name, attr_info, ty, default)

def trait_assoc_ty_of_json(ctx: OfJsonCtx, js: Json) -> TraitAssocTy:
    __fields = expect_object(js)
    name = trait_item_name_of_json(ctx, __fields["name"])
    attr_info = attr_info_of_json(ctx, __fields["attr_info"])
    default = option_of_json(trait_assoc_ty_impl_of_json)(ctx, __fields["default"])
    implied_clauses = list_of_json(trait_param_of_json)(ctx, __fields["implied_clauses"])
    return TraitAssocTy(name, attr_info, default, implied_clauses)

def trait_assoc_ty_impl_of_json(ctx: OfJsonCtx, js: Json) -> TraitAssocTyImpl:
    __fields = expect_object(js)
    value = ty_of_json(ctx, __fields["value"])
    implied_trait_refs = list_of_json(trait_ref_of_json)(ctx, __fields["implied_trait_refs"])
    return TraitAssocTyImpl(value, implied_trait_refs)

def trait_clause_id_of_json(ctx: OfJsonCtx, js: Json) -> TraitClauseId:
    return TraitClauseId(int_of_json(ctx, js))

def trait_decl_of_json(ctx: OfJsonCtx, js: Json) -> TraitDecl:
    __fields = expect_object(js)
    def_id = trait_decl_id_of_json(ctx, __fields["def_id"])
    item_meta = item_meta_of_json(ctx, __fields["item_meta"])
    src = trait_decl_source_of_json(ctx, __fields["src"])
    generics = generic_params_of_json(ctx, __fields["generics"])
    implied_clauses = list_of_json(trait_param_of_json)(ctx, __fields["implied_clauses"])
    consts = indexed_map_of_json(assoc_const_id_of_json, trait_assoc_const_of_json)(ctx, __fields["consts"])
    types = indexed_map_of_json(assoc_type_id_of_json, binder_of_json(trait_assoc_ty_of_json))(ctx, __fields["types"])
    methods = indexed_map_of_json(trait_method_id_of_json, binder_of_json(trait_method_of_json))(ctx, __fields["methods"])
    vtable = option_of_json(type_decl_ref_of_json)(ctx, __fields["vtable"])
    return TraitDecl(def_id, item_meta, src, generics, implied_clauses, consts, types, methods, vtable)

def trait_decl_id_of_json(ctx: OfJsonCtx, js: Json) -> TraitDeclId:
    return TraitDeclId(int_of_json(ctx, js))

def trait_decl_ref_of_json(ctx: OfJsonCtx, js: Json) -> TraitDeclRef:
    __fields = expect_object(js)
    id = trait_decl_id_of_json(ctx, __fields["id"])
    generics = box_of_json(generic_args_of_json)(ctx, __fields["generics"])
    return TraitDeclRef(id, generics)

def trait_decl_source_of_json(ctx: OfJsonCtx, js: Json) -> TraitDeclSource:
    __tag, __payload = split_variant(js)
    if __tag == "Normal":
        return TraitDeclSourceNormalTraitDecl()
    if __tag == "TraitAlias":
        return TraitDeclSourceTraitAliasTraitDecl()
    raise unknown_variant("TraitDeclSource", __tag)

def trait_impl_of_json(ctx: OfJsonCtx, js: Json) -> TraitImpl:
    __fields = expect_object(js)
    def_id = trait_impl_id_of_json(ctx, __fields["def_id"])
    item_meta = item_meta_of_json(ctx, __fields["item_meta"])
    src = trait_impl_source_of_json(ctx, __fields["src"])
    impl_trait = trait_decl_ref_of_json(ctx, __fields["impl_trait"])
    generics = generic_params_of_json(ctx, __fields["generics"])
    implied_trait_refs = list_of_json(trait_ref_of_json)(ctx, __fields["implied_trait_refs"])
    consts = indexed_map_of_json(assoc_const_id_of_json, global_decl_ref_of_json)(ctx, __fields["consts"])
    types = indexed_map_of_json(assoc_type_id_of_json, binder_of_json(trait_assoc_ty_impl_of_json))(ctx, __fields["types"])
    methods = indexed_map_of_json(trait_method_id_of_json, binder_of_json(fun_decl_ref_of_json))(ctx, __fields["methods"])
    vtable = option_of_json(global_decl_ref_of_json)(ctx, __fields["vtable"])
    return TraitImpl(def_id, item_meta, src, impl_trait, generics, implied_trait_refs, consts, types, methods, vtable)

def trait_impl_id_of_json(ctx: OfJsonCtx, js: Json) -> TraitImplId:
    return TraitImplId(int_of_json(ctx, js))

def trait_impl_ref_of_json(ctx: OfJsonCtx, js: Json) -> TraitImplRef:
    __fields = expect_object(js)
    id = trait_impl_id_of_json(ctx, __fields["id"])
    generics = box_of_json(generic_args_of_json)(ctx, __fields["generics"])
    return TraitImplRef(id, generics)

def trait_impl_source_of_json(ctx: OfJsonCtx, js: Json) -> TraitImplSource:
    __tag, __payload = split_variant(js)
    if __tag == "Normal":
        return TraitImplSourceNormalTraitImpl()
    if __tag == "TraitAlias":
        return TraitImplSourceTraitAliasTraitImpl()
    if __tag == "Closure":
        __fields = expect_object(__payload)
        kind = closure_kind_of_json(ctx, __fields["kind"])
        return TraitImplSourceClosureTraitImpl(kind)
    if __tag == "Destruct":
        return TraitImplSourceDestructTraitImpl()
    raise unknown_variant("TraitImplSource", __tag)

def trait_item_name_of_json(ctx: OfJsonCtx, js: Json) -> TraitItemName:
    return string_of_json(ctx, js)

def trait_method_of_json(ctx: OfJsonCtx, js: Json) -> TraitMethod:
    __fields = expect_object(js)
    name = trait_item_name_of_json(ctx, __fields["name"])
    item_meta = item_meta_of_json(ctx, __fields["item_meta"])
    signature = fun_sig_of_json(ctx, __fields["signature"])
    default = option_of_json(fun_decl_ref_of_json)(ctx, __fields["default"])
    return TraitMethod(name, item_meta, signature, default)

def trait_method_id_of_json(ctx: OfJsonCtx, js: Json) -> TraitMethodId:
    return TraitMethodId(int_of_json(ctx, js))

def trait_param_of_json(ctx: OfJsonCtx, js: Json) -> TraitParam:
    __fields = expect_object(js)
    clause_id = trait_clause_id_of_json(ctx, __fields["clause_id"])
    span = option_of_json(span_of_json)(ctx, __fields["span"])
    origin = predicate_origin_of_json(ctx, __fields["origin"])
    trait = region_binder_of_json(trait_decl_ref_of_json)(ctx, __fields["trait_"])
    return TraitParam(clause_id, span, origin, trait)

def trait_ref_of_json(ctx: OfJsonCtx, js: Json) -> TraitRef:
    return dedup_val_of_json(ctx.trait_ref_contents_dedup, trait_ref_contents_of_json)(ctx, js)

def trait_ref_contents_of_json(ctx: OfJsonCtx, js: Json) -> TraitRefContents:
    __fields = expect_object(js)
    kind = trait_ref_kind_of_json(ctx, __fields["kind"])
    trait_decl_ref = region_binder_of_json(trait_decl_ref_of_json)(ctx, __fields["trait_decl_ref"])
    return TraitRefContents(kind, trait_decl_ref)

def trait_ref_kind_of_json(ctx: OfJsonCtx, js: Json) -> TraitRefKind:
    __tag, __payload = split_variant(js)
    if __tag == "TraitImpl":
        _0 = trait_impl_ref_of_json(ctx, __payload)
        return TraitRefKindTraitImpl(_0)
    if __tag == "Clause":
        _0 = de_bruijn_var_of_json(trait_clause_id_of_json)(ctx, __payload)
        return TraitRefKindClause(_0)
    if __tag == "ParentClause":
        __items = expect_list(__payload, 2)
        _0 = trait_ref_of_json(ctx, __items[0])
        _1 = trait_clause_id_of_json(ctx, __items[1])
        return TraitRefKindParentClause(_0, _1)
    if __tag == "ItemClause":
        __items = expect_list(__payload, 3)
        _0 = trait_ref_of_json(ctx, __items[0])
        _1 = assoc_type_id_of_json(ctx, __items[1])
        _2 = trait_clause_id_of_json(ctx, __items[2])
        return TraitRefKindItemClause(_0, _1, _2)
    if __tag == "SelfId":
        return TraitRefKindSelf()
    if __tag == "BuiltinOrAuto":
        __fields = expect_object(__payload)
        builtin_data = builtin_impl_data_of_json(ctx, __fields["builtin_data"])
        parent_trait_refs = list_of_json(trait_ref_of_json)(ctx, __fields["parent_trait_refs"])
        types = indexed_map_of_json(assoc_type_id_of_json, trait_assoc_ty_impl_of_json)(ctx, __fields["types"])
        vtable = option_of_json(global_decl_ref_of_json)(ctx, __fields["vtable"])
        return TraitRefKindBuiltinOrAuto(builtin_data, parent_trait_refs, types, vtable)
    if __tag == "Dyn":
        return TraitRefKindDyn()
    if __tag == "Unknown":
        _0 = string_of_json(ctx, __payload)
        return TraitRefKindUnknownTrait(_0)
    raise unknown_variant("TraitRefKind", __tag)

def trait_type_constraint_of_json(ctx: OfJsonCtx, js: Json) -> TraitTypeConstraint:
    __fields = expect_object(js)
    trait_ref = trait_ref_of_json(ctx, __fields["trait_ref"])
    type_id = assoc_type_id_of_json(ctx, __fields["type_id"])
    ty = ty_of_json(ctx, __fields["ty"])
    return TraitTypeConstraint(trait_ref, type_id, ty)

def trait_type_constraint_id_of_json(ctx: OfJsonCtx, js: Json) -> TraitTypeConstraintId:
    return TraitTypeConstraintId(int_of_json(ctx, js))

def translated_crate_of_json(ctx: OfJsonCtx, js: Json) -> TranslatedCrate:
    __fields = expect_object(js)
    crate_name = string_of_json(ctx, __fields["crate_name"])
    options = cli_options_of_json(ctx, __fields["options"])
    target_information = list_of_json(key_value_pair_of_json(string_of_json, target_info_of_json))(ctx, __fields["target_information"])
    files = list_of_json(file_of_json)(ctx, __fields["files"])
    item_names = list_of_json(key_value_pair_of_json(item_id_of_json, name_of_json))(ctx, __fields["item_names"])
    assoc_item_names = indexed_map_of_json(trait_decl_id_of_json, assoc_item_names_of_json)(ctx, __fields["assoc_item_names"])
    short_names = list_of_json(key_value_pair_of_json(item_id_of_json, name_of_json))(ctx, __fields["short_names"])
    type_decls = indexed_map_of_json(type_decl_id_of_json, type_decl_of_json)(ctx, __fields["type_decls"])
    fun_decls = indexed_map_of_json(fun_decl_id_of_json, fun_decl_of_json)(ctx, __fields["fun_decls"])
    global_decls = indexed_map_of_json(global_decl_id_of_json, global_decl_of_json)(ctx, __fields["global_decls"])
    trait_decls = indexed_map_of_json(trait_decl_id_of_json, trait_decl_of_json)(ctx, __fields["trait_decls"])
    trait_impls = indexed_map_of_json(trait_impl_id_of_json, trait_impl_of_json)(ctx, __fields["trait_impls"])
    ordered_decls = option_of_json(list_of_json(declaration_group_of_json))(ctx, __fields["ordered_decls"])
    return TranslatedCrate(crate_name, options, target_information, files, item_names, assoc_item_names, short_names, type_decls, fun_decls, global_decls, trait_decls, trait_impls, ordered_decls)

def ty_of_json(ctx: OfJsonCtx, js: Json) -> Ty:
    return dedup_val_of_json(ctx.ty_kind_dedup, ty_kind_of_json)(ctx, js)

def ty_kind_of_json(ctx: OfJsonCtx, js: Json) -> TyKind:
    __tag, __payload = split_variant(js)
    if __tag == "Scalar":
        _0 = scalar_type_of_json(ctx, __payload)
        return TyKindTScalar(_0)
    if __tag == "Array":
        __items = expect_list(__payload, 3)
        _0 = ty_of_json(ctx, __items[0])
        _1 = constant_expr_of_json(ctx, __items[1])
        _2 = option_of_json(trait_ref_of_json)(ctx, __items[2])
        return TyKindTArray(_0, _1, _2)
    if __tag == "Slice":
        __items = expect_list(__payload, 2)
        _0 = ty_of_json(ctx, __items[0])
        _1 = option_of_json(trait_ref_of_json)(ctx, __items[1])
        return TyKindTSlice(_0, _1)
    if __tag == "Adt":
        _0 = type_decl_ref_of_json(ctx, __payload)
        return TyKindTAdt(_0)
    if __tag == "Ref":
        __items = expect_list(__payload, 3)
        _0 = region_of_json(ctx, __items[0])
        _1 = ty_of_json(ctx, __items[1])
        _2 = ref_kind_of_json(ctx, __items[2])
        return TyKindTRef(_0, _1, _2)
    if __tag == "RawPtr":
        __items = expect_list(__payload, 2)
        _0 = ty_of_json(ctx, __items[0])
        _1 = ref_kind_of_json(ctx, __items[1])
        return TyKindTRawPtr(_0, _1)
    if __tag == "FnDef":
        _0 = region_binder_of_json(fn_ptr_of_json)(ctx, __payload)
        return TyKindTFnDef(_0)
    if __tag == "FnPtr":
        _0 = region_binder_of_json(fun_sig_of_json)(ctx, __payload)
        return TyKindTFnPtr(_0)
    if __tag == "DynTrait":
        _0 = dyn_predicate_of_json(ctx, __payload)
        return TyKindTDynTrait(_0)
    if __tag == "Pattern":
        __items = expect_list(__payload, 2)
        _0 = ty_of_json(ctx, __items[0])
        _1 = type_pattern_of_json(ctx, __items[1])
        return TyKindTPattern(_0, _1)
    if __tag == "Never":
        return TyKindTNever()
    if __tag == "TypeVar":
        _0 = de_bruijn_var_of_json(type_var_id_of_json)(ctx, __payload)
        return TyKindTVar(_0)
    if __tag == "TraitType":
        __items = expect_list(__payload, 3)
        _0 = trait_ref_of_json(ctx, __items[0])
        _1 = assoc_type_id_of_json(ctx, __items[1])
        _2 = generic_args_of_json(ctx, __items[2])
        return TyKindTTraitType(_0, _1, _2)
    if __tag == "PtrMetadata":
        _0 = ty_of_json(ctx, __payload)
        return TyKindTPtrMetadata(_0)
    if __tag == "Error":
        _0 = string_of_json(ctx, __payload)
        return TyKindTError(_0)
    raise unknown_variant("TyKind", __tag)

def type_decl_of_json(ctx: OfJsonCtx, js: Json) -> TypeDecl:
    __fields = expect_object(js)
    def_id = type_decl_id_of_json(ctx, __fields["def_id"])
    item_meta = item_meta_of_json(ctx, __fields["item_meta"])
    generics = generic_params_of_json(ctx, __fields["generics"])
    src = type_source_of_json(ctx, __fields["src"])
    kind = type_decl_kind_of_json(ctx, __fields["kind"])
    layout = list_of_json(key_value_pair_of_json(string_of_json, layout_of_json))(ctx, __fields["layout"])
    ptr_metadata = ptr_metadata_of_json(ctx, __fields["ptr_metadata"])
    return TypeDecl(def_id, item_meta, generics, src, kind, layout, ptr_metadata)

def type_decl_id_of_json(ctx: OfJsonCtx, js: Json) -> TypeDeclId:
    return TypeDeclId(int_of_json(ctx, js))

def type_decl_kind_of_json(ctx: OfJsonCtx, js: Json) -> TypeDeclKind:
    __tag, __payload = split_variant(js)
    if __tag == "Struct":
        _0 = list_of_json(field_of_json)(ctx, __payload)
        return TypeDeclKindStruct(_0)
    if __tag == "Enum":
        _0 = list_of_json(variant_of_json)(ctx, __payload)
        return TypeDeclKindEnum(_0)
    if __tag == "Union":
        _0 = list_of_json(field_of_json)(ctx, __payload)
        return TypeDeclKindUnion(_0)
    if __tag == "Opaque":
        return TypeDeclKindOpaque()
    if __tag == "Alias":
        _0 = ty_of_json(ctx, __payload)
        return TypeDeclKindAlias(_0)
    if __tag == "Error":
        _0 = string_of_json(ctx, __payload)
        return TypeDeclKindTDeclError(_0)
    raise unknown_variant("TypeDeclKind", __tag)

def type_decl_ref_of_json(ctx: OfJsonCtx, js: Json) -> TypeDeclRef:
    __fields = expect_object(js)
    id = type_decl_id_of_json(ctx, __fields["id"])
    generics = box_of_json(generic_args_of_json)(ctx, __fields["generics"])
    builtin = option_of_json(builtin_adt_of_json)(ctx, __fields["builtin"])
    return TypeDeclRef(id, generics, builtin)

def type_param_of_json(ctx: OfJsonCtx, js: Json) -> TypeParam:
    __fields = expect_object(js)
    index = type_var_id_of_json(ctx, __fields["index"])
    name = string_of_json(ctx, __fields["name"])
    variance = variance_of_json(ctx, __fields["variance"])
    return TypeParam(index, name, variance)

def type_pattern_of_json(ctx: OfJsonCtx, js: Json) -> TypePattern:
    __tag, __payload = split_variant(js)
    if __tag == "Range":
        __items = expect_list(__payload, 2)
        _0 = constant_expr_of_json(ctx, __items[0])
        _1 = constant_expr_of_json(ctx, __items[1])
        return TypePatternRange(_0, _1)
    if __tag == "OrPattern":
        _0 = list_of_json(type_pattern_of_json)(ctx, __payload)
        return TypePatternOrPattern(_0)
    if __tag == "NotNull":
        return TypePatternNotNull()
    raise unknown_variant("TypePattern", __tag)

def type_source_of_json(ctx: OfJsonCtx, js: Json) -> TypeSource:
    __tag, __payload = split_variant(js)
    if __tag == "Normal":
        return TypeSourceNormalType()
    if __tag == "Closure":
        __fields = expect_object(__payload)
        info = closure_info_of_json(ctx, __fields["info"])
        return TypeSourceClosureType(info)
    if __tag == "VTable":
        __fields = expect_object(__payload)
        dyn_predicate = dyn_predicate_of_json(ctx, __fields["dyn_predicate"])
        field_map = list_of_json(v_table_field_of_json)(ctx, __fields["field_map"])
        supertrait_map = list_of_json(option_of_json(field_id_of_json))(ctx, __fields["supertrait_map"])
        return TypeSourceVTableType(dyn_predicate, field_map, supertrait_map)
    if __tag == "Builtin":
        _0 = builtin_adt_of_json(ctx, __payload)
        return TypeSourceBuiltinType(_0)
    raise unknown_variant("TypeSource", __tag)

def type_var_id_of_json(ctx: OfJsonCtx, js: Json) -> TypeVarId:
    return TypeVarId(int_of_json(ctx, js))

def u_int_ty_of_json(ctx: OfJsonCtx, js: Json) -> UIntTy:
    __tag, __payload = split_variant(js)
    if __tag == "Usize":
        return UIntTyUsize()
    if __tag == "U8":
        return UIntTyU8()
    if __tag == "U16":
        return UIntTyU16()
    if __tag == "U32":
        return UIntTyU32()
    if __tag == "U64":
        return UIntTyU64()
    if __tag == "U128":
        return UIntTyU128()
    raise unknown_variant("UIntTy", __tag)

def unop_of_json(ctx: OfJsonCtx, js: Json) -> Unop:
    __tag, __payload = split_variant(js)
    if __tag == "Not":
        return UnopNot()
    if __tag == "Neg":
        _0 = overflow_mode_of_json(ctx, __payload)
        return UnopNeg(_0)
    if __tag == "Cast":
        _0 = cast_kind_of_json(ctx, __payload)
        return UnopCast(_0)
    raise unknown_variant("Unop", __tag)

def unsizing_metadata_of_json(ctx: OfJsonCtx, js: Json) -> UnsizingMetadata:
    __tag, __payload = split_variant(js)
    if __tag == "Length":
        _0 = constant_expr_of_json(ctx, __payload)
        return UnsizingMetadataMetaLength(_0)
    if __tag == "VTable":
        __items = expect_list(__payload, 2)
        _0 = trait_ref_of_json(ctx, __items[0])
        _1 = constant_expr_of_json(ctx, __items[1])
        return UnsizingMetadataMetaVTable(_0, _1)
    if __tag == "VTableUpcast":
        _0 = list_of_json(field_id_of_json)(ctx, __payload)
        return UnsizingMetadataMetaVTableUpcast(_0)
    if __tag == "Unknown":
        return UnsizingMetadataMetaUnknown()
    raise unknown_variant("UnsizingMetadata", __tag)

def v_table_field_of_json(ctx: OfJsonCtx, js: Json) -> VTableField:
    __tag, __payload = split_variant(js)
    if __tag == "Size":
        return VTableFieldVTableSize()
    if __tag == "Align":
        return VTableFieldVTableAlign()
    if __tag == "Drop":
        return VTableFieldVTableDrop()
    if __tag == "Method":
        _0 = trait_method_id_of_json(ctx, __payload)
        return VTableFieldVTableMethod(_0)
    if __tag == "SuperTrait":
        _0 = trait_clause_id_of_json(ctx, __payload)
        return VTableFieldVTableSuperTrait(_0)
    raise unknown_variant("VTableField", __tag)

def variance_of_json(ctx: OfJsonCtx, js: Json) -> Variance:
    __tag, __payload = split_variant(js)
    if __tag == "Covariant":
        return VarianceCovariant()
    if __tag == "Invariant":
        return VarianceInvariant()
    if __tag == "Contravariant":
        return VarianceContravariant()
    if __tag == "Bivariant":
        return VarianceBivariant()
    if __tag == "Unknown":
        return VarianceVaUnknown()
    raise unknown_variant("Variance", __tag)

def variant_of_json(ctx: OfJsonCtx, js: Json) -> Variant:
    __fields = expect_object(js)
    id = variant_id_of_json(ctx, __fields["id"])
    span = span_of_json(ctx, __fields["span"])
    attr_info = attr_info_of_json(ctx, __fields["attr_info"])
    variant_name = string_of_json(ctx, __fields["name"])
    fields = list_of_json(field_of_json)(ctx, __fields["fields"])
    discriminant = integer_value_of_json(ctx, __fields["discriminant"])
    return Variant(id, span, attr_info, variant_name, fields, discriminant)

def variant_id_of_json(ctx: OfJsonCtx, js: Json) -> VariantId:
    return VariantId(int_of_json(ctx, js))

def variant_layout_of_json(ctx: OfJsonCtx, js: Json) -> VariantLayout:
    __fields = expect_object(js)
    field_offsets = list_of_json(offset_expr_of_json)(ctx, __fields["field_offsets"])
    uninhabited = bool_of_json(ctx, __fields["uninhabited"])
    tagger = list_of_json(pair_of_json(int_of_json, integer_value_of_json))(ctx, __fields["tagger"])
    return VariantLayout(field_offsets, uninhabited, tagger)

def with_retag_of_json(ctx: OfJsonCtx, js: Json) -> WithRetag:
    __tag, __payload = split_variant(js)
    if __tag == "No":
        return WithRetagNoRetag()
    if __tag == "Yes":
        return WithRetagYesRetag()
    raise unknown_variant("WithRetag", __tag)



def crate_of_json(js: Json) -> TranslatedCrate:
    """Read a crate from an already-parsed json value."""
    fields = expect_object(js)
    version = string_of_json(None, fields["charon_version"])
    if version != SUPPORTED_CHARON_VERSION:
        raise DeserializeError(
            "Incompatible version of charon: this program supports llbc emitted by charon "
            f"v{SUPPORTED_CHARON_VERSION} but attempted to read a file emitted by charon "
            f"v{version}."
        )
    return translated_crate_of_json(OfJsonCtx(), fields["translated"])


def crate_of_json_file(path: str | os.PathLike[str]) -> TranslatedCrate:
    """Read a crate from a json-serialized `.llbc`/`.ullbc` file."""
    with open(path, "rb") as file:
        contents = file.read()
    hint = format_hint(contents)
    if hint is InputFormat.POSTCARD:
        raise DeserializeError(
            f"This file looks like Postcard, but JSON deserialization was requested: {path}. "
            "Please use Postcard deserialization or regenerate as JSON."
        )
    if hint is InputFormat.EMPTY:
        raise DeserializeError(f"Input file is empty: {path}")
    return crate_of_json(_json.loads(contents))
