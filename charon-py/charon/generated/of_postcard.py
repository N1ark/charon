"""WARNING: this file is partially auto-generated. Do not edit `of_postcard.py` by hand. Edit
`generate_py/templates/of_postcard.py` instead, or improve the code generation tool so as to avoid
the need for hand-writing things.

`generate_py/templates/of_postcard.py` contains the manual definitions and some `# __REPLACEn__`
comments. These comments are replaced by auto-generated definitions by running `make
generate-asts` in the crate root. The code-generation code is in `charon/src/bin/generate-asts`.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field

from ..errors import DeserializeError, unknown_variant
from ..postcard_basic import *
from ..version import SUPPORTED_CHARON_VERSION
from .types import *


@dataclass
class OfPostcardCtx:
    """See `charon.generated.of_json.OfJsonCtx`."""

    files: dict[int, File] = field(default_factory=dict)
    ty_dedup: dict[int, Ty] = field(default_factory=dict)
    trait_ref_dedup: dict[int, TraitRef] = field(default_factory=dict)
    constant_expr_dedup: dict[int, ConstantExpr] = field(default_factory=dict)
    exact_size_expr_dedup: dict[int, ExactSizeExpr] = field(default_factory=dict)
    span_dedup: dict[int, Span] = field(default_factory=dict)


def abi_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Abi:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return AbiRust()
    if __tag == 1:
        return AbiC()
    if __tag == 2:
        _0 = string_of_postcard(ctx, st)
        return AbiOther(_0)
    raise unknown_variant("Abi", __tag)

def abort_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> AbortKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = option_of_postcard(name_of_postcard)(ctx, st)
        return AbortKindPanic(_0)
    if __tag == 1:
        return AbortKindUndefinedBehavior()
    if __tag == 2:
        return AbortKindUnwindTerminate()
    raise unknown_variant("AbortKind", __tag)

def aggregate_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> AggregateKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = type_decl_ref_of_postcard(ctx, st)
        _1 = option_of_postcard(variant_id_of_postcard)(ctx, st)
        _2 = option_of_postcard(field_id_of_postcard)(ctx, st)
        return AggregateKindAggregatedAdt(_0, _1, _2)
    if __tag == 1:
        _0 = ty_of_postcard(ctx, st)
        _1 = constant_expr_of_postcard(ctx, st)
        _2 = option_of_postcard(trait_ref_of_postcard)(ctx, st)
        return AggregateKindAggregatedArray(_0, _1, _2)
    if __tag == 2:
        _0 = ty_of_postcard(ctx, st)
        _1 = ref_kind_of_postcard(ctx, st)
        return AggregateKindAggregatedRawPtr(_0, _1)
    raise unknown_variant("AggregateKind", __tag)

def alignment_modifier_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> AlignmentModifier:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = u64_of_postcard(ctx, st)
        return AlignmentModifierAlign(_0)
    if __tag == 1:
        _0 = u64_of_postcard(ctx, st)
        return AlignmentModifierPack(_0)
    raise unknown_variant("AlignmentModifier", __tag)

def assertion_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Assertion:
    cond = operand_of_postcard(ctx, st)
    expected = bool_of_postcard(ctx, st)
    check_kind = option_of_postcard(builtin_assert_kind_of_postcard)(ctx, st)
    return Assertion(cond, expected, check_kind)

def assoc_const_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> AssocConstId:
    return AssocConstId(int_of_postcard(ctx, st))

def assoc_item_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> AssocItemId:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = assoc_type_id_of_postcard(ctx, st)
        return AssocItemIdAssocIdType(_0)
    if __tag == 1:
        _0 = trait_method_id_of_postcard(ctx, st)
        return AssocItemIdAssocIdMethod(_0)
    if __tag == 2:
        _0 = assoc_const_id_of_postcard(ctx, st)
        return AssocItemIdAssocIdConst(_0)
    raise unknown_variant("AssocItemId", __tag)

def assoc_item_names_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> AssocItemNames:
    types = index_vec_of_postcard(assoc_type_id_of_postcard, trait_item_name_of_postcard)(ctx, st)
    methods = index_vec_of_postcard(trait_method_id_of_postcard, trait_item_name_of_postcard)(ctx, st)
    consts = index_vec_of_postcard(assoc_const_id_of_postcard, trait_item_name_of_postcard)(ctx, st)
    return AssocItemNames(types, methods, consts)

def assoc_type_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> AssocTypeId:
    return AssocTypeId(int_of_postcard(ctx, st))

def attr_info_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> AttrInfo:
    attributes = list_of_postcard(attribute_of_postcard)(ctx, st)
    inline = option_of_postcard(inline_attr_of_postcard)(ctx, st)
    rename = option_of_postcard(string_of_postcard)(ctx, st)
    public = bool_of_postcard(ctx, st)
    return AttrInfo(attributes, inline, rename, public)

def attribute_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Attribute:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return AttributeAttrOpaque()
    if __tag == 1:
        return AttributeAttrExclude()
    if __tag == 2:
        _0 = string_of_postcard(ctx, st)
        return AttributeAttrRename(_0)
    if __tag == 3:
        _0 = string_of_postcard(ctx, st)
        return AttributeAttrVariantsPrefix(_0)
    if __tag == 4:
        _0 = string_of_postcard(ctx, st)
        return AttributeAttrVariantsSuffix(_0)
    if __tag == 5:
        return AttributeAttrTransparent()
    if __tag == 6:
        kind = string_of_postcard(ctx, st)
        target = maybe_assoc_item_id_of_postcard(ctx, st)
        return AttributeAttrIsContract(kind, target)
    if __tag == 7:
        kind = string_of_postcard(ctx, st)
        contract = fun_decl_id_of_postcard(ctx, st)
        return AttributeAttrHasContract(kind, contract)
    if __tag == 8:
        _0 = string_of_postcard(ctx, st)
        return AttributeAttrDocComment(_0)
    if __tag == 9:
        _0 = rustc_attribute_kind_of_postcard(ctx, st)
        return AttributeAttrBuiltin(_0)
    if __tag == 10:
        _0 = raw_attribute_of_postcard(ctx, st)
        return AttributeAttrUnknown(_0)
    raise unknown_variant("Attribute", __tag)

def rustc_attribute_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RustcAttributeKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return RustcAttributeKindAutomaticallyDerived()
    if __tag == 1:
        return RustcAttributeKindCold()
    if __tag == 2:
        deprecation = rustc_deprecation_of_postcard(ctx, st)
        span = span_of_postcard(ctx, st)
        return RustcAttributeKindDeprecated(deprecation, span)
    if __tag == 3:
        return RustcAttributeKindFundamental()
    if __tag == 4:
        span = span_of_postcard(ctx, st)
        reason = option_of_postcard(string_of_postcard)(ctx, st)
        return RustcAttributeKindIgnore(span, reason)
    if __tag == 5:
        _0 = rustc_inline_attr_of_postcard(ctx, st)
        _1 = span_of_postcard(ctx, st)
        return RustcAttributeKindInline(_0, _1)
    if __tag == 6:
        _0 = span_of_postcard(ctx, st)
        return RustcAttributeKindMayDangle(_0)
    if __tag == 7:
        _0 = span_of_postcard(ctx, st)
        return RustcAttributeKindNaked(_0)
    if __tag == 8:
        return RustcAttributeKindNoLink()
    if __tag == 9:
        _0 = span_of_postcard(ctx, st)
        return RustcAttributeKindNoMangle(_0)
    if __tag == 10:
        _0 = span_of_postcard(ctx, st)
        return RustcAttributeKindNonExhaustive(_0)
    if __tag == 11:
        _0 = rustc_optimize_attr_of_postcard(ctx, st)
        _1 = span_of_postcard(ctx, st)
        return RustcAttributeKindOptimize(_0, _1)
    if __tag == 12:
        align = u64_of_postcard(ctx, st)
        span = span_of_postcard(ctx, st)
        return RustcAttributeKindRustcAlign(align, span)
    if __tag == 13:
        return RustcAttributeKindRustcIntrinsic()
    if __tag == 14:
        return RustcAttributeKindRustcTestEntrypointMarker()
    if __tag == 15:
        reason = option_of_postcard(string_of_postcard)(ctx, st)
        return RustcAttributeKindShouldPanic(reason)
    if __tag == 16:
        features = list_of_postcard(pair_of_postcard(string_of_postcard, span_of_postcard))(ctx, st)
        attr_span = span_of_postcard(ctx, st)
        was_forced = bool_of_postcard(ctx, st)
        return RustcAttributeKindTargetFeature(features, attr_span, was_forced)
    if __tag == 17:
        _0 = span_of_postcard(ctx, st)
        return RustcAttributeKindTrackCaller(_0)
    raise unknown_variant("RustcAttributeKind", __tag)

def binop_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Binop:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return BinopBitXor()
    if __tag == 1:
        return BinopBitAnd()
    if __tag == 2:
        return BinopBitOr()
    if __tag == 3:
        return BinopEq()
    if __tag == 4:
        return BinopLt()
    if __tag == 5:
        return BinopLe()
    if __tag == 6:
        return BinopNe()
    if __tag == 7:
        return BinopGe()
    if __tag == 8:
        return BinopGt()
    if __tag == 9:
        _0 = overflow_mode_of_postcard(ctx, st)
        return BinopAdd(_0)
    if __tag == 10:
        _0 = overflow_mode_of_postcard(ctx, st)
        return BinopSub(_0)
    if __tag == 11:
        _0 = overflow_mode_of_postcard(ctx, st)
        return BinopMul(_0)
    if __tag == 12:
        _0 = overflow_mode_of_postcard(ctx, st)
        return BinopDiv(_0)
    if __tag == 13:
        _0 = overflow_mode_of_postcard(ctx, st)
        return BinopRem(_0)
    if __tag == 14:
        return BinopAddChecked()
    if __tag == 15:
        return BinopSubChecked()
    if __tag == 16:
        return BinopMulChecked()
    if __tag == 17:
        _0 = overflow_mode_of_postcard(ctx, st)
        return BinopShl(_0)
    if __tag == 18:
        _0 = overflow_mode_of_postcard(ctx, st)
        return BinopShr(_0)
    if __tag == 19:
        return BinopOffset()
    if __tag == 20:
        return BinopCmp()
    raise unknown_variant("Binop", __tag)

def binder_of_postcard(arg0_of_postcard: PostcardDecoder[T0]) -> PostcardDecoder[Binder[T0]]:
    def read(ctx: OfPostcardCtx, st: PostcardReader) -> Binder[T0]:
        binder_params = generic_params_of_postcard(ctx, st)
        binder_value = arg0_of_postcard(ctx, st)
        _ = binder_kind_of_postcard(ctx, st)
        return Binder(binder_params, binder_value)
    return read

def binder_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> BinderKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = trait_decl_id_of_postcard(ctx, st)
        _1 = assoc_type_id_of_postcard(ctx, st)
        return BinderKindBKTraitType(_0, _1)
    if __tag == 1:
        _0 = trait_decl_id_of_postcard(ctx, st)
        _1 = trait_method_id_of_postcard(ctx, st)
        return BinderKindBKTraitMethod(_0, _1)
    if __tag == 2:
        return BinderKindBKInherentImplBlock()
    if __tag == 3:
        return BinderKindBKDyn()
    if __tag == 4:
        return BinderKindBKOther()
    raise unknown_variant("BinderKind", __tag)

def llbc_block_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> LlbcBlock:
    span = span_of_postcard(ctx, st)
    block_id = llbc_block_id_of_postcard(ctx, st)
    statements = list_of_postcard(llbc_statement_of_postcard)(ctx, st)
    return LlbcBlock(span, block_id, statements)

def ullbc_block_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> UllbcBlock:
    statements = list_of_postcard(ullbc_statement_of_postcard)(ctx, st)
    terminator = terminator_of_postcard(ctx, st)
    return UllbcBlock(statements, terminator)

def ullbc_block_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> UllbcBlockId:
    return UllbcBlockId(int_of_postcard(ctx, st))

def llbc_block_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> LlbcBlockId:
    return LlbcBlockId(int_of_postcard(ctx, st))

def body_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Body:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = gexpr_body_of_postcard(index_vec_of_postcard(ullbc_block_id_of_postcard, ullbc_block_of_postcard))(ctx, st)
        return BodyUnstructuredBody(_0)
    if __tag == 1:
        _0 = gexpr_body_of_postcard(llbc_block_of_postcard)(ctx, st)
        return BodyStructuredBody(_0)
    if __tag == 2:
        _0 = index_map_of_postcard(string_of_postcard, fun_decl_ref_of_postcard, int_of_postcard)(ctx, st)
        return BodyTargetDispatchBody(_0)
    if __tag == 3:
        _0 = string_of_postcard(ctx, st)
        return BodyExternBody(_0)
    if __tag == 4:
        name = string_of_postcard(ctx, st)
        arg_names = list_of_postcard(option_of_postcard(string_of_postcard))(ctx, st)
        return BodyIntrinsicBody(name, arg_names)
    if __tag == 5:
        return BodyOpaqueBody()
    if __tag == 6:
        return BodyMissingBody()
    if __tag == 7:
        _0 = error_of_postcard(ctx, st)
        return BodyErrorBody(_0)
    raise unknown_variant("Body", __tag)

def borrow_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> BorrowKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return BorrowKindBShared()
    if __tag == 1:
        return BorrowKindBMut()
    if __tag == 2:
        return BorrowKindBTwoPhaseMut()
    if __tag == 3:
        return BorrowKindBShallow()
    if __tag == 4:
        return BorrowKindBUniqueImmutable()
    raise unknown_variant("BorrowKind", __tag)

def borrowck_statement_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> BorrowckStatement:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = place_of_postcard(ctx, st)
        return BorrowckStatementFakeRead(_0)
    if __tag == 1:
        place = place_of_postcard(ctx, st)
        ty = ty_of_postcard(ctx, st)
        variance = variance_of_postcard(ctx, st)
        return BorrowckStatementSetType(place, ty, variance)
    if __tag == 2:
        _0 = ty_of_postcard(ctx, st)
        _1 = region_of_postcard(ctx, st)
        return BorrowckStatementSetOutlives(_0, _1)
    if __tag == 3:
        _0 = trait_ref_of_postcard(ctx, st)
        return BorrowckStatementPredicateHolds(_0)
    raise unknown_variant("BorrowckStatement", __tag)

def branch_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> BranchId:
    return BranchId(int_of_postcard(ctx, st))

def builtin_adt_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> BuiltinAdt:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return BuiltinAdtTTuple()
    if __tag == 1:
        return BuiltinAdtTBox()
    if __tag == 2:
        return BuiltinAdtTStr()
    raise unknown_variant("BuiltinAdt", __tag)

def builtin_assert_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> BuiltinAssertKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        len = operand_of_postcard(ctx, st)
        index = operand_of_postcard(ctx, st)
        return BuiltinAssertKindBoundsCheck(len, index)
    if __tag == 1:
        _0 = binop_of_postcard(ctx, st)
        _1 = operand_of_postcard(ctx, st)
        _2 = operand_of_postcard(ctx, st)
        return BuiltinAssertKindOverflow(_0, _1, _2)
    if __tag == 2:
        _0 = operand_of_postcard(ctx, st)
        return BuiltinAssertKindOverflowNeg(_0)
    if __tag == 3:
        _0 = operand_of_postcard(ctx, st)
        return BuiltinAssertKindDivisionByZero(_0)
    if __tag == 4:
        _0 = operand_of_postcard(ctx, st)
        return BuiltinAssertKindRemainderByZero(_0)
    if __tag == 5:
        required = operand_of_postcard(ctx, st)
        found = operand_of_postcard(ctx, st)
        return BuiltinAssertKindMisalignedPointerDereference(required, found)
    if __tag == 6:
        return BuiltinAssertKindNullPointerDereference()
    if __tag == 7:
        return BuiltinAssertKindNullReferenceCreated()
    if __tag == 8:
        _0 = operand_of_postcard(ctx, st)
        return BuiltinAssertKindInvalidEnumConstruction(_0)
    if __tag == 9:
        return BuiltinAssertKindResumedAfterReturn()
    if __tag == 10:
        return BuiltinAssertKindResumedAfterPanic()
    if __tag == 11:
        return BuiltinAssertKindResumedAfterDrop()
    raise unknown_variant("BuiltinAssertKind", __tag)

def builtin_impl_data_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> BuiltinImplData:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return BuiltinImplDataBuiltinAuto()
    if __tag == 1:
        return BuiltinImplDataBuiltinSized()
    if __tag == 2:
        return BuiltinImplDataBuiltinMetaSized()
    if __tag == 3:
        return BuiltinImplDataBuiltinPointeeSized()
    if __tag == 4:
        return BuiltinImplDataBuiltinCopy()
    if __tag == 5:
        return BuiltinImplDataBuiltinClone()
    if __tag == 6:
        return BuiltinImplDataBuiltinTuple()
    if __tag == 7:
        return BuiltinImplDataBuiltinTransmute()
    if __tag == 8:
        return BuiltinImplDataBuiltinUnsize()
    if __tag == 9:
        return BuiltinImplDataBuiltinPointee()
    if __tag == 10:
        return BuiltinImplDataBuiltinDiscriminantKind()
    if __tag == 11:
        return BuiltinImplDataBuiltinFn()
    if __tag == 12:
        return BuiltinImplDataBuiltinFnMut()
    if __tag == 13:
        return BuiltinImplDataBuiltinFnOnce()
    if __tag == 14:
        return BuiltinImplDataBuiltinFnPtr()
    if __tag == 15:
        return BuiltinImplDataBuiltinAsyncFn()
    if __tag == 16:
        return BuiltinImplDataBuiltinAsyncFnMut()
    if __tag == 17:
        return BuiltinImplDataBuiltinAsyncFnOnce()
    if __tag == 18:
        return BuiltinImplDataBuiltinCoroutine()
    if __tag == 19:
        return BuiltinImplDataBuiltinFuture()
    if __tag == 20:
        return BuiltinImplDataBuiltinTryAsDynCompatible()
    if __tag == 21:
        return BuiltinImplDataBuiltinNoopDestruct()
    if __tag == 22:
        return BuiltinImplDataBuiltinUntrackedDestruct()
    if __tag == 23:
        return BuiltinImplDataBuiltinRemovedAdtClause()
    raise unknown_variant("BuiltinImplData", __tag)

def builtin_path_elem_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> BuiltinPathElem:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = usize_of_postcard(ctx, st)
        return BuiltinPathElemPeTuple(_0)
    if __tag == 1:
        return BuiltinPathElemPeStr()
    if __tag == 2:
        return BuiltinPathElemPeClosure()
    if __tag == 3:
        return BuiltinPathElemPeUse()
    if __tag == 4:
        return BuiltinPathElemPeAnonConst()
    if __tag == 5:
        return BuiltinPathElemPePromotedConst()
    if __tag == 6:
        return BuiltinPathElemPeClosureAsFn()
    if __tag == 7:
        return BuiltinPathElemPeDropGlue()
    if __tag == 8:
        return BuiltinPathElemPeVTable()
    if __tag == 9:
        return BuiltinPathElemPeVTableMethod()
    if __tag == 10:
        return BuiltinPathElemPeVTableDropShim()
    raise unknown_variant("BuiltinPathElem", __tag)

def byte_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Byte:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return ByteUninit()
    if __tag == 1:
        _0 = u8_of_postcard(ctx, st)
        return ByteValue(_0)
    if __tag == 2:
        _0 = provenance_of_postcard(ctx, st)
        _1 = u8_of_postcard(ctx, st)
        return ByteProvenance(_0, _1)
    raise unknown_variant("Byte", __tag)

def call_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Call:
    func = fn_operand_of_postcard(ctx, st)
    args = list_of_postcard(operand_of_postcard)(ctx, st)
    dest = place_of_postcard(ctx, st)
    return Call(func, args, dest)

def cast_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> CastKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = scalar_type_of_postcard(ctx, st)
        _1 = scalar_type_of_postcard(ctx, st)
        return CastKindCastScalar(_0, _1)
    if __tag == 1:
        _0 = ty_of_postcard(ctx, st)
        _1 = ty_of_postcard(ctx, st)
        return CastKindCastRawPtr(_0, _1)
    if __tag == 2:
        _0 = ty_of_postcard(ctx, st)
        _1 = ty_of_postcard(ctx, st)
        return CastKindCastFnPtr(_0, _1)
    if __tag == 3:
        _0 = ty_of_postcard(ctx, st)
        _1 = ty_of_postcard(ctx, st)
        _2 = unsizing_metadata_of_postcard(ctx, st)
        return CastKindCastUnsize(_0, _1, _2)
    if __tag == 4:
        _0 = ty_of_postcard(ctx, st)
        _1 = ty_of_postcard(ctx, st)
        return CastKindCastTransmute(_0, _1)
    if __tag == 5:
        _0 = ty_of_postcard(ctx, st)
        _1 = ty_of_postcard(ctx, st)
        return CastKindCastConcretize(_0, _1)
    raise unknown_variant("CastKind", __tag)

def cli_options_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> CliOptions:
    ullbc = bool_of_postcard(ctx, st)
    precise_drops = bool_of_postcard(ctx, st)
    mir = option_of_postcard(mir_level_of_postcard)(ctx, st)
    rustc_args = list_of_postcard(string_of_postcard)(ctx, st)
    targets = list_of_postcard(string_of_postcard)(ctx, st)
    sysroot = option_of_postcard(string_of_postcard)(ctx, st)
    monomorphize = bool_of_postcard(ctx, st)
    monomorphize_mut = option_of_postcard(monomorphize_mut_of_postcard)(ctx, st)
    start_from = list_of_postcard(string_of_postcard)(ctx, st)
    start_from_if_exists = list_of_postcard(string_of_postcard)(ctx, st)
    start_from_attribute = list_of_postcard(string_of_postcard)(ctx, st)
    start_from_pub = bool_of_postcard(ctx, st)
    included = list_of_postcard(string_of_postcard)(ctx, st)
    opaque = list_of_postcard(string_of_postcard)(ctx, st)
    exclude = list_of_postcard(string_of_postcard)(ctx, st)
    extract_opaque_bodies = bool_of_postcard(ctx, st)
    translate_all_methods = bool_of_postcard(ctx, st)
    duplicate_defaulted_methods = bool_of_postcard(ctx, st)
    lift_associated_types = list_of_postcard(string_of_postcard)(ctx, st)
    hide_marker_traits = bool_of_postcard(ctx, st)
    hide_allocator = bool_of_postcard(ctx, st)
    remove_unused_clauses = bool_of_postcard(ctx, st)
    remove_unused_self_clauses = bool_of_postcard(ctx, st)
    remove_adt_clauses = bool_of_postcard(ctx, st)
    desugar_drops = bool_of_postcard(ctx, st)
    ops_to_function_calls = bool_of_postcard(ctx, st)
    index_to_function_calls = bool_of_postcard(ctx, st)
    treat_box_as_builtin = bool_of_postcard(ctx, st)
    no_gen_tuple_structs = bool_of_postcard(ctx, st)
    raw_consts = bool_of_postcard(ctx, st)
    consts = option_of_postcard(const_handling_of_postcard)(ctx, st)
    unsized_strings = bool_of_postcard(ctx, st)
    reconstruct_fallible_operations = bool_of_postcard(ctx, st)
    reconstruct_asserts = bool_of_postcard(ctx, st)
    reconstruct_matches = bool_of_postcard(ctx, st)
    deallocate_all_locals = bool_of_postcard(ctx, st)
    unbind_item_vars = bool_of_postcard(ctx, st)
    print_original_ullbc = bool_of_postcard(ctx, st)
    print_ullbc = bool_of_postcard(ctx, st)
    print_built_llbc = bool_of_postcard(ctx, st)
    print_llbc = bool_of_postcard(ctx, st)
    dest_dir = option_of_postcard(string_of_postcard)(ctx, st)
    dest_file = option_of_postcard(string_of_postcard)(ctx, st)
    no_dedup_serialized_ast = bool_of_postcard(ctx, st)
    format = option_of_postcard(serialization_format_arg_of_postcard)(ctx, st)
    no_serialize = bool_of_postcard(ctx, st)
    skip_borrowck = bool_of_postcard(ctx, st)
    no_typecheck = bool_of_postcard(ctx, st)
    no_normalize = bool_of_postcard(ctx, st)
    no_reorder_decls = bool_of_postcard(ctx, st)
    abort_on_error = bool_of_postcard(ctx, st)
    error_on_warnings = bool_of_postcard(ctx, st)
    preset = option_of_postcard(preset_of_postcard)(ctx, st)
    return CliOptions(ullbc, precise_drops, mir, rustc_args, targets, sysroot, monomorphize, monomorphize_mut, start_from, start_from_if_exists, start_from_attribute, start_from_pub, included, opaque, exclude, extract_opaque_bodies, translate_all_methods, duplicate_defaulted_methods, lift_associated_types, hide_marker_traits, hide_allocator, remove_unused_clauses, remove_unused_self_clauses, remove_adt_clauses, desugar_drops, ops_to_function_calls, index_to_function_calls, treat_box_as_builtin, no_gen_tuple_structs, raw_consts, consts, unsized_strings, reconstruct_fallible_operations, reconstruct_asserts, reconstruct_matches, deallocate_all_locals, unbind_item_vars, print_original_ullbc, print_ullbc, print_built_llbc, print_llbc, dest_dir, dest_file, no_dedup_serialized_ast, format, no_serialize, skip_borrowck, no_typecheck, no_normalize, no_reorder_decls, abort_on_error, error_on_warnings, preset)

def closure_info_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ClosureInfo:
    kind = closure_kind_of_postcard(ctx, st)
    fn_once_impl = region_binder_of_postcard(trait_impl_ref_of_postcard)(ctx, st)
    fn_mut_impl = option_of_postcard(region_binder_of_postcard(trait_impl_ref_of_postcard))(ctx, st)
    fn_impl = option_of_postcard(region_binder_of_postcard(trait_impl_ref_of_postcard))(ctx, st)
    signature = region_binder_of_postcard(fun_sig_of_postcard)(ctx, st)
    return ClosureInfo(kind, fn_once_impl, fn_mut_impl, fn_impl, signature)

def closure_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ClosureKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return ClosureKindFn()
    if __tag == 1:
        return ClosureKindFnMut()
    if __tag == 2:
        return ClosureKindFnOnce()
    raise unknown_variant("ClosureKind", __tag)

def const_generic_param_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ConstGenericParam:
    index = const_generic_var_id_of_postcard(ctx, st)
    name = string_of_postcard(ctx, st)
    ty = ty_of_postcard(ctx, st)
    return ConstGenericParam(index, name, ty)

def const_generic_var_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ConstGenericVarId:
    return ConstGenericVarId(int_of_postcard(ctx, st))

def const_handling_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ConstHandling:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return ConstHandlingInitializers()
    if __tag == 1:
        return ConstHandlingValues()
    raise unknown_variant("ConstHandling", __tag)

def constant_expr_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ConstantExpr:
    def read_contents(ctx: OfPostcardCtx, st: PostcardReader) -> ConstantExpr:
        kind, ty = pair_of_postcard(constant_expr_kind_of_postcard, ty_of_postcard)(ctx, st)
        return ConstantExpr(kind=kind, ty=ty)

    return dedup_val_of_postcard(ctx.constant_expr_dedup, read_contents, ctx, st)

def constant_expr_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ConstantExprKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = bool_of_postcard(ctx, st)
        return ConstantExprKindCBool(_0)
    if __tag == 1:
        _0 = integer_value_of_postcard(ctx, st)
        return ConstantExprKindCInteger(_0)
    if __tag == 2:
        _0 = char_of_postcard(ctx, st)
        return ConstantExprKindCChar(_0)
    if __tag == 3:
        _0 = float_value_of_postcard(ctx, st)
        return ConstantExprKindCFloat(_0)
    if __tag == 4:
        _0 = option_of_postcard(variant_id_of_postcard)(ctx, st)
        _1 = list_of_postcard(constant_expr_of_postcard)(ctx, st)
        return ConstantExprKindCAdt(_0, _1)
    if __tag == 5:
        _0 = list_of_postcard(constant_expr_of_postcard)(ctx, st)
        return ConstantExprKindCArray(_0)
    if __tag == 6:
        _0 = constant_expr_of_postcard(ctx, st)
        _1 = option_of_postcard(unsizing_metadata_of_postcard)(ctx, st)
        return ConstantExprKindCRef(_0, _1)
    if __tag == 7:
        _0 = ref_kind_of_postcard(ctx, st)
        _1 = constant_expr_of_postcard(ctx, st)
        _2 = option_of_postcard(unsizing_metadata_of_postcard)(ctx, st)
        return ConstantExprKindCPtr(_0, _1, _2)
    if __tag == 8:
        _0 = string_of_postcard(ctx, st)
        return ConstantExprKindCStr(_0)
    if __tag == 9:
        _0 = list_of_postcard(u8_of_postcard)(ctx, st)
        return ConstantExprKindCByteStr(_0)
    if __tag == 10:
        _0 = fn_ptr_of_postcard(ctx, st)
        return ConstantExprKindCFnDef(_0)
    if __tag == 11:
        _0 = fn_ptr_of_postcard(ctx, st)
        return ConstantExprKindCFnPtr(_0)
    if __tag == 12:
        _0 = big_uint_of_postcard(ctx, st)
        return ConstantExprKindCPtrNoProvenance(_0)
    if __tag == 13:
        _0 = ty_of_postcard(ctx, st)
        return ConstantExprKindCTypeId(_0)
    if __tag == 14:
        _0 = list_of_postcard(byte_of_postcard)(ctx, st)
        return ConstantExprKindCRawMemory(_0)
    if __tag == 15:
        _0 = de_bruijn_var_of_postcard(const_generic_var_id_of_postcard)(ctx, st)
        return ConstantExprKindCVar(_0)
    if __tag == 16:
        _0 = global_decl_ref_of_postcard(ctx, st)
        return ConstantExprKindCGlobal(_0)
    if __tag == 17:
        _0 = fn_ptr_of_postcard(ctx, st)
        _1 = list_of_postcard(constant_expr_of_postcard)(ctx, st)
        return ConstantExprKindCCall(_0, _1)
    if __tag == 18:
        _0 = trait_ref_of_postcard(ctx, st)
        _1 = assoc_const_id_of_postcard(ctx, st)
        return ConstantExprKindCTraitConst(_0, _1)
    if __tag == 19:
        _0 = trait_ref_of_postcard(ctx, st)
        return ConstantExprKindCVTableRef(_0)
    if __tag == 20:
        _0 = type_decl_ref_of_postcard(ctx, st)
        _1 = variant_id_of_postcard(ctx, st)
        return ConstantExprKindCDiscriminant(_0, _1)
    if __tag == 21:
        _0 = ty_of_postcard(ctx, st)
        return ConstantExprKindCSizeOf(_0)
    if __tag == 22:
        _0 = ty_of_postcard(ctx, st)
        return ConstantExprKindCAlignOf(_0)
    if __tag == 23:
        _0 = string_of_postcard(ctx, st)
        return ConstantExprKindCOpaque(_0)
    raise unknown_variant("ConstantExprKind", __tag)

def de_bruijn_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> DeBruijnId:
    return usize_of_postcard(ctx, st)

def de_bruijn_var_of_postcard(arg0_of_postcard: PostcardDecoder[T0]) -> PostcardDecoder[DeBruijnVar[T0]]:
    def read(ctx: OfPostcardCtx, st: PostcardReader) -> DeBruijnVar[T0]:
        __tag = int_of_postcard(ctx, st)
        if __tag == 0:
            _0 = de_bruijn_id_of_postcard(ctx, st)
            _1 = arg0_of_postcard(ctx, st)
            return DeBruijnVarBound(_0, _1)
        if __tag == 1:
            _0 = arg0_of_postcard(ctx, st)
            return DeBruijnVarFree(_0)
        raise unknown_variant("DeBruijnVar", __tag)
    return read

def declaration_group_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> DeclarationGroup:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = g_declaration_group_of_postcard(type_decl_id_of_postcard)(ctx, st)
        return DeclarationGroupTypeGroup(_0)
    if __tag == 1:
        _0 = g_declaration_group_of_postcard(fun_decl_id_of_postcard)(ctx, st)
        return DeclarationGroupFunGroup(_0)
    if __tag == 2:
        _0 = g_declaration_group_of_postcard(global_decl_id_of_postcard)(ctx, st)
        return DeclarationGroupGlobalGroup(_0)
    if __tag == 3:
        _0 = g_declaration_group_of_postcard(trait_decl_id_of_postcard)(ctx, st)
        return DeclarationGroupTraitDeclGroup(_0)
    if __tag == 4:
        _0 = g_declaration_group_of_postcard(trait_impl_id_of_postcard)(ctx, st)
        return DeclarationGroupTraitImplGroup(_0)
    if __tag == 5:
        _0 = g_declaration_group_of_postcard(item_id_of_postcard)(ctx, st)
        return DeclarationGroupMixedGroup(_0)
    raise unknown_variant("DeclarationGroup", __tag)

def rustc_deprecated_since_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RustcDeprecatedSince:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = rustc_rustc_version_of_postcard(ctx, st)
        return RustcDeprecatedSinceRustcVersion(_0)
    if __tag == 1:
        return RustcDeprecatedSinceFuture()
    if __tag == 2:
        _0 = string_of_postcard(ctx, st)
        return RustcDeprecatedSinceNonStandard(_0)
    if __tag == 3:
        return RustcDeprecatedSinceUnspecified()
    if __tag == 4:
        return RustcDeprecatedSinceErr()
    raise unknown_variant("RustcDeprecatedSince", __tag)

def rustc_deprecation_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RustcDeprecation:
    since = rustc_deprecated_since_of_postcard(ctx, st)
    note = option_of_postcard(rustc_ident_of_postcard)(ctx, st)
    suggestion = option_of_postcard(string_of_postcard)(ctx, st)
    return RustcDeprecation(since, note, suggestion)

def disambiguator_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Disambiguator:
    return Disambiguator(int_of_postcard(ctx, st))

def discriminator_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Discriminator:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = variant_id_of_postcard(ctx, st)
        return DiscriminatorKnown(_0)
    if __tag == 1:
        return DiscriminatorInvalid()
    if __tag == 2:
        offset = offset_expr_of_postcard(ctx, st)
        int_ty = integer_type_of_postcard(ctx, st)
        children = list_of_postcard(pair_of_postcard(range_inclusive_of_postcard(integer_value_of_postcard), discriminator_of_postcard))(ctx, st)
        fallback = box_of_postcard(discriminator_of_postcard)(ctx, st)
        return DiscriminatorBranch(offset, int_ty, children, fallback)
    raise unknown_variant("Discriminator", __tag)

def drop_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> DropKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return DropKindPrecise()
    if __tag == 1:
        return DropKindConditional()
    raise unknown_variant("DropKind", __tag)

def dyn_predicate_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> DynPredicate:
    binder = binder_of_postcard(ty_of_postcard)(ctx, st)
    return DynPredicate(binder)

def error_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Error:
    span = span_of_postcard(ctx, st)
    msg = string_of_postcard(ctx, st)
    return Error(span, msg)

def exact_size_expr_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ExactSizeExpr:
    return dedup_val_of_postcard(
        ctx.exact_size_expr_dedup, exact_size_expr_kind_of_postcard, ctx, st
    )

def exact_size_expr_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ExactSizeExprKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = constant_expr_of_postcard(ctx, st)
        return ExactSizeExprKindExactSizeExprConstant(_0)
    if __tag == 1:
        _0 = metadata_value_of_postcard(ctx, st)
        return ExactSizeExprKindExactSizeExprFromMetadata(_0)
    if __tag == 2:
        _0 = list_of_postcard(exact_size_expr_of_postcard)(ctx, st)
        return ExactSizeExprKindExactSizeExprMax(_0)
    if __tag == 3:
        _0 = list_of_postcard(exact_size_expr_of_postcard)(ctx, st)
        return ExactSizeExprKindExactSizeExprMin(_0)
    if __tag == 4:
        _0 = exact_size_expr_of_postcard(ctx, st)
        _1 = exact_size_expr_of_postcard(ctx, st)
        return ExactSizeExprKindExactSizeExprPlus(_0, _1)
    if __tag == 5:
        _0 = exact_size_expr_of_postcard(ctx, st)
        _1 = constant_expr_of_postcard(ctx, st)
        return ExactSizeExprKindExactSizeExprScale(_0, _1)
    if __tag == 6:
        base = exact_size_expr_of_postcard(ctx, st)
        target_align = exact_size_expr_of_postcard(ctx, st)
        return ExactSizeExprKindExactSizeExprAlignTo(base, target_align)
    if __tag == 7:
        ty = ty_of_postcard(ctx, st)
        then_size = exact_size_expr_of_postcard(ctx, st)
        else_size = exact_size_expr_of_postcard(ctx, st)
        return ExactSizeExprKindExactSizeExprIfInhabited(ty, then_size, else_size)
    raise unknown_variant("ExactSizeExprKind", __tag)

def field_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Field:
    span = span_of_postcard(ctx, st)
    attr_info = attr_info_of_postcard(ctx, st)
    field_name = string_of_postcard(ctx, st)
    is_positional = bool_of_postcard(ctx, st)
    field_ty = ty_of_postcard(ctx, st)
    return Field(span, attr_info, field_name, is_positional, field_ty)

def field_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FieldId:
    return FieldId(int_of_postcard(ctx, st))

def file_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> File:
    __file_id = int_of_postcard(ctx, st)
    __file = File(
        name=file_name_of_postcard(ctx, st),
        crate_name=string_of_postcard(ctx, st),
        contents=option_of_postcard(string_of_postcard)(ctx, st),
    )
    ctx.files[__file_id] = __file
    return __file

def file_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FileId:
    __file_id = int_of_postcard(ctx, st)
    try:
        return ctx.files[__file_id]
    except KeyError:
        raise DeserializeError(
            f"unknown file id: {__file_id}. valid ids are: {sorted(ctx.files)}"
        ) from None

def file_name_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FileName:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = string_of_postcard(ctx, st)
        return FileNameVirtual(_0)
    if __tag == 1:
        _0 = string_of_postcard(ctx, st)
        return FileNameLocal(_0)
    if __tag == 2:
        _0 = string_of_postcard(ctx, st)
        return FileNameNotReal(_0)
    raise unknown_variant("FileName", __tag)

def float_type_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FloatType:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return FloatTypeF16()
    if __tag == 1:
        return FloatTypeF32()
    if __tag == 2:
        return FloatTypeF64()
    if __tag == 3:
        return FloatTypeF128()
    raise unknown_variant("FloatType", __tag)

def float_value_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FloatValue:
    float_value = string_of_postcard(ctx, st)
    float_ty = float_type_of_postcard(ctx, st)
    return FloatValue(float_value, float_ty)

def fn_operand_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FnOperand:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = fn_ptr_of_postcard(ctx, st)
        return FnOperandFnOpRegular(_0)
    if __tag == 1:
        _0 = operand_of_postcard(ctx, st)
        return FnOperandFnOpDynamic(_0)
    raise unknown_variant("FnOperand", __tag)

def fn_ptr_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FnPtr:
    kind = box_of_postcard(fn_ptr_kind_of_postcard)(ctx, st)
    generics = box_of_postcard(generic_args_of_postcard)(ctx, st)
    return FnPtr(kind, generics)

def fn_ptr_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FnPtrKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = fun_decl_id_of_postcard(ctx, st)
        return FnPtrKindFun(_0)
    if __tag == 1:
        _0 = trait_ref_of_postcard(ctx, st)
        _1 = trait_method_id_of_postcard(ctx, st)
        return FnPtrKindTraitMethod(_0, _1)
    raise unknown_variant("FnPtrKind", __tag)

def fun_decl_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FunDecl:
    def_id = fun_decl_id_of_postcard(ctx, st)
    item_meta = item_meta_of_postcard(ctx, st)
    generics = generic_params_of_postcard(ctx, st)
    signature = box_of_postcard(fun_sig_of_postcard)(ctx, st)
    src = fun_source_of_postcard(ctx, st)
    body = body_of_postcard(ctx, st)
    return FunDecl(def_id, item_meta, generics, signature, src, body)

def fun_decl_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FunDeclId:
    return FunDeclId(int_of_postcard(ctx, st))

def fun_decl_ref_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FunDeclRef:
    id = fun_decl_id_of_postcard(ctx, st)
    generics = box_of_postcard(generic_args_of_postcard)(ctx, st)
    return FunDeclRef(id, generics)

def fun_sig_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FunSig:
    is_unsafe = bool_of_postcard(ctx, st)
    abi = abi_of_postcard(ctx, st)
    is_variadic = bool_of_postcard(ctx, st)
    inputs = list_of_postcard(ty_of_postcard)(ctx, st)
    output = ty_of_postcard(ctx, st)
    return FunSig(is_unsafe, abi, is_variadic, inputs, output)

def fun_source_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> FunSource:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return FunSourceNormalFun()
    if __tag == 1:
        return FunSourceAdtConstructorFun()
    if __tag == 2:
        trait_ref = trait_decl_ref_of_postcard(ctx, st)
        item_id = trait_method_id_of_postcard(ctx, st)
        return FunSourceTraitDefaultFun(trait_ref, item_id)
    if __tag == 3:
        impl_ref = trait_impl_ref_of_postcard(ctx, st)
        trait_ref = trait_decl_ref_of_postcard(ctx, st)
        item_id = trait_method_id_of_postcard(ctx, st)
        reuses_default = bool_of_postcard(ctx, st)
        return FunSourceTraitImplFun(impl_ref, trait_ref, item_id, reuses_default)
    if __tag == 4:
        return FunSourceVTableShimFun()
    if __tag == 5:
        _0 = global_decl_ref_of_postcard(ctx, st)
        return FunSourceGlobalInitializerFun(_0)
    if __tag == 6:
        dispatcher = fun_decl_ref_of_postcard(ctx, st)
        return FunSourceTargetDependentFun(dispatcher)
    raise unknown_variant("FunSource", __tag)

def g_declaration_group_of_postcard(arg0_of_postcard: PostcardDecoder[T0]) -> PostcardDecoder[GDeclarationGroup[T0]]:
    def read(ctx: OfPostcardCtx, st: PostcardReader) -> GDeclarationGroup[T0]:
        __tag = int_of_postcard(ctx, st)
        if __tag == 0:
            _0 = arg0_of_postcard(ctx, st)
            return GDeclarationGroupNonRecGroup(_0)
        if __tag == 1:
            _0 = list_of_postcard(arg0_of_postcard)(ctx, st)
            return GDeclarationGroupRecGroup(_0)
        raise unknown_variant("GDeclarationGroup", __tag)
    return read

def gexpr_body_of_postcard(arg0_of_postcard: PostcardDecoder[T0]) -> PostcardDecoder[GexprBody[T0]]:
    def read(ctx: OfPostcardCtx, st: PostcardReader) -> GexprBody[T0]:
        span = span_of_postcard(ctx, st)
        bound_body_regions = usize_of_postcard(ctx, st)
        locals = locals_of_postcard(ctx, st)
        body = arg0_of_postcard(ctx, st)
        _ = list_of_postcard(pair_of_postcard(u32_of_postcard, list_of_postcard(string_of_postcard)))(ctx, st)
        return GexprBody(span, bound_body_regions, locals, body)
    return read

def generic_args_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> GenericArgs:
    regions = index_vec_of_postcard(region_id_of_postcard, region_of_postcard)(ctx, st)
    types = index_vec_of_postcard(type_var_id_of_postcard, ty_of_postcard)(ctx, st)
    const_generics = index_vec_of_postcard(const_generic_var_id_of_postcard, constant_expr_of_postcard)(ctx, st)
    trait_refs = index_vec_of_postcard(trait_clause_id_of_postcard, trait_ref_of_postcard)(ctx, st)
    return GenericArgs(regions, types, const_generics, trait_refs)

def generic_params_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> GenericParams:
    regions = index_vec_of_postcard(region_id_of_postcard, region_param_of_postcard)(ctx, st)
    types = index_vec_of_postcard(type_var_id_of_postcard, type_param_of_postcard)(ctx, st)
    const_generics = index_vec_of_postcard(const_generic_var_id_of_postcard, const_generic_param_of_postcard)(ctx, st)
    trait_clauses = index_vec_of_postcard(trait_clause_id_of_postcard, trait_param_of_postcard)(ctx, st)
    regions_outlive = list_of_postcard(region_binder_of_postcard(outlives_pred_of_postcard(region_of_postcard, region_of_postcard)))(ctx, st)
    types_outlive = list_of_postcard(region_binder_of_postcard(outlives_pred_of_postcard(ty_of_postcard, region_of_postcard)))(ctx, st)
    trait_type_constraints = index_vec_of_postcard(trait_type_constraint_id_of_postcard, region_binder_of_postcard(trait_type_constraint_of_postcard))(ctx, st)
    return GenericParams(regions, types, const_generics, trait_clauses, regions_outlive, types_outlive, trait_type_constraints)

def global_decl_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> GlobalDecl:
    def_id = global_decl_id_of_postcard(ctx, st)
    item_meta = item_meta_of_postcard(ctx, st)
    generics = generic_params_of_postcard(ctx, st)
    ty = ty_of_postcard(ctx, st)
    src = global_source_of_postcard(ctx, st)
    global_kind = global_kind_of_postcard(ctx, st)
    value = constant_expr_of_postcard(ctx, st)
    return GlobalDecl(def_id, item_meta, generics, ty, src, global_kind, value)

def global_decl_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> GlobalDeclId:
    return GlobalDeclId(int_of_postcard(ctx, st))

def global_decl_ref_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> GlobalDeclRef:
    id = global_decl_id_of_postcard(ctx, st)
    generics = box_of_postcard(generic_args_of_postcard)(ctx, st)
    return GlobalDeclRef(id, generics)

def global_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> GlobalKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return GlobalKindStatic()
    if __tag == 1:
        return GlobalKindThreadLocal()
    if __tag == 2:
        return GlobalKindNamedConst()
    if __tag == 3:
        return GlobalKindAnonConst()
    raise unknown_variant("GlobalKind", __tag)

def global_source_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> GlobalSource:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return GlobalSourceNormalGlobal()
    if __tag == 1:
        trait_ref = trait_decl_ref_of_postcard(ctx, st)
        item_id = assoc_const_id_of_postcard(ctx, st)
        return GlobalSourceTraitDefaultGlobal(trait_ref, item_id)
    if __tag == 2:
        impl_ref = trait_impl_ref_of_postcard(ctx, st)
        trait_ref = trait_decl_ref_of_postcard(ctx, st)
        item_id = assoc_const_id_of_postcard(ctx, st)
        reuses_default = bool_of_postcard(ctx, st)
        return GlobalSourceTraitImplGlobal(impl_ref, trait_ref, item_id, reuses_default)
    if __tag == 3:
        impl_ref = option_of_postcard(trait_impl_ref_of_postcard)(ctx, st)
        return GlobalSourceVTableInstanceGlobal(impl_ref)
    raise unknown_variant("GlobalSource", __tag)

def hash_consed_of_postcard(arg0_of_postcard: PostcardDecoder[T0]) -> PostcardDecoder[HashConsed[T0]]:
    def read(ctx: OfPostcardCtx, st: PostcardReader) -> HashConsed[T0]:
        raise DeserializeError("use `dedup_val_of_postcard` instead")
    return read

def rustc_ident_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RustcIdent:
    name = string_of_postcard(ctx, st)
    span = span_of_postcard(ctx, st)
    return RustcIdent(name, span)

def impl_elem_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ImplElem:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = box_of_postcard(binder_of_postcard(ty_of_postcard))(ctx, st)
        return ImplElemTy(_0)
    if __tag == 1:
        _0 = trait_impl_id_of_postcard(ctx, st)
        return ImplElemTrait(_0)
    raise unknown_variant("ImplElem", __tag)

def index_map_of_postcard(arg0_of_postcard: PostcardDecoder[T0], arg1_of_postcard: PostcardDecoder[T1], arg2_of_postcard: PostcardDecoder[T2]) -> PostcardDecoder[IndexMap[T0, T1, T2]]:
    def read(ctx: OfPostcardCtx, st: PostcardReader) -> IndexMap[T0, T1, T2]:
        return list_of_postcard(key_value_pair_of_postcard(arg0_of_postcard, arg1_of_postcard))(ctx, st)
    return read

def index_vec_of_postcard(arg0_of_postcard: PostcardDecoder[T0], arg1_of_postcard: PostcardDecoder[T1]) -> PostcardDecoder[IndexVec[T0, T1]]:
    def read(ctx: OfPostcardCtx, st: PostcardReader) -> IndexVec[T0, T1]:
        return list_of_postcard(arg1_of_postcard)(ctx, st)
    return read

def inline_attr_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> InlineAttr:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return InlineAttrHint()
    if __tag == 1:
        return InlineAttrNever()
    if __tag == 2:
        return InlineAttrAlways()
    raise unknown_variant("InlineAttr", __tag)

def rustc_inline_attr_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RustcInlineAttr:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return RustcInlineAttrNone()
    if __tag == 1:
        return RustcInlineAttrHint()
    if __tag == 2:
        return RustcInlineAttrAlways()
    if __tag == 3:
        return RustcInlineAttrNever()
    if __tag == 4:
        attr_span = span_of_postcard(ctx, st)
        reason = option_of_postcard(string_of_postcard)(ctx, st)
        return RustcInlineAttrForce(attr_span, reason)
    raise unknown_variant("RustcInlineAttr", __tag)

def int_ty_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> IntTy:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return IntTyIsize()
    if __tag == 1:
        return IntTyI8()
    if __tag == 2:
        return IntTyI16()
    if __tag == 3:
        return IntTyI32()
    if __tag == 4:
        return IntTyI64()
    if __tag == 5:
        return IntTyI128()
    raise unknown_variant("IntTy", __tag)

def integer_type_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> IntegerType:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = int_ty_of_postcard(ctx, st)
        return IntegerTypeSigned(_0)
    if __tag == 1:
        _0 = u_int_ty_of_postcard(ctx, st)
        return IntegerTypeUnsigned(_0)
    raise unknown_variant("IntegerType", __tag)

def integer_value_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> IntegerValue:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = u_int_ty_of_postcard(ctx, st)
        _1 = big_uint_of_postcard(ctx, st)
        return IntegerValueUnsignedInteger(_0, _1)
    if __tag == 1:
        _0 = int_ty_of_postcard(ctx, st)
        _1 = big_int_of_postcard(ctx, st)
        return IntegerValueSignedInteger(_0, _1)
    raise unknown_variant("IntegerValue", __tag)

def item_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ItemId:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = type_decl_id_of_postcard(ctx, st)
        return ItemIdIdType(_0)
    if __tag == 1:
        _0 = trait_decl_id_of_postcard(ctx, st)
        return ItemIdIdTraitDecl(_0)
    if __tag == 2:
        _0 = trait_impl_id_of_postcard(ctx, st)
        return ItemIdIdTraitImpl(_0)
    if __tag == 3:
        _0 = fun_decl_id_of_postcard(ctx, st)
        return ItemIdIdFun(_0)
    if __tag == 4:
        _0 = global_decl_id_of_postcard(ctx, st)
        return ItemIdIdGlobal(_0)
    raise unknown_variant("ItemId", __tag)

def item_meta_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ItemMeta:
    name = name_of_postcard(ctx, st)
    span = span_of_postcard(ctx, st)
    source_text = option_of_postcard(string_of_postcard)(ctx, st)
    attr_info = attr_info_of_postcard(ctx, st)
    is_local = bool_of_postcard(ctx, st)
    opacity = item_opacity_of_postcard(ctx, st)
    lang_item = option_of_postcard(rustc_lang_item_of_postcard)(ctx, st)
    diagnostic_item = option_of_postcard(string_of_postcard)(ctx, st)
    return ItemMeta(name, span, source_text, attr_info, is_local, opacity, lang_item, diagnostic_item)

def item_opacity_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ItemOpacity:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return ItemOpacityTransparent()
    if __tag == 1:
        return ItemOpacityForeign()
    if __tag == 2:
        return ItemOpacityItemOpaque()
    if __tag == 3:
        return ItemOpacityInvisible()
    raise unknown_variant("ItemOpacity", __tag)

def rustc_lang_item_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RustcLangItem:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return RustcLangItemSized()
    if __tag == 1:
        return RustcLangItemMetaSized()
    if __tag == 2:
        return RustcLangItemPointeeSized()
    if __tag == 3:
        return RustcLangItemUnsize()
    if __tag == 4:
        return RustcLangItemAlignOf()
    if __tag == 5:
        return RustcLangItemSizeOf()
    if __tag == 6:
        return RustcLangItemOffsetOf()
    if __tag == 7:
        return RustcLangItemStructuralPeq()
    if __tag == 8:
        return RustcLangItemCopy()
    if __tag == 9:
        return RustcLangItemClone()
    if __tag == 10:
        return RustcLangItemCloneFn()
    if __tag == 11:
        return RustcLangItemUseCloned()
    if __tag == 12:
        return RustcLangItemTrivialClone()
    if __tag == 13:
        return RustcLangItemSync()
    if __tag == 14:
        return RustcLangItemDiscriminantKind()
    if __tag == 15:
        return RustcLangItemDiscriminant()
    if __tag == 16:
        return RustcLangItemPointeeTrait()
    if __tag == 17:
        return RustcLangItemMetadata()
    if __tag == 18:
        return RustcLangItemDynMetadata()
    if __tag == 19:
        return RustcLangItemFreeze()
    if __tag == 20:
        return RustcLangItemUnsafeUnpin()
    if __tag == 21:
        return RustcLangItemFnPtrTrait()
    if __tag == 22:
        return RustcLangItemFnPtrAddr()
    if __tag == 23:
        return RustcLangItemDrop()
    if __tag == 24:
        return RustcLangItemDestruct()
    if __tag == 25:
        return RustcLangItemAsyncDrop()
    if __tag == 26:
        return RustcLangItemAsyncDropInPlace()
    if __tag == 27:
        return RustcLangItemCoerceUnsized()
    if __tag == 28:
        return RustcLangItemDispatchFromDyn()
    if __tag == 29:
        return RustcLangItemTryAsDyn()
    if __tag == 30:
        return RustcLangItemTransmuteOpts()
    if __tag == 31:
        return RustcLangItemTransmuteTrait()
    if __tag == 32:
        return RustcLangItemAdd()
    if __tag == 33:
        return RustcLangItemSub()
    if __tag == 34:
        return RustcLangItemMul()
    if __tag == 35:
        return RustcLangItemDiv()
    if __tag == 36:
        return RustcLangItemRem()
    if __tag == 37:
        return RustcLangItemNeg()
    if __tag == 38:
        return RustcLangItemNot()
    if __tag == 39:
        return RustcLangItemBitXor()
    if __tag == 40:
        return RustcLangItemBitAnd()
    if __tag == 41:
        return RustcLangItemBitOr()
    if __tag == 42:
        return RustcLangItemShl()
    if __tag == 43:
        return RustcLangItemShr()
    if __tag == 44:
        return RustcLangItemAddAssign()
    if __tag == 45:
        return RustcLangItemSubAssign()
    if __tag == 46:
        return RustcLangItemMulAssign()
    if __tag == 47:
        return RustcLangItemDivAssign()
    if __tag == 48:
        return RustcLangItemRemAssign()
    if __tag == 49:
        return RustcLangItemBitXorAssign()
    if __tag == 50:
        return RustcLangItemBitAndAssign()
    if __tag == 51:
        return RustcLangItemBitOrAssign()
    if __tag == 52:
        return RustcLangItemShlAssign()
    if __tag == 53:
        return RustcLangItemShrAssign()
    if __tag == 54:
        return RustcLangItemIndex()
    if __tag == 55:
        return RustcLangItemIndexMut()
    if __tag == 56:
        return RustcLangItemUnsafeCell()
    if __tag == 57:
        return RustcLangItemCovariantUnsafeCell()
    if __tag == 58:
        return RustcLangItemUnsafePinned()
    if __tag == 59:
        return RustcLangItemVaArgSafe()
    if __tag == 60:
        return RustcLangItemVaList()
    if __tag == 61:
        return RustcLangItemComplex()
    if __tag == 62:
        return RustcLangItemDeref()
    if __tag == 63:
        return RustcLangItemDerefMut()
    if __tag == 64:
        return RustcLangItemDerefPure()
    if __tag == 65:
        return RustcLangItemDerefTarget()
    if __tag == 66:
        return RustcLangItemReceiver()
    if __tag == 67:
        return RustcLangItemReceiverTarget()
    if __tag == 68:
        return RustcLangItemLegacyReceiver()
    if __tag == 69:
        return RustcLangItemFn()
    if __tag == 70:
        return RustcLangItemFnMut()
    if __tag == 71:
        return RustcLangItemFnOnce()
    if __tag == 72:
        return RustcLangItemAsyncFn()
    if __tag == 73:
        return RustcLangItemAsyncFnMut()
    if __tag == 74:
        return RustcLangItemAsyncFnOnce()
    if __tag == 75:
        return RustcLangItemAsyncFnOnceOutput()
    if __tag == 76:
        return RustcLangItemCallOnceFuture()
    if __tag == 77:
        return RustcLangItemCallRefFuture()
    if __tag == 78:
        return RustcLangItemAsyncFnKindHelper()
    if __tag == 79:
        return RustcLangItemAsyncFnKindUpvars()
    if __tag == 80:
        return RustcLangItemFnOnceOutput()
    if __tag == 81:
        return RustcLangItemIterator()
    if __tag == 82:
        return RustcLangItemFusedIterator()
    if __tag == 83:
        return RustcLangItemFuture()
    if __tag == 84:
        return RustcLangItemFutureOutput()
    if __tag == 85:
        return RustcLangItemAsyncIterator()
    if __tag == 86:
        return RustcLangItemCoroutineState()
    if __tag == 87:
        return RustcLangItemCoroutine()
    if __tag == 88:
        return RustcLangItemCoroutineReturn()
    if __tag == 89:
        return RustcLangItemCoroutineYield()
    if __tag == 90:
        return RustcLangItemCoroutineResume()
    if __tag == 91:
        return RustcLangItemUnpin()
    if __tag == 92:
        return RustcLangItemPin()
    if __tag == 93:
        return RustcLangItemOrderingEnum()
    if __tag == 94:
        return RustcLangItemPartialEq()
    if __tag == 95:
        return RustcLangItemPartialOrd()
    if __tag == 96:
        return RustcLangItemCVoid()
    if __tag == 97:
        return RustcLangItemType()
    if __tag == 98:
        return RustcLangItemTypeGeneric()
    if __tag == 99:
        return RustcLangItemTypeId()
    if __tag == 100:
        return RustcLangItemPanic()
    if __tag == 101:
        return RustcLangItemPanicNounwind()
    if __tag == 102:
        return RustcLangItemPanicFmt()
    if __tag == 103:
        return RustcLangItemPanicDisplay()
    if __tag == 104:
        return RustcLangItemConstPanicFmt()
    if __tag == 105:
        return RustcLangItemPanicBoundsCheck()
    if __tag == 106:
        return RustcLangItemPanicMisalignedPointerDereference()
    if __tag == 107:
        return RustcLangItemPanicInfo()
    if __tag == 108:
        return RustcLangItemPanicLocation()
    if __tag == 109:
        return RustcLangItemPanicImpl()
    if __tag == 110:
        return RustcLangItemPanicCannotUnwind()
    if __tag == 111:
        return RustcLangItemPanicInCleanup()
    if __tag == 112:
        return RustcLangItemPanicAddOverflow()
    if __tag == 113:
        return RustcLangItemPanicSubOverflow()
    if __tag == 114:
        return RustcLangItemPanicMulOverflow()
    if __tag == 115:
        return RustcLangItemPanicDivOverflow()
    if __tag == 116:
        return RustcLangItemPanicRemOverflow()
    if __tag == 117:
        return RustcLangItemPanicNegOverflow()
    if __tag == 118:
        return RustcLangItemPanicShrOverflow()
    if __tag == 119:
        return RustcLangItemPanicShlOverflow()
    if __tag == 120:
        return RustcLangItemPanicDivZero()
    if __tag == 121:
        return RustcLangItemPanicRemZero()
    if __tag == 122:
        return RustcLangItemPanicCoroutineResumed()
    if __tag == 123:
        return RustcLangItemPanicAsyncFnResumed()
    if __tag == 124:
        return RustcLangItemPanicAsyncGenFnResumed()
    if __tag == 125:
        return RustcLangItemPanicGenFnNone()
    if __tag == 126:
        return RustcLangItemPanicCoroutineResumedPanic()
    if __tag == 127:
        return RustcLangItemPanicAsyncFnResumedPanic()
    if __tag == 128:
        return RustcLangItemPanicAsyncGenFnResumedPanic()
    if __tag == 129:
        return RustcLangItemPanicGenFnNonePanic()
    if __tag == 130:
        return RustcLangItemPanicNullPointerDereference()
    if __tag == 131:
        return RustcLangItemPanicNullReferenceConstructed()
    if __tag == 132:
        return RustcLangItemPanicInvalidEnumConstruction()
    if __tag == 133:
        return RustcLangItemPanicCoroutineResumedDrop()
    if __tag == 134:
        return RustcLangItemPanicAsyncFnResumedDrop()
    if __tag == 135:
        return RustcLangItemPanicAsyncGenFnResumedDrop()
    if __tag == 136:
        return RustcLangItemPanicGenFnNoneDrop()
    if __tag == 137:
        return RustcLangItemBeginPanic()
    if __tag == 138:
        return RustcLangItemFormatArgument()
    if __tag == 139:
        return RustcLangItemFormatArguments()
    if __tag == 140:
        return RustcLangItemDropGlue()
    if __tag == 141:
        return RustcLangItemAllocLayout()
    if __tag == 142:
        return RustcLangItemStart()
    if __tag == 143:
        return RustcLangItemEhPersonality()
    if __tag == 144:
        return RustcLangItemCompilerMove()
    if __tag == 145:
        return RustcLangItemCompilerCopy()
    if __tag == 146:
        return RustcLangItemOwnedBox()
    if __tag == 147:
        return RustcLangItemGlobalAlloc()
    if __tag == 148:
        return RustcLangItemPhantomData()
    if __tag == 149:
        return RustcLangItemManuallyDrop()
    if __tag == 150:
        return RustcLangItemMaybeDangling()
    if __tag == 151:
        return RustcLangItemBikeshedGuaranteedNoDrop()
    if __tag == 152:
        return RustcLangItemMaybeUninit()
    if __tag == 153:
        return RustcLangItemTermination()
    if __tag == 154:
        return RustcLangItemTry()
    if __tag == 155:
        return RustcLangItemTuple()
    if __tag == 156:
        return RustcLangItemSliceLen()
    if __tag == 157:
        return RustcLangItemTryTraitFromResidual()
    if __tag == 158:
        return RustcLangItemTryTraitFromOutput()
    if __tag == 159:
        return RustcLangItemTryTraitBranch()
    if __tag == 160:
        return RustcLangItemTryTraitFromYeet()
    if __tag == 161:
        return RustcLangItemResidualIntoTryType()
    if __tag == 162:
        return RustcLangItemCoercePointeeValidated()
    if __tag == 163:
        return RustcLangItemConstParamTy()
    if __tag == 164:
        return RustcLangItemPoll()
    if __tag == 165:
        return RustcLangItemPollReady()
    if __tag == 166:
        return RustcLangItemPollPending()
    if __tag == 167:
        return RustcLangItemAsyncGenReady()
    if __tag == 168:
        return RustcLangItemAsyncGenPending()
    if __tag == 169:
        return RustcLangItemAsyncGenFinished()
    if __tag == 170:
        return RustcLangItemResumeTy()
    if __tag == 171:
        return RustcLangItemGetContext()
    if __tag == 172:
        return RustcLangItemContext()
    if __tag == 173:
        return RustcLangItemFuturePoll()
    if __tag == 174:
        return RustcLangItemAsyncIteratorPollNext()
    if __tag == 175:
        return RustcLangItemIntoAsyncIterIntoIter()
    if __tag == 176:
        return RustcLangItemOption()
    if __tag == 177:
        return RustcLangItemOptionSome()
    if __tag == 178:
        return RustcLangItemOptionNone()
    if __tag == 179:
        return RustcLangItemResultOk()
    if __tag == 180:
        return RustcLangItemResultErr()
    if __tag == 181:
        return RustcLangItemControlFlowContinue()
    if __tag == 182:
        return RustcLangItemControlFlowBreak()
    if __tag == 183:
        return RustcLangItemIntoFutureIntoFuture()
    if __tag == 184:
        return RustcLangItemIntoIterIntoIter()
    if __tag == 185:
        return RustcLangItemIteratorNext()
    if __tag == 186:
        return RustcLangItemPinNewUnchecked()
    if __tag == 187:
        return RustcLangItemRangeFrom()
    if __tag == 188:
        return RustcLangItemRangeFull()
    if __tag == 189:
        return RustcLangItemRangeInclusiveStruct()
    if __tag == 190:
        return RustcLangItemRangeInclusiveNew()
    if __tag == 191:
        return RustcLangItemRange()
    if __tag == 192:
        return RustcLangItemRangeToInclusive()
    if __tag == 193:
        return RustcLangItemRangeTo()
    if __tag == 194:
        return RustcLangItemRangeMax()
    if __tag == 195:
        return RustcLangItemRangeMin()
    if __tag == 196:
        return RustcLangItemRangeSub()
    if __tag == 197:
        return RustcLangItemRangeFromCopy()
    if __tag == 198:
        return RustcLangItemRangeCopy()
    if __tag == 199:
        return RustcLangItemRangeInclusiveCopy()
    if __tag == 200:
        return RustcLangItemRangeToInclusiveCopy()
    if __tag == 201:
        return RustcLangItemString()
    if __tag == 202:
        return RustcLangItemCStr()
    if __tag == 203:
        return RustcLangItemContractBuildCheckEnsures()
    if __tag == 204:
        return RustcLangItemContractCheckRequires()
    if __tag == 205:
        return RustcLangItemDefaultTrait4()
    if __tag == 206:
        return RustcLangItemDefaultTrait3()
    if __tag == 207:
        return RustcLangItemDefaultTrait2()
    if __tag == 208:
        return RustcLangItemDefaultTrait1()
    if __tag == 209:
        return RustcLangItemContractCheckEnsures()
    if __tag == 210:
        return RustcLangItemReborrow()
    if __tag == 211:
        return RustcLangItemCoerceShared()
    if __tag == 212:
        return RustcLangItemFieldRepresentingType()
    if __tag == 213:
        return RustcLangItemField()
    if __tag == 214:
        return RustcLangItemFieldBase()
    if __tag == 215:
        return RustcLangItemFieldType()
    if __tag == 216:
        return RustcLangItemFieldOffset()
    if __tag == 217:
        return RustcLangItemFrom()
    if __tag == 218:
        return RustcLangItemFromFn()
    raise unknown_variant("RustcLangItem", __tag)

def layout_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Layout:
    size = size_expr_of_postcard(ctx, st)
    align = size_expr_of_postcard(ctx, st)
    discriminator = option_of_postcard(discriminator_of_postcard)(ctx, st)
    uninhabited = bool_of_postcard(ctx, st)
    variant_layouts = index_vec_of_postcard(variant_id_of_postcard, option_of_postcard(variant_layout_of_postcard))(ctx, st)
    repr = repr_options_of_postcard(ctx, st)
    return Layout(size, align, discriminator, uninhabited, variant_layouts, repr)

def lifetime_mutability_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> LifetimeMutability:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return LifetimeMutabilityLtMutable()
    if __tag == 1:
        return LifetimeMutabilityLtShared()
    if __tag == 2:
        return LifetimeMutabilityLtUnknown()
    raise unknown_variant("LifetimeMutability", __tag)

def loc_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Loc:
    line = u32_of_postcard(ctx, st)
    col = u32_of_postcard(ctx, st)
    return Loc(line, col)

def local_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Local:
    index = local_id_of_postcard(ctx, st)
    name = option_of_postcard(string_of_postcard)(ctx, st)
    span = span_of_postcard(ctx, st)
    local_ty = ty_of_postcard(ctx, st)
    return Local(index, name, span, local_ty)

def local_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> LocalId:
    return LocalId(int_of_postcard(ctx, st))

def locals_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Locals:
    arg_count = usize_of_postcard(ctx, st)
    locals = index_vec_of_postcard(local_id_of_postcard, local_of_postcard)(ctx, st)
    return Locals(arg_count, locals)

def maybe_assoc_item_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> MaybeAssocItemId:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = item_id_of_postcard(ctx, st)
        return MaybeAssocItemIdItemFree(_0)
    if __tag == 1:
        _0 = trait_decl_id_of_postcard(ctx, st)
        _1 = assoc_item_id_of_postcard(ctx, st)
        return MaybeAssocItemIdItemAssoc(_0, _1)
    raise unknown_variant("MaybeAssocItemId", __tag)

def metadata_value_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> MetadataValue:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return MetadataValueDynSize()
    if __tag == 1:
        return MetadataValueDynAlign()
    if __tag == 2:
        return MetadataValueSliceLength()
    raise unknown_variant("MetadataValue", __tag)

def mir_level_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> MirLevel:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return MirLevelBuilt()
    if __tag == 1:
        return MirLevelPromoted()
    if __tag == 2:
        return MirLevelElaborated()
    if __tag == 3:
        return MirLevelOptimized()
    raise unknown_variant("MirLevel", __tag)

def monomorphize_mut_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> MonomorphizeMut:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return MonomorphizeMutAll()
    if __tag == 1:
        return MonomorphizeMutExceptTypes()
    raise unknown_variant("MonomorphizeMut", __tag)

def name_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Name:
    return list_of_postcard(path_elem_of_postcard)(ctx, st)

def nullop_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Nullop:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return NullopSizeOf()
    if __tag == 1:
        return NullopAlignOf()
    if __tag == 2:
        _0 = type_decl_ref_of_postcard(ctx, st)
        _1 = option_of_postcard(variant_id_of_postcard)(ctx, st)
        _2 = field_id_of_postcard(ctx, st)
        return NullopOffsetOf(_0, _1, _2)
    if __tag == 3:
        return NullopUbChecks()
    if __tag == 4:
        return NullopOverflowChecks()
    if __tag == 5:
        return NullopContractChecks()
    raise unknown_variant("Nullop", __tag)

def offset_expr_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> OffsetExpr:
    guarantee = option_of_postcard(offset_guarantee_of_postcard)(ctx, st)
    chosen = option_of_postcard(u64_of_postcard)(ctx, st)
    return OffsetExpr(guarantee, chosen)

def offset_guarantee_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> OffsetGuarantee:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return OffsetGuaranteeAtOffsetZero()
    if __tag == 1:
        _0 = exact_size_expr_of_postcard(ctx, st)
        return OffsetGuaranteeGuaranteedAlignment(_0)
    if __tag == 2:
        predecessor = option_of_postcard(field_id_of_postcard)(ctx, st)
        return OffsetGuaranteeReprCField(predecessor)
    raise unknown_variant("OffsetGuarantee", __tag)

def operand_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Operand:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = place_of_postcard(ctx, st)
        return OperandCopy(_0)
    if __tag == 1:
        _0 = place_of_postcard(ctx, st)
        return OperandMove(_0)
    if __tag == 2:
        _0 = constant_expr_of_postcard(ctx, st)
        return OperandConstant(_0)
    raise unknown_variant("Operand", __tag)

def rustc_optimize_attr_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RustcOptimizeAttr:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return RustcOptimizeAttrDefault()
    if __tag == 1:
        return RustcOptimizeAttrDoNotOptimize()
    if __tag == 2:
        return RustcOptimizeAttrSpeed()
    if __tag == 3:
        return RustcOptimizeAttrSize()
    raise unknown_variant("RustcOptimizeAttr", __tag)

def outlives_pred_of_postcard(arg0_of_postcard: PostcardDecoder[T0], arg1_of_postcard: PostcardDecoder[T1]) -> PostcardDecoder[OutlivesPred[T0, T1]]:
    def read(ctx: OfPostcardCtx, st: PostcardReader) -> OutlivesPred[T0, T1]:
        _0 = arg0_of_postcard(ctx, st)
        _1 = arg1_of_postcard(ctx, st)
        return OutlivesPred(_0, _1)
    return read

def overflow_mode_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> OverflowMode:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return OverflowModeOPanic()
    if __tag == 1:
        return OverflowModeOUB()
    if __tag == 2:
        return OverflowModeOWrap()
    raise unknown_variant("OverflowMode", __tag)

def path_elem_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> PathElem:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = string_of_postcard(ctx, st)
        _1 = disambiguator_of_postcard(ctx, st)
        return PathElemPeIdent(_0, _1)
    if __tag == 1:
        _0 = impl_elem_of_postcard(ctx, st)
        return PathElemPeImpl(_0)
    if __tag == 2:
        _0 = box_of_postcard(binder_of_postcard(generic_args_of_postcard))(ctx, st)
        return PathElemPeInstantiated(_0)
    if __tag == 3:
        _0 = string_of_postcard(ctx, st)
        return PathElemPeTarget(_0)
    if __tag == 4:
        _0 = builtin_path_elem_of_postcard(ctx, st)
        _1 = disambiguator_of_postcard(ctx, st)
        return PathElemPeBuiltin(_0, _1)
    raise unknown_variant("PathElem", __tag)

def place_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Place:
    kind = place_kind_of_postcard(ctx, st)
    ty = ty_of_postcard(ctx, st)
    return Place(kind, ty)

def place_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> PlaceKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = local_id_of_postcard(ctx, st)
        return PlaceKindPlaceLocal(_0)
    if __tag == 1:
        _0 = box_of_postcard(place_of_postcard)(ctx, st)
        _1 = projection_elem_of_postcard(ctx, st)
        return PlaceKindPlaceProjection(_0, _1)
    if __tag == 2:
        _0 = global_decl_ref_of_postcard(ctx, st)
        return PlaceKindPlaceGlobal(_0)
    raise unknown_variant("PlaceKind", __tag)

def predicate_origin_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> PredicateOrigin:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return PredicateOriginWhereClauseOnFn()
    if __tag == 1:
        return PredicateOriginWhereClauseOnType()
    if __tag == 2:
        return PredicateOriginWhereClauseOnImpl()
    if __tag == 3:
        return PredicateOriginTraitSelf()
    if __tag == 4:
        return PredicateOriginWhereClauseOnTrait()
    if __tag == 5:
        _0 = assoc_type_id_of_postcard(ctx, st)
        return PredicateOriginTraitItem(_0)
    if __tag == 6:
        return PredicateOriginOriginDyn()
    raise unknown_variant("PredicateOrigin", __tag)

def preset_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Preset:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return PresetOldDefaults()
    if __tag == 1:
        return PresetRawMir()
    if __tag == 2:
        return PresetFast()
    if __tag == 3:
        return PresetAeneas()
    if __tag == 4:
        return PresetEurydice()
    if __tag == 5:
        return PresetSoteria()
    if __tag == 6:
        return PresetTests()
    raise unknown_variant("Preset", __tag)

def projection_elem_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ProjectionElem:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return ProjectionElemDeref()
    if __tag == 1:
        _0 = option_of_postcard(variant_id_of_postcard)(ctx, st)
        _1 = field_id_of_postcard(ctx, st)
        return ProjectionElemField(_0, _1)
    if __tag == 2:
        return ProjectionElemPtrMetadata()
    if __tag == 3:
        offset = box_of_postcard(operand_of_postcard)(ctx, st)
        from_end = bool_of_postcard(ctx, st)
        return ProjectionElemProjIndex(offset, from_end)
    if __tag == 4:
        from_ = box_of_postcard(operand_of_postcard)(ctx, st)
        to = box_of_postcard(operand_of_postcard)(ctx, st)
        from_end = bool_of_postcard(ctx, st)
        return ProjectionElemSubslice(from_, to, from_end)
    raise unknown_variant("ProjectionElem", __tag)

def provenance_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Provenance:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = global_decl_ref_of_postcard(ctx, st)
        return ProvenanceProvGlobal(_0)
    if __tag == 1:
        _0 = fun_decl_ref_of_postcard(ctx, st)
        return ProvenanceProvFunction(_0)
    if __tag == 2:
        return ProvenanceProvUnknown()
    raise unknown_variant("Provenance", __tag)

def ptr_metadata_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> PtrMetadata:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return PtrMetadataNoMetadata()
    if __tag == 1:
        return PtrMetadataLength()
    if __tag == 2:
        _0 = type_decl_ref_of_postcard(ctx, st)
        return PtrMetadataVTable(_0)
    if __tag == 3:
        _0 = ty_of_postcard(ctx, st)
        return PtrMetadataInheritFrom(_0)
    raise unknown_variant("PtrMetadata", __tag)

def raw_attribute_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RawAttribute:
    path = string_of_postcard(ctx, st)
    args = option_of_postcard(string_of_postcard)(ctx, st)
    return RawAttribute(path, args)

def ref_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RefKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return RefKindRMut()
    if __tag == 1:
        return RefKindRShared()
    raise unknown_variant("RefKind", __tag)

def region_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Region:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = de_bruijn_var_of_postcard(region_id_of_postcard)(ctx, st)
        return RegionRVar(_0)
    if __tag == 1:
        return RegionRStatic()
    if __tag == 2:
        _0 = region_id_of_postcard(ctx, st)
        return RegionRBody(_0)
    if __tag == 3:
        return RegionRErased()
    raise unknown_variant("Region", __tag)

def region_binder_of_postcard(arg0_of_postcard: PostcardDecoder[T0]) -> PostcardDecoder[RegionBinder[T0]]:
    def read(ctx: OfPostcardCtx, st: PostcardReader) -> RegionBinder[T0]:
        binder_regions = index_vec_of_postcard(region_id_of_postcard, region_param_of_postcard)(ctx, st)
        binder_value = arg0_of_postcard(ctx, st)
        return RegionBinder(binder_regions, binder_value)
    return read

def region_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RegionId:
    return RegionId(int_of_postcard(ctx, st))

def region_param_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RegionParam:
    index = region_id_of_postcard(ctx, st)
    name = option_of_postcard(string_of_postcard)(ctx, st)
    variance = variance_of_postcard(ctx, st)
    mutability = lifetime_mutability_of_postcard(ctx, st)
    return RegionParam(index, name, variance, mutability)

def repr_algorithm_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ReprAlgorithm:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return ReprAlgorithmRust()
    if __tag == 1:
        return ReprAlgorithmC()
    raise unknown_variant("ReprAlgorithm", __tag)

def repr_options_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ReprOptions:
    repr_algo = repr_algorithm_of_postcard(ctx, st)
    align_modif = option_of_postcard(alignment_modifier_of_postcard)(ctx, st)
    transparent = bool_of_postcard(ctx, st)
    explicit_discr_type = option_of_postcard(integer_type_of_postcard)(ctx, st)
    return ReprOptions(repr_algo, align_modif, transparent, explicit_discr_type)

def rustc_rustc_version_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> RustcRustcVersion:
    major = u16_of_postcard(ctx, st)
    minor = u16_of_postcard(ctx, st)
    patch = u16_of_postcard(ctx, st)
    return RustcRustcVersion(major, minor, patch)

def rvalue_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Rvalue:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = operand_of_postcard(ctx, st)
        _1 = with_retag_of_postcard(ctx, st)
        return RvalueUse(_0, _1)
    if __tag == 1:
        place = place_of_postcard(ctx, st)
        kind = borrow_kind_of_postcard(ctx, st)
        ptr_metadata = operand_of_postcard(ctx, st)
        return RvalueRvRef(place, kind, ptr_metadata)
    if __tag == 2:
        place = place_of_postcard(ctx, st)
        kind = ref_kind_of_postcard(ctx, st)
        ptr_metadata = operand_of_postcard(ctx, st)
        return RvalueRawPtr(place, kind, ptr_metadata)
    if __tag == 3:
        _0 = binop_of_postcard(ctx, st)
        _1 = operand_of_postcard(ctx, st)
        _2 = operand_of_postcard(ctx, st)
        return RvalueBinaryOp(_0, _1, _2)
    if __tag == 4:
        _0 = unop_of_postcard(ctx, st)
        _1 = operand_of_postcard(ctx, st)
        return RvalueUnaryOp(_0, _1)
    if __tag == 5:
        _0 = nullop_of_postcard(ctx, st)
        _1 = ty_of_postcard(ctx, st)
        return RvalueNullaryOp(_0, _1)
    if __tag == 6:
        _0 = place_of_postcard(ctx, st)
        return RvalueDiscriminant(_0)
    if __tag == 7:
        _0 = aggregate_kind_of_postcard(ctx, st)
        _1 = list_of_postcard(operand_of_postcard)(ctx, st)
        return RvalueAggregate(_0, _1)
    if __tag == 8:
        _0 = place_of_postcard(ctx, st)
        _1 = ty_of_postcard(ctx, st)
        _2 = option_of_postcard(constant_expr_of_postcard)(ctx, st)
        return RvalueLen(_0, _1, _2)
    if __tag == 9:
        _0 = operand_of_postcard(ctx, st)
        _1 = ty_of_postcard(ctx, st)
        _2 = constant_expr_of_postcard(ctx, st)
        _3 = trait_ref_of_postcard(ctx, st)
        return RvalueRepeat(_0, _1, _2, _3)
    raise unknown_variant("Rvalue", __tag)

def scalar_type_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> ScalarType:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = integer_type_of_postcard(ctx, st)
        return ScalarTypeTInteger(_0)
    if __tag == 1:
        _0 = float_type_of_postcard(ctx, st)
        return ScalarTypeTFloat(_0)
    if __tag == 2:
        return ScalarTypeTBool()
    if __tag == 3:
        return ScalarTypeTChar()
    raise unknown_variant("ScalarType", __tag)

def serialization_format_arg_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> SerializationFormatArg:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return SerializationFormatArgJson()
    if __tag == 1:
        return SerializationFormatArgPostcard()
    if __tag == 2:
        return SerializationFormatArgAllFormats()
    raise unknown_variant("SerializationFormatArg", __tag)

def size_expr_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> SizeExpr:
    guarantee = option_of_postcard(size_guarantee_of_postcard)(ctx, st)
    chosen = option_of_postcard(u64_of_postcard)(ctx, st)
    return SizeExpr(guarantee, chosen)

def size_guarantee_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> SizeGuarantee:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = exact_size_expr_of_postcard(ctx, st)
        return SizeGuaranteeEquals(_0)
    if __tag == 1:
        _0 = exact_size_expr_of_postcard(ctx, st)
        return SizeGuaranteeAtLeast(_0)
    raise unknown_variant("SizeGuarantee", __tag)

def span_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Span:
    def read_contents(ctx: OfPostcardCtx, st: PostcardReader) -> Span:
        data = span_data_of_postcard(ctx, st)
        generated_from_span = option_of_postcard(span_data_of_postcard)(ctx, st)
        return Span(data=data, generated_from_span=generated_from_span)

    return dedup_val_of_postcard(ctx.span_dedup, read_contents, ctx, st)

def span_data_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> SpanData:
    file = file_id_of_postcard(ctx, st)
    beg_loc = loc_of_postcard(ctx, st)
    end_loc = loc_of_postcard(ctx, st)
    return SpanData(file, beg_loc, end_loc)

def ullbc_statement_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> UllbcStatement:
    span = span_of_postcard(ctx, st)
    kind = ullbc_statement_kind_of_postcard(ctx, st)
    comments_before = list_of_postcard(string_of_postcard)(ctx, st)
    return UllbcStatement(span, kind, comments_before)

def llbc_statement_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> LlbcStatement:
    span = span_of_postcard(ctx, st)
    statement_id = statement_id_of_postcard(ctx, st)
    kind = llbc_statement_kind_of_postcard(ctx, st)
    comments_before = list_of_postcard(string_of_postcard)(ctx, st)
    return LlbcStatement(span, statement_id, kind, comments_before)

def statement_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> StatementId:
    return StatementId(int_of_postcard(ctx, st))

def ullbc_statement_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> UllbcStatementKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = place_of_postcard(ctx, st)
        _1 = rvalue_of_postcard(ctx, st)
        return UllbcStatementKindAssign(_0, _1)
    if __tag == 1:
        _0 = place_of_postcard(ctx, st)
        _1 = variant_id_of_postcard(ctx, st)
        return UllbcStatementKindSetDiscriminant(_0, _1)
    if __tag == 2:
        _0 = local_id_of_postcard(ctx, st)
        return UllbcStatementKindStorageLive(_0)
    if __tag == 3:
        _0 = local_id_of_postcard(ctx, st)
        return UllbcStatementKindStorageDead(_0)
    if __tag == 4:
        _0 = place_of_postcard(ctx, st)
        return UllbcStatementKindPlaceMention(_0)
    if __tag == 5:
        _0 = borrowck_statement_of_postcard(ctx, st)
        return UllbcStatementKindBorrowck(_0)
    if __tag == 6:
        assert_ = assertion_of_postcard(ctx, st)
        on_failure = abort_kind_of_postcard(ctx, st)
        return UllbcStatementKindAssert(assert_, on_failure)
    if __tag == 7:
        return UllbcStatementKindNop()
    raise unknown_variant("UllbcStatementKind", __tag)

def llbc_statement_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> LlbcStatementKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = place_of_postcard(ctx, st)
        _1 = rvalue_of_postcard(ctx, st)
        return LlbcStatementKindAssign(_0, _1)
    if __tag == 1:
        _0 = place_of_postcard(ctx, st)
        _1 = variant_id_of_postcard(ctx, st)
        return LlbcStatementKindSetDiscriminant(_0, _1)
    if __tag == 2:
        _0 = local_id_of_postcard(ctx, st)
        return LlbcStatementKindStorageLive(_0)
    if __tag == 3:
        _0 = local_id_of_postcard(ctx, st)
        return LlbcStatementKindStorageDead(_0)
    if __tag == 4:
        _0 = place_of_postcard(ctx, st)
        return LlbcStatementKindPlaceMention(_0)
    if __tag == 5:
        _0 = borrowck_statement_of_postcard(ctx, st)
        return LlbcStatementKindBorrowck(_0)
    if __tag == 6:
        place = place_of_postcard(ctx, st)
        fn_ptr = fn_ptr_of_postcard(ctx, st)
        kind = drop_kind_of_postcard(ctx, st)
        on_unwind = llbc_block_of_postcard(ctx, st)
        return LlbcStatementKindDrop(place, fn_ptr, kind, on_unwind)
    if __tag == 7:
        assert_ = assertion_of_postcard(ctx, st)
        on_failure = abort_kind_of_postcard(ctx, st)
        on_unwind = llbc_block_of_postcard(ctx, st)
        return LlbcStatementKindAssert(assert_, on_failure, on_unwind)
    if __tag == 8:
        asm = string_of_postcard(ctx, st)
        targets = list_of_postcard(llbc_block_of_postcard)(ctx, st)
        on_unwind = llbc_block_of_postcard(ctx, st)
        return LlbcStatementKindInlineAsm(asm, targets, on_unwind)
    if __tag == 9:
        call = call_of_postcard(ctx, st)
        on_unwind = llbc_block_of_postcard(ctx, st)
        return LlbcStatementKindCall(call, on_unwind)
    if __tag == 10:
        _0 = abort_kind_of_postcard(ctx, st)
        return LlbcStatementKindAbort(_0)
    if __tag == 11:
        return LlbcStatementKindReturn()
    if __tag == 12:
        return LlbcStatementKindUnwindResume()
    if __tag == 13:
        _0 = usize_of_postcard(ctx, st)
        return LlbcStatementKindBreak(_0)
    if __tag == 14:
        _0 = usize_of_postcard(ctx, st)
        return LlbcStatementKindContinue(_0)
    if __tag == 15:
        return LlbcStatementKindNop()
    if __tag == 16:
        data = switch_data_of_postcard(ctx, st)
        branches = index_vec_of_postcard(branch_id_of_postcard, llbc_block_of_postcard)(ctx, st)
        return LlbcStatementKindSwitch(data, branches)
    if __tag == 17:
        _0 = llbc_block_of_postcard(ctx, st)
        return LlbcStatementKindLoop(_0)
    if __tag == 18:
        _0 = string_of_postcard(ctx, st)
        return LlbcStatementKindError(_0)
    raise unknown_variant("LlbcStatementKind", __tag)

def switch_data_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> SwitchData:
    scrutinee = switch_scrutinee_of_postcard(ctx, st)
    branches = list_of_postcard(pair_of_postcard(constant_expr_of_postcard, branch_id_of_postcard))(ctx, st)
    fallback = option_of_postcard(branch_id_of_postcard)(ctx, st)
    return SwitchData(scrutinee, branches, fallback)

def switch_scrutinee_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> SwitchScrutinee:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = operand_of_postcard(ctx, st)
        return SwitchScrutineeSwitchValue(_0)
    if __tag == 1:
        _0 = place_of_postcard(ctx, st)
        return SwitchScrutineeSwitchDiscriminant(_0)
    raise unknown_variant("SwitchScrutinee", __tag)

def target_info_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TargetInfo:
    target_pointer_size = u64_of_postcard(ctx, st)
    is_little_endian = bool_of_postcard(ctx, st)
    c_enum_smallest_repr_ty = int_ty_of_postcard(ctx, st)
    primitive_alignments = index_map_of_postcard(scalar_type_of_postcard, u64_of_postcard, int_of_postcard)(ctx, st)
    return TargetInfo(target_pointer_size, is_little_endian, c_enum_smallest_repr_ty, primitive_alignments)

def terminator_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Terminator:
    span = span_of_postcard(ctx, st)
    kind = terminator_kind_of_postcard(ctx, st)
    comments_before = list_of_postcard(string_of_postcard)(ctx, st)
    return Terminator(span, kind, comments_before)

def terminator_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TerminatorKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        target = ullbc_block_id_of_postcard(ctx, st)
        return TerminatorKindGoto(target)
    if __tag == 1:
        data = switch_data_of_postcard(ctx, st)
        branches = index_vec_of_postcard(branch_id_of_postcard, ullbc_block_id_of_postcard)(ctx, st)
        return TerminatorKindSwitch(data, branches)
    if __tag == 2:
        call = call_of_postcard(ctx, st)
        target = ullbc_block_id_of_postcard(ctx, st)
        on_unwind = ullbc_block_id_of_postcard(ctx, st)
        return TerminatorKindCall(call, target, on_unwind)
    if __tag == 3:
        kind = drop_kind_of_postcard(ctx, st)
        place = place_of_postcard(ctx, st)
        fn_ptr = fn_ptr_of_postcard(ctx, st)
        target = ullbc_block_id_of_postcard(ctx, st)
        on_unwind = ullbc_block_id_of_postcard(ctx, st)
        return TerminatorKindDrop(kind, place, fn_ptr, target, on_unwind)
    if __tag == 4:
        assert_ = assertion_of_postcard(ctx, st)
        target = ullbc_block_id_of_postcard(ctx, st)
        on_unwind = ullbc_block_id_of_postcard(ctx, st)
        return TerminatorKindTAssert(assert_, target, on_unwind)
    if __tag == 5:
        asm = string_of_postcard(ctx, st)
        targets = list_of_postcard(ullbc_block_id_of_postcard)(ctx, st)
        on_unwind = ullbc_block_id_of_postcard(ctx, st)
        return TerminatorKindInlineAsm(asm, targets, on_unwind)
    if __tag == 6:
        _0 = abort_kind_of_postcard(ctx, st)
        return TerminatorKindAbort(_0)
    if __tag == 7:
        return TerminatorKindReturn()
    if __tag == 8:
        return TerminatorKindUnwindResume()
    raise unknown_variant("TerminatorKind", __tag)

def trait_assoc_const_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitAssocConst:
    name = trait_item_name_of_postcard(ctx, st)
    attr_info = attr_info_of_postcard(ctx, st)
    ty = ty_of_postcard(ctx, st)
    default = option_of_postcard(global_decl_ref_of_postcard)(ctx, st)
    return TraitAssocConst(name, attr_info, ty, default)

def trait_assoc_ty_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitAssocTy:
    name = trait_item_name_of_postcard(ctx, st)
    attr_info = attr_info_of_postcard(ctx, st)
    default = option_of_postcard(trait_assoc_ty_impl_of_postcard)(ctx, st)
    implied_clauses = index_vec_of_postcard(trait_clause_id_of_postcard, trait_param_of_postcard)(ctx, st)
    return TraitAssocTy(name, attr_info, default, implied_clauses)

def trait_assoc_ty_impl_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitAssocTyImpl:
    value = ty_of_postcard(ctx, st)
    implied_trait_refs = index_vec_of_postcard(trait_clause_id_of_postcard, trait_ref_of_postcard)(ctx, st)
    return TraitAssocTyImpl(value, implied_trait_refs)

def trait_clause_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitClauseId:
    return TraitClauseId(int_of_postcard(ctx, st))

def trait_decl_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitDecl:
    def_id = trait_decl_id_of_postcard(ctx, st)
    item_meta = item_meta_of_postcard(ctx, st)
    src = trait_decl_source_of_postcard(ctx, st)
    generics = generic_params_of_postcard(ctx, st)
    implied_clauses = index_vec_of_postcard(trait_clause_id_of_postcard, trait_param_of_postcard)(ctx, st)
    consts = indexed_map_of_postcard(assoc_const_id_of_postcard, trait_assoc_const_of_postcard)(ctx, st)
    types = indexed_map_of_postcard(assoc_type_id_of_postcard, binder_of_postcard(trait_assoc_ty_of_postcard))(ctx, st)
    methods = indexed_map_of_postcard(trait_method_id_of_postcard, binder_of_postcard(trait_method_of_postcard))(ctx, st)
    vtable = option_of_postcard(type_decl_ref_of_postcard)(ctx, st)
    return TraitDecl(def_id, item_meta, src, generics, implied_clauses, consts, types, methods, vtable)

def trait_decl_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitDeclId:
    return TraitDeclId(int_of_postcard(ctx, st))

def trait_decl_ref_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitDeclRef:
    id = trait_decl_id_of_postcard(ctx, st)
    generics = box_of_postcard(generic_args_of_postcard)(ctx, st)
    return TraitDeclRef(id, generics)

def trait_decl_source_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitDeclSource:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return TraitDeclSourceNormalTraitDecl()
    if __tag == 1:
        return TraitDeclSourceTraitAliasTraitDecl()
    raise unknown_variant("TraitDeclSource", __tag)

def trait_impl_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitImpl:
    def_id = trait_impl_id_of_postcard(ctx, st)
    item_meta = item_meta_of_postcard(ctx, st)
    src = trait_impl_source_of_postcard(ctx, st)
    impl_trait = trait_decl_ref_of_postcard(ctx, st)
    generics = generic_params_of_postcard(ctx, st)
    implied_trait_refs = index_vec_of_postcard(trait_clause_id_of_postcard, trait_ref_of_postcard)(ctx, st)
    consts = indexed_map_of_postcard(assoc_const_id_of_postcard, global_decl_ref_of_postcard)(ctx, st)
    types = indexed_map_of_postcard(assoc_type_id_of_postcard, binder_of_postcard(trait_assoc_ty_impl_of_postcard))(ctx, st)
    methods = indexed_map_of_postcard(trait_method_id_of_postcard, binder_of_postcard(fun_decl_ref_of_postcard))(ctx, st)
    vtable = option_of_postcard(global_decl_ref_of_postcard)(ctx, st)
    return TraitImpl(def_id, item_meta, src, impl_trait, generics, implied_trait_refs, consts, types, methods, vtable)

def trait_impl_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitImplId:
    return TraitImplId(int_of_postcard(ctx, st))

def trait_impl_ref_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitImplRef:
    id = trait_impl_id_of_postcard(ctx, st)
    generics = box_of_postcard(generic_args_of_postcard)(ctx, st)
    return TraitImplRef(id, generics)

def trait_impl_source_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitImplSource:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return TraitImplSourceNormalTraitImpl()
    if __tag == 1:
        return TraitImplSourceTraitAliasTraitImpl()
    if __tag == 2:
        kind = closure_kind_of_postcard(ctx, st)
        return TraitImplSourceClosureTraitImpl(kind)
    if __tag == 3:
        return TraitImplSourceDestructTraitImpl()
    raise unknown_variant("TraitImplSource", __tag)

def trait_item_name_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitItemName:
    return string_of_postcard(ctx, st)

def trait_method_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitMethod:
    name = trait_item_name_of_postcard(ctx, st)
    item_meta = item_meta_of_postcard(ctx, st)
    signature = fun_sig_of_postcard(ctx, st)
    default = option_of_postcard(fun_decl_ref_of_postcard)(ctx, st)
    return TraitMethod(name, item_meta, signature, default)

def trait_method_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitMethodId:
    return TraitMethodId(int_of_postcard(ctx, st))

def trait_param_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitParam:
    clause_id = trait_clause_id_of_postcard(ctx, st)
    span = option_of_postcard(span_of_postcard)(ctx, st)
    origin = predicate_origin_of_postcard(ctx, st)
    trait = region_binder_of_postcard(trait_decl_ref_of_postcard)(ctx, st)
    return TraitParam(clause_id, span, origin, trait)

def trait_ref_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitRef:
    return dedup_val_of_postcard(ctx.trait_ref_dedup, trait_ref_contents_of_postcard, ctx, st)

def trait_ref_contents_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitRefContents:
    kind = trait_ref_kind_of_postcard(ctx, st)
    trait_decl_ref = region_binder_of_postcard(trait_decl_ref_of_postcard)(ctx, st)
    return TraitRefContents(kind, trait_decl_ref)

def trait_ref_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitRefKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = trait_impl_ref_of_postcard(ctx, st)
        return TraitRefKindTraitImpl(_0)
    if __tag == 1:
        _0 = de_bruijn_var_of_postcard(trait_clause_id_of_postcard)(ctx, st)
        return TraitRefKindClause(_0)
    if __tag == 2:
        _0 = trait_ref_of_postcard(ctx, st)
        _1 = trait_clause_id_of_postcard(ctx, st)
        return TraitRefKindParentClause(_0, _1)
    if __tag == 3:
        _0 = trait_ref_of_postcard(ctx, st)
        _1 = assoc_type_id_of_postcard(ctx, st)
        _2 = trait_clause_id_of_postcard(ctx, st)
        return TraitRefKindItemClause(_0, _1, _2)
    if __tag == 4:
        return TraitRefKindSelf()
    if __tag == 5:
        builtin_data = builtin_impl_data_of_postcard(ctx, st)
        parent_trait_refs = index_vec_of_postcard(trait_clause_id_of_postcard, trait_ref_of_postcard)(ctx, st)
        types = indexed_map_of_postcard(assoc_type_id_of_postcard, trait_assoc_ty_impl_of_postcard)(ctx, st)
        vtable = option_of_postcard(global_decl_ref_of_postcard)(ctx, st)
        return TraitRefKindBuiltinOrAuto(builtin_data, parent_trait_refs, types, vtable)
    if __tag == 6:
        return TraitRefKindDyn()
    if __tag == 7:
        _0 = string_of_postcard(ctx, st)
        return TraitRefKindUnknownTrait(_0)
    raise unknown_variant("TraitRefKind", __tag)

def trait_type_constraint_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitTypeConstraint:
    trait_ref = trait_ref_of_postcard(ctx, st)
    type_id = assoc_type_id_of_postcard(ctx, st)
    ty = ty_of_postcard(ctx, st)
    return TraitTypeConstraint(trait_ref, type_id, ty)

def trait_type_constraint_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TraitTypeConstraintId:
    return TraitTypeConstraintId(int_of_postcard(ctx, st))

def translated_crate_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TranslatedCrate:
    crate_name = string_of_postcard(ctx, st)
    options = cli_options_of_postcard(ctx, st)
    target_information = index_map_of_postcard(string_of_postcard, target_info_of_postcard, int_of_postcard)(ctx, st)
    files = index_vec_of_postcard(file_id_of_postcard, file_of_postcard)(ctx, st)
    item_names = index_map_of_postcard(item_id_of_postcard, name_of_postcard, int_of_postcard)(ctx, st)
    assoc_item_names = indexed_map_of_postcard(trait_decl_id_of_postcard, assoc_item_names_of_postcard)(ctx, st)
    short_names = index_map_of_postcard(item_id_of_postcard, name_of_postcard, int_of_postcard)(ctx, st)
    type_decls = indexed_map_of_postcard(type_decl_id_of_postcard, type_decl_of_postcard)(ctx, st)
    fun_decls = indexed_map_of_postcard(fun_decl_id_of_postcard, fun_decl_of_postcard)(ctx, st)
    global_decls = indexed_map_of_postcard(global_decl_id_of_postcard, global_decl_of_postcard)(ctx, st)
    trait_decls = indexed_map_of_postcard(trait_decl_id_of_postcard, trait_decl_of_postcard)(ctx, st)
    trait_impls = indexed_map_of_postcard(trait_impl_id_of_postcard, trait_impl_of_postcard)(ctx, st)
    ordered_decls = option_of_postcard(list_of_postcard(declaration_group_of_postcard))(ctx, st)
    return TranslatedCrate(crate_name, options, target_information, files, item_names, assoc_item_names, short_names, type_decls, fun_decls, global_decls, trait_decls, trait_impls, ordered_decls)

def ty_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Ty:
    return dedup_val_of_postcard(ctx.ty_dedup, ty_kind_of_postcard, ctx, st)

def ty_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TyKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = scalar_type_of_postcard(ctx, st)
        return TyKindTScalar(_0)
    if __tag == 1:
        _0 = ty_of_postcard(ctx, st)
        _1 = constant_expr_of_postcard(ctx, st)
        _2 = option_of_postcard(trait_ref_of_postcard)(ctx, st)
        return TyKindTArray(_0, _1, _2)
    if __tag == 2:
        _0 = ty_of_postcard(ctx, st)
        _1 = option_of_postcard(trait_ref_of_postcard)(ctx, st)
        return TyKindTSlice(_0, _1)
    if __tag == 3:
        _0 = type_decl_ref_of_postcard(ctx, st)
        return TyKindTAdt(_0)
    if __tag == 4:
        _0 = region_of_postcard(ctx, st)
        _1 = ty_of_postcard(ctx, st)
        _2 = ref_kind_of_postcard(ctx, st)
        return TyKindTRef(_0, _1, _2)
    if __tag == 5:
        _0 = ty_of_postcard(ctx, st)
        _1 = ref_kind_of_postcard(ctx, st)
        return TyKindTRawPtr(_0, _1)
    if __tag == 6:
        _0 = region_binder_of_postcard(fn_ptr_of_postcard)(ctx, st)
        return TyKindTFnDef(_0)
    if __tag == 7:
        _0 = region_binder_of_postcard(fun_sig_of_postcard)(ctx, st)
        return TyKindTFnPtr(_0)
    if __tag == 8:
        _0 = dyn_predicate_of_postcard(ctx, st)
        return TyKindTDynTrait(_0)
    if __tag == 9:
        _0 = ty_of_postcard(ctx, st)
        _1 = type_pattern_of_postcard(ctx, st)
        return TyKindTPattern(_0, _1)
    if __tag == 10:
        return TyKindTNever()
    if __tag == 11:
        _0 = de_bruijn_var_of_postcard(type_var_id_of_postcard)(ctx, st)
        return TyKindTVar(_0)
    if __tag == 12:
        _0 = trait_ref_of_postcard(ctx, st)
        _1 = assoc_type_id_of_postcard(ctx, st)
        _2 = generic_args_of_postcard(ctx, st)
        return TyKindTTraitType(_0, _1, _2)
    if __tag == 13:
        _0 = ty_of_postcard(ctx, st)
        return TyKindTPtrMetadata(_0)
    if __tag == 14:
        _0 = string_of_postcard(ctx, st)
        return TyKindTError(_0)
    raise unknown_variant("TyKind", __tag)

def type_decl_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TypeDecl:
    def_id = type_decl_id_of_postcard(ctx, st)
    item_meta = item_meta_of_postcard(ctx, st)
    generics = generic_params_of_postcard(ctx, st)
    src = type_source_of_postcard(ctx, st)
    kind = type_decl_kind_of_postcard(ctx, st)
    layout = index_map_of_postcard(string_of_postcard, layout_of_postcard, int_of_postcard)(ctx, st)
    ptr_metadata = ptr_metadata_of_postcard(ctx, st)
    return TypeDecl(def_id, item_meta, generics, src, kind, layout, ptr_metadata)

def type_decl_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TypeDeclId:
    return TypeDeclId(int_of_postcard(ctx, st))

def type_decl_kind_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TypeDeclKind:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = index_vec_of_postcard(field_id_of_postcard, field_of_postcard)(ctx, st)
        return TypeDeclKindStruct(_0)
    if __tag == 1:
        _0 = index_vec_of_postcard(variant_id_of_postcard, variant_of_postcard)(ctx, st)
        return TypeDeclKindEnum(_0)
    if __tag == 2:
        _0 = index_vec_of_postcard(field_id_of_postcard, field_of_postcard)(ctx, st)
        return TypeDeclKindUnion(_0)
    if __tag == 3:
        return TypeDeclKindOpaque()
    if __tag == 4:
        _0 = ty_of_postcard(ctx, st)
        return TypeDeclKindAlias(_0)
    if __tag == 5:
        _0 = string_of_postcard(ctx, st)
        return TypeDeclKindTDeclError(_0)
    raise unknown_variant("TypeDeclKind", __tag)

def type_decl_ref_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TypeDeclRef:
    id = type_decl_id_of_postcard(ctx, st)
    generics = box_of_postcard(generic_args_of_postcard)(ctx, st)
    builtin = option_of_postcard(builtin_adt_of_postcard)(ctx, st)
    return TypeDeclRef(id, generics, builtin)

def type_param_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TypeParam:
    index = type_var_id_of_postcard(ctx, st)
    name = string_of_postcard(ctx, st)
    variance = variance_of_postcard(ctx, st)
    return TypeParam(index, name, variance)

def type_pattern_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TypePattern:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = constant_expr_of_postcard(ctx, st)
        _1 = constant_expr_of_postcard(ctx, st)
        return TypePatternRange(_0, _1)
    if __tag == 1:
        _0 = list_of_postcard(type_pattern_of_postcard)(ctx, st)
        return TypePatternOrPattern(_0)
    if __tag == 2:
        return TypePatternNotNull()
    raise unknown_variant("TypePattern", __tag)

def type_source_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TypeSource:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return TypeSourceNormalType()
    if __tag == 1:
        info = closure_info_of_postcard(ctx, st)
        return TypeSourceClosureType(info)
    if __tag == 2:
        dyn_predicate = dyn_predicate_of_postcard(ctx, st)
        field_map = index_vec_of_postcard(field_id_of_postcard, v_table_field_of_postcard)(ctx, st)
        supertrait_map = index_vec_of_postcard(trait_clause_id_of_postcard, option_of_postcard(field_id_of_postcard))(ctx, st)
        return TypeSourceVTableType(dyn_predicate, field_map, supertrait_map)
    if __tag == 3:
        _0 = builtin_adt_of_postcard(ctx, st)
        return TypeSourceBuiltinType(_0)
    raise unknown_variant("TypeSource", __tag)

def type_var_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> TypeVarId:
    return TypeVarId(int_of_postcard(ctx, st))

def u_int_ty_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> UIntTy:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return UIntTyUsize()
    if __tag == 1:
        return UIntTyU8()
    if __tag == 2:
        return UIntTyU16()
    if __tag == 3:
        return UIntTyU32()
    if __tag == 4:
        return UIntTyU64()
    if __tag == 5:
        return UIntTyU128()
    raise unknown_variant("UIntTy", __tag)

def unop_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Unop:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return UnopNot()
    if __tag == 1:
        _0 = overflow_mode_of_postcard(ctx, st)
        return UnopNeg(_0)
    if __tag == 2:
        _0 = cast_kind_of_postcard(ctx, st)
        return UnopCast(_0)
    raise unknown_variant("Unop", __tag)

def unsizing_metadata_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> UnsizingMetadata:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        _0 = constant_expr_of_postcard(ctx, st)
        return UnsizingMetadataMetaLength(_0)
    if __tag == 1:
        _0 = trait_ref_of_postcard(ctx, st)
        _1 = constant_expr_of_postcard(ctx, st)
        return UnsizingMetadataMetaVTable(_0, _1)
    if __tag == 2:
        _0 = list_of_postcard(field_id_of_postcard)(ctx, st)
        return UnsizingMetadataMetaVTableUpcast(_0)
    if __tag == 3:
        return UnsizingMetadataMetaUnknown()
    raise unknown_variant("UnsizingMetadata", __tag)

def v_table_field_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> VTableField:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return VTableFieldVTableSize()
    if __tag == 1:
        return VTableFieldVTableAlign()
    if __tag == 2:
        return VTableFieldVTableDrop()
    if __tag == 3:
        _0 = trait_method_id_of_postcard(ctx, st)
        return VTableFieldVTableMethod(_0)
    if __tag == 4:
        _0 = trait_clause_id_of_postcard(ctx, st)
        return VTableFieldVTableSuperTrait(_0)
    raise unknown_variant("VTableField", __tag)

def variance_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Variance:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return VarianceCovariant()
    if __tag == 1:
        return VarianceInvariant()
    if __tag == 2:
        return VarianceContravariant()
    if __tag == 3:
        return VarianceBivariant()
    if __tag == 4:
        return VarianceVaUnknown()
    raise unknown_variant("Variance", __tag)

def variant_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> Variant:
    id = variant_id_of_postcard(ctx, st)
    span = span_of_postcard(ctx, st)
    attr_info = attr_info_of_postcard(ctx, st)
    variant_name = string_of_postcard(ctx, st)
    fields = index_vec_of_postcard(field_id_of_postcard, field_of_postcard)(ctx, st)
    discriminant = integer_value_of_postcard(ctx, st)
    return Variant(id, span, attr_info, variant_name, fields, discriminant)

def variant_id_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> VariantId:
    return VariantId(int_of_postcard(ctx, st))

def variant_layout_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> VariantLayout:
    field_offsets = index_vec_of_postcard(field_id_of_postcard, offset_expr_of_postcard)(ctx, st)
    uninhabited = bool_of_postcard(ctx, st)
    tagger = list_of_postcard(pair_of_postcard(u64_of_postcard, integer_value_of_postcard))(ctx, st)
    return VariantLayout(field_offsets, uninhabited, tagger)

def with_retag_of_postcard(ctx: OfPostcardCtx, st: PostcardReader) -> WithRetag:
    __tag = int_of_postcard(ctx, st)
    if __tag == 0:
        return WithRetagNoRetag()
    if __tag == 1:
        return WithRetagYesRetag()
    raise unknown_variant("WithRetag", __tag)



def crate_of_postcard(contents: bytes) -> TranslatedCrate:
    """Read a crate from the bytes of a postcard-serialized file."""
    st = PostcardReader(contents)
    version = string_of_postcard(None, st)
    if version != SUPPORTED_CHARON_VERSION:
        raise DeserializeError(
            "Incompatible version of charon: this program supports llbc emitted by charon "
            f"v{SUPPORTED_CHARON_VERSION} but attempted to read a file emitted by charon "
            f"v{version}."
        )
    ctx = OfPostcardCtx()
    crate = translated_crate_of_postcard(ctx, st)
    bool_of_postcard(ctx, st)  # whether the translation had errors
    ensure_eof(st)
    return crate


def crate_of_postcard_file(path: str | os.PathLike[str]) -> TranslatedCrate:
    """Read a crate from a postcard-serialized `.llbc.postcard`/`.ullbc.postcard` file."""
    with open(path, "rb") as file:
        contents = file.read()
    hint = format_hint(contents)
    if hint is InputFormat.JSON:
        raise DeserializeError(
            f"This file looks like JSON, but Postcard deserialization was requested: {path}. "
            "Please use JSON deserialization or regenerate as Postcard."
        )
    if hint is InputFormat.EMPTY:
        raise DeserializeError(f"Input file is empty: {path}")
    return crate_of_postcard(contents)
