use charon_lib::ast::*;
use indoc::indoc;
use itertools::Itertools;

use super::deserialize::{Deserializer, Format};
use super::util::*;
use crate::codegen::*;

pub static FORMAT: Format = Format {
    suffix: "of_postcard",
    ctx_ty: "OfPostcardCtx",
    input: "st",
    input_ty: "PostcardReader",
    decoder_ty: "PostcardDecoder",
    scalar_fn,
    manual_impls: MANUAL_IMPLS,
};

fn scalar_fn(scalar: ScalarTy) -> &'static str {
    match scalar {
        ScalarTy::Bool => "bool_of_postcard",
        ScalarTy::Char => "char_of_postcard",
        ScalarTy::Integer(IntegerTy::Signed(int_ty)) => match int_ty {
            IntTy::Isize => "isize_of_postcard",
            IntTy::I8 => "i8_of_postcard",
            IntTy::I16 => "i16_of_postcard",
            IntTy::I32 => "i32_of_postcard",
            IntTy::I64 => "i64_of_postcard",
            IntTy::I128 => "big_int_of_postcard",
        },
        ScalarTy::Integer(IntegerTy::Unsigned(uint_ty)) => match uint_ty {
            UIntTy::Usize => "usize_of_postcard",
            UIntTy::U8 => "u8_of_postcard",
            UIntTy::U16 => "u16_of_postcard",
            UIntTy::U32 => "u32_of_postcard",
            UIntTy::U64 => "u64_of_postcard",
            UIntTy::U128 => "big_uint_of_postcard",
        },
        ScalarTy::Float(FloatTy::F32) => "f32_of_postcard",
        ScalarTy::Float(_) => "float_of_postcard",
    }
}

const MANUAL_IMPLS: &[(&str, &str)] = &[
    (
        "charon_lib::ids::index_vec::IndexVec",
        "return list_of_postcard(arg1_of_postcard)(ctx, st)",
    ),
    (
        "charon_lib::ids::index_map::IndexMap",
        indoc!(
            r#"
            __entries = list_of_postcard(option_of_postcard(arg1_of_postcard))(ctx, st)
            return [__entry for __entry in __entries if __entry is not None]
            "#
        ),
    ),
    (
        "indexmap::map::IndexMap",
        "return list_of_postcard(key_value_pair_of_postcard(arg0_of_postcard, arg1_of_postcard))(ctx, st)",
    ),
    (
        "FileId",
        indoc!(
            r#"
            __file_id = int_of_postcard(ctx, st)
            try:
                return ctx.files[__file_id]
            except KeyError:
                raise DeserializeError(
                    f"unknown file id: {__file_id}. valid ids are: {sorted(ctx.files)}"
                ) from None
            "#
        ),
    ),
    (
        "File",
        indoc!(
            r#"
            __file_id = int_of_postcard(ctx, st)
            __file = File(
                name=file_name_of_postcard(ctx, st),
                crate_name=string_of_postcard(ctx, st),
                contents=option_of_postcard(string_of_postcard)(ctx, st),
            )
            ctx.files[__file_id] = __file
            return __file
            "#
        ),
    ),
    (
        "HashConsed",
        "raise DeserializeError(\"use `dedup_val_of_postcard` instead\")",
    ),
    (
        "Ty",
        "return dedup_val_of_postcard(ctx.ty_dedup, ty_kind_of_postcard, ctx, st)",
    ),
    (
        "TraitRef",
        "return dedup_val_of_postcard(ctx.trait_ref_dedup, trait_ref_contents_of_postcard, ctx, st)",
    ),
    (
        "ConstantExpr",
        indoc!(
            r#"
            def read_contents(ctx: OfPostcardCtx, st: PostcardReader) -> ConstantExpr:
                kind, ty = pair_of_postcard(constant_expr_kind_of_postcard, ty_of_postcard)(ctx, st)
                return ConstantExpr(kind=kind, ty=ty)

            return dedup_val_of_postcard(ctx.constant_expr_dedup, read_contents, ctx, st)
            "#
        ),
    ),
    (
        "ExactSizeExpr",
        indoc!(
            r#"
            return dedup_val_of_postcard(
                ctx.exact_size_expr_dedup, exact_size_expr_kind_of_postcard, ctx, st
            )
            "#
        ),
    ),
    // Hand-written because spans are deduplicated in the serialized output.
    (
        "Span",
        indoc!(
            r#"
            def read_contents(ctx: OfPostcardCtx, st: PostcardReader) -> Span:
                data = span_data_of_postcard(ctx, st)
                generated_from_span = option_of_postcard(span_data_of_postcard)(ctx, st)
                return Span(data=data, generated_from_span=generated_from_span)

            return dedup_val_of_postcard(ctx.span_dedup, read_contents, ctx, st)
            "#
        ),
    ),
];

/// Postcard is a sequential format: fields are read one after the other, straight from the reader.
/// Opaque fields are still part of the input, so we read and discard them.
fn read_construct(
    ds: &Deserializer<'_, '_>,
    class: &str,
    fields: &IndexVec<FieldId, Field>,
) -> String {
    let mut lines = Vec::new();
    let mut names = Vec::new();
    for field in fields.iter() {
        let name = if field.is_opaque() {
            "_".to_string()
        } else {
            make_py_ident(field.renamed_name())
        };
        lines.push(ds.bind(&name, &field.ty, "st"));
        if !field.is_opaque() {
            names.push(name);
        }
    }
    lines.push(format!("return {class}({})", names.into_iter().join(", ")));
    lines.join("\n")
}

fn body(ds: &Deserializer<'_, '_>, decl: &TypeDecl) -> String {
    if let Some(def) = ds.manual_impl(decl) {
        return def.trim_end().to_string();
    }
    let class = ds.ctx.type_to_py_class(decl);
    match type_shape(decl) {
        TypeShape::Unit => "return None".to_string(),
        TypeShape::Index(_) => format!("return {class}(int_of_postcard(ctx, st))"),
        TypeShape::Transparent(ty) => {
            let call = ds.call(ty);
            format!("return {call}(ctx, st)")
        }
        TypeShape::Tuple(fields) | TypeShape::Record(fields) => read_construct(ds, &class, fields),
        TypeShape::Enum(variants) => {
            // Postcard identifies variants by their index, including the opaque ones.
            let branches = variants
                .iter()
                .enumerate()
                .filter(|(_, variant)| !variant.is_opaque())
                .map(|(i, variant)| {
                    let variant_class = ds.ctx.variant_to_py_class(decl, variant);
                    let read = read_construct(ds, &variant_class, &variant.fields);
                    format!("if __tag == {i}:\n{}", indent(&read, 1))
                })
                .join("\n");
            format!(
                "__tag = int_of_postcard(ctx, st)\n{branches}\nraise unknown_variant({class:?}, __tag)"
            )
        }
    }
}

pub fn generate(ctx: &GenerateCtx<'_>, tys: Vec<&TypeDecl>) -> String {
    Deserializer::new(ctx, &FORMAT).generate(tys, body)
}
