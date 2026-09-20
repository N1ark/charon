use charon_lib::ast::*;
use indoc::indoc;
use itertools::Itertools;

use super::deserialize::{Deserializer, Format};
use super::util::*;
use crate::codegen::*;

pub static FORMAT: Format = Format {
    suffix: "of_json",
    ctx_ty: "OfJsonCtx",
    input: "js",
    input_ty: "Json",
    decoder_ty: "JsonDecoder",
    scalar_fn,
    manual_impls: MANUAL_IMPLS,
};

fn scalar_fn(scalar: ScalarTy) -> &'static str {
    match scalar {
        ScalarTy::Bool => "bool_of_json",
        ScalarTy::Char => "char_of_json",
        // 128-bit integers are serialized as strings, as json numbers can't hold them.
        ScalarTy::Integer(IntegerTy::Signed(IntTy::I128) | IntegerTy::Unsigned(UIntTy::U128)) => {
            "big_int_of_json"
        }
        ScalarTy::Integer(_) => "int_of_json",
        ScalarTy::Float(_) => "float_of_json",
    }
}

const MANUAL_IMPLS: &[(&str, &str)] = &[
    // Hand-written because we interpret it as a list.
    (
        "charon_lib::ids::index_vec::IndexVec",
        "return list_of_json(arg1_of_json)(ctx, js)",
    ),
    // Hand-written because we interpret it as a list.
    (
        "charon_lib::ids::index_map::IndexMap",
        indoc!(
            r#"
            __entries = list_of_json(option_of_json(arg1_of_json))(ctx, js)
            return [__entry for __entry in __entries if __entry is not None]
            "#
        ),
    ),
    // Hand-written because we turn it into a list of pairs.
    (
        "indexmap::map::IndexMap",
        "return list_of_json(key_value_pair_of_json(arg0_of_json, arg1_of_json))(ctx, js)",
    ),
    // Hand-written because we replace the `FileId` with the corresponding file.
    (
        "FileId",
        indoc!(
            r#"
            __file_id = int_of_json(ctx, js)
            try:
                return ctx.files[__file_id]
            except KeyError:
                raise DeserializeError(f"unknown file id: {__file_id}") from None
            "#
        ),
    ),
    (
        "File",
        indoc!(
            r#"
            __fields = expect_object(js)
            __file_id = int_of_json(ctx, __fields["id"])
            __file = File(
                name=file_name_of_json(ctx, __fields["name"]),
                crate_name=string_of_json(ctx, __fields["crate_name"]),
                contents=option_of_json(string_of_json)(ctx, __fields["contents"]),
            )
            ctx.files[__file_id] = __file
            return __file
            "#
        ),
    ),
    (
        "HashConsed",
        "raise DeserializeError(\"use `dedup_val_of_json` instead\")",
    ),
    (
        "Ty",
        "return dedup_val_of_json(ctx.ty_dedup, ty_kind_of_json, ctx, js)",
    ),
    (
        "TraitRef",
        "return dedup_val_of_json(ctx.trait_ref_dedup, trait_ref_contents_of_json, ctx, js)",
    ),
    (
        "ConstantExpr",
        indoc!(
            r#"
            def read_contents(ctx: OfJsonCtx, js: Json) -> ConstantExpr:
                kind, ty = pair_of_json(constant_expr_kind_of_json, ty_of_json)(ctx, js)
                return ConstantExpr(kind=kind, ty=ty)

            return dedup_val_of_json(ctx.constant_expr_dedup, read_contents, ctx, js)
            "#
        ),
    ),
    (
        "ExactSizeExpr",
        "return dedup_val_of_json(ctx.exact_size_expr_dedup, exact_size_expr_kind_of_json, ctx, js)",
    ),
    // Hand-written because spans are deduplicated in the serialized output.
    (
        "Span",
        indoc!(
            r#"
            def read_contents(ctx: OfJsonCtx, js: Json) -> Span:
                __fields = expect_object(js)
                return Span(
                    data=span_data_of_json(ctx, __fields["data"]),
                    generated_from_span=option_of_json(span_data_of_json)(
                        ctx, __fields["generated_from_span"]
                    ),
                )

            return dedup_val_of_json(ctx.span_dedup, read_contents, ctx, js)
            "#
        ),
    ),
];

/// Reads each field out of the json value that holds it, and returns the names they were bound to.
fn read_fields(
    ds: &Deserializer<'_, '_>,
    fields: &IndexVec<FieldId, Field>,
    source: impl Fn(usize, &Field) -> String,
) -> (String, Vec<String>) {
    let mut lines = Vec::new();
    let mut names = Vec::new();
    for (i, field) in fields.iter().enumerate() {
        if field.is_opaque() {
            continue;
        }
        let name = make_py_ident(field.renamed_name());
        lines.push(ds.bind(&name, &field.ty, &source(i, field)));
        names.push(name);
    }
    (lines.join("\n"), names)
}

/// Reads a value built out of several fields: a struct, or the payload of an enum variant.
fn read_construct(
    ds: &Deserializer<'_, '_>,
    class: &str,
    fields: &IndexVec<FieldId, Field>,
    value: &str,
) -> String {
    if fields.is_empty() {
        return format!("return {class}()");
    }
    let positional = fields.iter().all(|field| field.is_positional);
    let (reads, names) = if !positional {
        // A struct or a struct variant: the fields are keyed by name.
        let prelude = format!("__fields = expect_object({value})");
        let (reads, names) = read_fields(ds, fields, |_, f| format!("__fields[{:?}]", f.name));
        (format!("{prelude}\n{reads}"), names)
    } else if fields.len() == 1 {
        // A single positional field is serialized as the field itself.
        read_fields(ds, fields, |_, _| value.to_string())
    } else {
        let prelude = format!("__items = expect_list({value}, {})", fields.len());
        let (reads, names) = read_fields(ds, fields, |i, _| format!("__items[{i}]"));
        (format!("{prelude}\n{reads}"), names)
    };
    format!("{reads}\nreturn {class}({})", names.into_iter().join(", "))
}

fn body(ds: &Deserializer<'_, '_>, decl: &TypeDecl) -> String {
    if let Some(def) = ds.manual_impl(decl) {
        return def.trim_end().to_string();
    }
    let class = ds.ctx.type_to_py_class(decl);
    match type_shape(decl) {
        TypeShape::Unit => "expect_null(js)\nreturn None".to_string(),
        TypeShape::Index(_) => format!("return {class}(int_of_json(ctx, js))"),
        TypeShape::Transparent(ty) => {
            let call = ds.call(ty);
            format!("return {call}(ctx, js)")
        }
        TypeShape::Tuple(fields) | TypeShape::Record(fields) => {
            read_construct(ds, &class, fields, "js")
        }
        TypeShape::Enum(variants) => {
            let branches = variants
                .iter()
                .filter(|v| !v.is_opaque())
                .map(|variant| {
                    let variant_class = ds.ctx.variant_to_py_class(decl, variant);
                    let read = read_construct(ds, &variant_class, &variant.fields, "__payload");
                    format!("if __tag == {:?}:\n{}", variant.name, indent(&read, 1))
                })
                .join("\n");
            format!(
                "__tag, __payload = split_variant(js)\n{branches}\nraise unknown_variant({class:?}, __tag)"
            )
        }
    }
}

pub fn generate(ctx: &GenerateCtx<'_>, tys: Vec<&TypeDecl>) -> String {
    Deserializer::new(ctx, &FORMAT).generate(tys, body)
}
