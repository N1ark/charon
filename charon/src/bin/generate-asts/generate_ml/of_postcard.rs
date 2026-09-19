use charon_lib::ast::*;
use indoc::indoc;
use itertools::Itertools;

use super::deserialize::{Deserializer, Format};
use super::util::*;
use crate::codegen::*;

pub static FORMAT: Format = Format {
    suffix: "of_postcard",
    ctx_ty: "of_postcard_ctx",
    input: "st",
    input_ty: "postcard_state",
    value: "st",
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
        "list_of_postcard arg1_of_postcard ctx st",
    ),
    (
        "charon_lib::ids::index_map::IndexMap",
        indoc!(
            r#"
            let* list = list_of_postcard (option_of_postcard arg1_of_postcard) ctx st in
            Ok (List.filter_map (fun x -> x) list)
            "#
        ),
    ),
    (
        "indexmap::map::IndexMap",
        "list_of_postcard (key_value_pair_of_postcard arg0_of_postcard arg1_of_postcard) ctx st",
    ),
    (
        "FileId",
        indoc!(
            r#"
            let* file_id = FileId.id_of_postcard ctx st in
            try Ok (FileTbl.find ctx.id_to_file_map file_id)
            with Not_found ->
              let valid_keys = FileTbl.fold (fun key _ acc -> FileId.to_string key :: acc) ctx.id_to_file_map [] in
              Error ("unknown file id: " ^ FileId.to_string file_id ^ ". valid ids are: " ^ String.concat ", " valid_keys)
            "#
        ),
    ),
    (
        "File",
        indoc!(
            r#"
            let* id = FileId.id_of_postcard ctx st in
            let* name = file_name_of_postcard ctx st in
            let* crate_name = string_of_postcard ctx st in
            let* contents = option_of_postcard string_of_postcard ctx st in
            let file: file = { name; crate_name; contents } in
            FileTbl.add ctx.id_to_file_map id file;
            Ok file
            "#
        ),
    ),
    (
        "HashConsed",
        r#"Error "use `dedup_val_of_postcard` instead""#,
    ),
    (
        "Ty",
        "dedup_val_of_postcard ctx.ty_dedup_tbl ty_kind_of_postcard ctx st",
    ),
    (
        "TraitRef",
        "dedup_val_of_postcard ctx.tref_dedup_tbl trait_ref_contents_of_postcard ctx st",
    ),
    (
        "ConstantExpr",
        indoc!(
            r#"
            dedup_val_of_postcard ctx.constant_expr_dedup_tbl
              (fun ctx st ->
                let* contents = pair_of_postcard constant_expr_kind_of_postcard ty_of_postcard ctx st in
                let kind, ty = contents in
                Ok ({ kind; ty } : constant_expr))
              ctx st
            "#
        ),
    ),
    (
        "ExactSizeExpr",
        "dedup_val_of_postcard ctx.exact_size_expr_dedup_tbl exact_size_expr_kind_of_postcard ctx st",
    ),
    // Hand-written because spans are deduplicated in the serialized output.
    (
        "Span",
        indoc!(
            r#"
            dedup_val_of_postcard ctx.span_dedup_tbl
              (fun ctx st ->
                let* data = span_data_of_postcard ctx st in
                let* generated_from_span = option_of_postcard span_data_of_postcard ctx st in
                Ok ({ data; generated_from_span } : span))
              ctx st
            "#
        ),
    ),
];

/// Postcard is a sequential format: fields are read one after the other, straight from the state.
fn convert_vars<'b>(
    ds: &Deserializer<'_, '_>,
    fields: impl IntoIterator<Item = &'b Field>,
) -> String {
    fields
        .into_iter()
        .map(|f| {
            let rename = if f.is_opaque() {
                "_".to_string()
            } else {
                make_ocaml_ident(f.renamed_name())
            };
            ds.bind(&rename, &f.ty, ds.format.input)
        })
        .join("\n")
}

fn body(ds: &Deserializer<'_, '_>, decl: &TypeDecl) -> String {
    if let Some(def) = ds.manual_impl(decl) {
        return def.to_string();
    }
    match type_shape(decl) {
        TypeShape::Unit => "Ok ()".to_string(),
        TypeShape::Index(name) => format!("{name}.id_of_postcard ctx st"),
        TypeShape::Transparent(ty) => {
            let call = ds.call(ty);
            format!("{call} ctx st")
        }
        TypeShape::Tuple(fields) => {
            let convert = convert_vars(ds, fields);
            let construct = fields
                .iter()
                .map(Field::renamed_name)
                .map(make_ocaml_ident)
                .join(", ");
            format!("{convert}\nOk ({construct})")
        }
        TypeShape::Record(fields) => {
            let convert = convert_vars(ds, fields);
            let construct = fields
                .iter()
                .filter(|f| !f.is_opaque())
                .map(Field::renamed_name)
                .map(make_ocaml_ident)
                .join("; ");
            let return_ty = ds.return_ty(decl);
            format!("{convert}\nOk (({{ {construct} }} : {return_ty}))")
        }
        TypeShape::Enum(variants) => {
            // Postcard identifies variants by their index, including the opaque ones.
            let branches = variants
                .iter()
                .enumerate()
                .filter(|(_, variant)| !variant.is_opaque())
                .map(|(i, variant)| {
                    let rename = variant.renamed_name();
                    if variant.fields.is_empty() {
                        format!("| {i} -> Ok {rename}")
                    } else {
                        let fields = &variant.fields;
                        let convert = convert_vars(ds, fields);
                        let construct_fields = fields
                            .iter()
                            .map(|f| f.name.as_str())
                            .map(make_ocaml_ident)
                            .join(", ");
                        let construct = format!("{rename} ({construct_fields})");
                        format!("| {i} -> {convert}\n  Ok ({construct})")
                    }
                })
                .join("\n");
            format!(
                "let* __tag = int_of_postcard ctx st in\nmatch __tag with\n{branches}\n| _ -> Error (\"unknown enum variant tag: \" ^ string_of_int __tag)"
            )
        }
    }
}

pub fn generate(ctx: &GenerateCtx<'_>, tys: Vec<&TypeDecl>) -> String {
    Deserializer::new(ctx, &FORMAT).generate(tys, body)
}
