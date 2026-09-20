use charon_lib::ast::*;
use indoc::indoc;
use itertools::Itertools;

use super::deserialize::{Deserializer, Format};
use super::util::*;
use crate::codegen::*;

pub static FORMAT: Format = Format {
    suffix: "of_json",
    ctx_ty: "of_json_ctx",
    input: "js",
    input_ty: "json",
    value: "json",
    scalar_fn,
    manual_impls: MANUAL_IMPLS,
};

fn scalar_fn(scalar: ScalarTy) -> &'static str {
    match scalar {
        ScalarTy::Bool => "bool_of_json",
        ScalarTy::Char => "char_of_json",
        // Even though OCaml ints are only 63 bits, only scalars with their 128 bits should be able
        // to become too large.
        ScalarTy::Integer(IntegerTy::Signed(IntTy::I128) | IntegerTy::Unsigned(UIntTy::U128)) => {
            "big_int_of_json"
        }
        ScalarTy::Integer(_) => "int_of_json",
        ScalarTy::Float(_) => "float_of_json",
    }
}

const MANUAL_IMPLS: &[(&str, &str)] = &[
    // Hand-written because we replace the `FileId` with the corresponding file name.
    (
        "FileId",
        indoc!(
            r#"
            let* file_id = FileId.id_of_json ctx json in
            let file = FileTbl.find ctx.id_to_file_map file_id in
            Ok file
            "#,
        ),
    ),
    (
        "File",
        indoc!(
            r#"
            (match json with
            | `Assoc
                [ ("id", id); ("name", name); ("crate_name", crate_name); ("contents", contents) ]
            ->
                let* id = FileId.id_of_json ctx id in
                let* name = file_name_of_json ctx name in
                let* crate_name = string_of_json ctx crate_name in
                let* contents = option_of_json string_of_json ctx contents in
                let file: file = { name; crate_name; contents } in
                FileTbl.add ctx.id_to_file_map id file;
                Ok file
            | _ -> Error "")
            "#
        ),
    ),
    // Hand-written because its contents are a pair that we present as a record.
    (
        "ConstantExpr",
        indoc!(
            r#"
            dedup_val_of_json ctx.constant_expr_dedup_tbl
              (fun ctx json ->
                let* contents = pair_of_json constant_expr_kind_of_json ty_of_json ctx json in
                let kind, ty = contents in
                Ok ({ kind; ty } : constant_expr))
              ctx json
            "#
        ),
    ),
    // Hand-written because spans are deduplicated in the serialized output.
    (
        "Span",
        indoc!(
            r#"
            dedup_val_of_json ctx.span_dedup_tbl
              (fun ctx json ->
                match json with
                | `Assoc [ ("data", data); ("generated_from_span", generated_from_span) ] ->
                    let* data = span_data_of_json ctx data in
                    let* generated_from_span =
                      option_of_json span_data_of_json ctx generated_from_span
                    in
                    Ok ({ data; generated_from_span } : span)
                | _ -> Error "")
              ctx json
            "#
        ),
    ),
];

/// Reads each field from the sub-json value that the pattern bound it to.
fn convert_vars<'b>(
    ds: &Deserializer<'_, '_>,
    fields: impl IntoIterator<Item = &'b Field>,
) -> String {
    fields
        .into_iter()
        .filter(|f| !f.is_opaque())
        .map(|f| {
            let name = make_ocaml_ident(&f.name);
            let rename = make_ocaml_ident(f.renamed_name());
            ds.bind(&rename, &f.ty, &name)
        })
        .join("\n")
}

fn build_branch<'b>(
    ds: &Deserializer<'_, '_>,
    pat: &str,
    fields: impl IntoIterator<Item = &'b Field>,
    construct: &str,
) -> String {
    let convert = convert_vars(ds, fields);
    format!("| {pat} -> {convert} Ok ({construct})")
}

/// A json deserializer is a match on the shape of the json value.
fn branches(ds: &Deserializer<'_, '_>, decl: &TypeDecl) -> String {
    if let Some(def) = ds.manual_impl(decl) {
        return format!("| json -> {def}");
    }
    match type_shape(decl) {
        TypeShape::Unit => build_branch(ds, "`Null", &[], "()"),
        TypeShape::Index(name) => format!("| x -> {name}.id_of_json ctx x"),
        TypeShape::Transparent(ty) => {
            let call = ds.call(ty);
            format!("| x -> {call} ctx x")
        }
        TypeShape::Tuple(fields) => {
            let pat: String = fields
                .iter()
                .map(|f| f.name.as_str())
                .map(make_ocaml_ident)
                .join(";");
            let pat = format!("`List [ {pat} ]");
            let construct = fields
                .iter()
                .map(Field::renamed_name)
                .map(make_ocaml_ident)
                .join(", ");
            let construct = format!("( {construct} )");
            build_branch(ds, &pat, fields, &construct)
        }
        TypeShape::Record(fields) => {
            let pat: String = fields
                .iter()
                .map(|f| {
                    let name = &f.name;
                    let var = if f.is_opaque() {
                        "_"
                    } else {
                        &make_ocaml_ident(name)
                    };
                    format!("(\"{name}\", {var});")
                })
                .join("\n");
            let pat = format!("`Assoc [ {pat} ]");
            let construct = fields
                .iter()
                .filter(|f| !f.is_opaque())
                .map(Field::renamed_name)
                .map(make_ocaml_ident)
                .join("; ");
            let return_ty = ds.return_ty(decl);
            let construct = format!("({{ {construct} }} : {return_ty})");
            build_branch(ds, &pat, fields, &construct)
        }
        TypeShape::Enum(variants) => variants
            .iter()
            .filter(|v| !v.is_opaque())
            .map(|variant| {
                let name = &variant.name;
                let rename = variant.renamed_name();
                if variant.fields.is_empty() {
                    // Unit variant
                    let pat = format!("`String \"{name}\"");
                    build_branch(ds, &pat, &variant.fields, rename)
                } else {
                    let fields = &variant.fields;
                    let inner_pat = if fields.iter().all(|field| field.is_positional) {
                        // Tuple variant
                        if fields.len() == 1 {
                            make_ocaml_ident(&fields[0].name)
                        } else {
                            let pat = fields.iter().map(|f| f.name.as_str()).join("; ");
                            format!("`List [ {pat} ]")
                        }
                    } else {
                        // Struct variant
                        let pat = fields
                            .iter()
                            .map(|f| {
                                let name = &f.name;
                                let var = if f.is_opaque() {
                                    "_"
                                } else {
                                    &make_ocaml_ident(name)
                                };
                                format!("(\"{name}\", {var});")
                            })
                            .join(" ");
                        format!("`Assoc [ {pat} ]")
                    };
                    let pat = format!("`Assoc [ (\"{name}\", {inner_pat}) ]");
                    let construct_fields = fields
                        .iter()
                        .map(|f| f.name.as_str())
                        .map(make_ocaml_ident)
                        .join(", ");
                    let construct = format!("{rename} ({construct_fields})");
                    build_branch(ds, &pat, fields, &construct)
                }
            })
            .join("\n"),
    }
}

pub fn generate(ctx: &GenerateCtx<'_>, tys: Vec<&TypeDecl>) -> String {
    Deserializer::new(ctx, &FORMAT).generate(tys, |ds, decl| {
        let branches = branches(ds, decl);
        format!("match js with{branches} | _ -> Error \"\"")
    })
}
