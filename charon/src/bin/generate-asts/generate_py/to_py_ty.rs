//! Generate the python declaration of each AST type.
//!
//! Structs become dataclasses and enums become one dataclass per variant plus a union alias, which
//! is the idiomatic way to write a tagged union that a type checker understands.

use charon_lib::ast::*;
use itertools::Itertools;

use super::util::*;
use crate::codegen::*;

const MANUAL_IMPLS: &[(&str, &str)] = &[
    // Hand-written because we replace the `FileId` with the corresponding file.
    ("FileId", "FileId: TypeAlias = \"File\""),
    // Keep the public python representation independent from rust's hash-consing wrapper.
    (
        "ConstantExpr",
        "@dataclass\nclass ConstantExpr:\n    kind: ConstantExprKind\n    ty: Ty",
    ),
    (
        "HashConsed",
        "# `HashConsed` is transparent on the python side; it has no declaration of its own.",
    ),
];

/// Turn rust doc comments into a python docstring.
fn docstring(attr_info: &AttrInfo, level: usize) -> String {
    let comment = attr_info
        .attributes
        .iter()
        .filter_map(|a| a.as_doc_comment())
        .join("\n");
    if comment.is_empty() {
        return String::new();
    }
    // We emit raw strings, so the text must neither close the docstring nor end with a backslash.
    let comment = comment.replace("\"\"\"", "'''");
    let comment = comment.trim_end_matches('\\').trim();
    let comment = comment
        .lines()
        .map(|line| line.strip_prefix(' ').unwrap_or(line))
        .join("\n");
    format!("{}\n", indent(&format!("r\"\"\"{comment}\"\"\""), level))
}

/// A comment describing a type alias, which can't carry a docstring.
fn alias_comment(attr_info: &AttrInfo) -> String {
    attr_info
        .attributes
        .iter()
        .filter_map(|a| a.as_doc_comment())
        .flat_map(|comment| {
            comment
                .lines()
                .map(|line| format!("# {}\n", line.trim()))
                .collect_vec()
        })
        .join("")
}

/// The `(Generic[T0, T1])` clause of a class that mirrors a generic rust type.
fn generic_clause(decl: &TypeDecl) -> String {
    match decl.generics.types.len() {
        0 => String::new(),
        n => format!("(Generic[{}])", (0..n).map(|i| format!("T{i}")).join(", ")),
    }
}

impl<'a> GenerateCtx<'a> {
    /// A dataclass with one attribute per field. Opaque fields are skipped, as they are not
    /// serialized.
    fn py_dataclass(
        &self,
        name: &str,
        generics: &str,
        doc: String,
        fields: &IndexVec<FieldId, Field>,
    ) -> String {
        let attributes = fields
            .iter()
            .filter(|f| !f.is_opaque())
            .map(|f| {
                let field_name = make_py_ident(f.renamed_name());
                let ty = self.type_to_py_name(&f.ty);
                let doc = docstring(&f.attr_info, 1);
                format!("    {field_name}: {ty}\n{doc}")
            })
            .join("");
        let body = if doc.is_empty() && attributes.is_empty() {
            "    pass\n".to_string()
        } else {
            format!("{doc}{attributes}")
        };
        format!("@dataclass\nclass {name}{generics}:\n{body}")
    }

    fn type_decl_to_py(&self, decl: &TypeDecl) -> String {
        let name = self.type_to_py_class(decl);
        let generics = generic_clause(decl);
        let doc = docstring(&decl.item_meta.attr_info, 1);
        match type_shape(decl) {
            // An empty struct carries nothing, so it is represented by `None`.
            TypeShape::Unit => {
                format!(
                    "{}{name}: TypeAlias = \"None\"\n",
                    alias_comment(&decl.item_meta.attr_info)
                )
            }
            // A distinct type for a plain integer, which costs nothing at runtime.
            TypeShape::Index(_) => format!("{name} = NewType(\"{name}\", int)\n"),
            TypeShape::Transparent(ty) => {
                let ty = self.type_to_py_name(ty);
                format!(
                    "{}{name}: TypeAlias = \"{ty}\"\n",
                    alias_comment(&decl.item_meta.attr_info)
                )
            }
            // Tuple structs keep their positional field names (`_0`, `_1`, ...).
            TypeShape::Tuple(fields) | TypeShape::Record(fields) => {
                self.py_dataclass(&name, &generics, doc, fields)
            }
            TypeShape::Enum(variants) => {
                let variants = variants.iter().filter(|v| !v.is_opaque()).collect_vec();
                let classes = variants
                    .iter()
                    .map(|variant| {
                        let variant_name = self.variant_to_py_class(decl, variant);
                        let doc = docstring(&variant.attr_info, 1);
                        self.py_dataclass(&variant_name, &generics, doc, &variant.fields)
                    })
                    .join("\n");
                let args = match decl.generics.types.len() {
                    0 => String::new(),
                    n => format!("[{}]", (0..n).map(|i| format!("T{i}")).join(", ")),
                };
                let union = match variants.as_slice() {
                    // An enum with no visible variant has no value at all.
                    [] => "NoReturn".to_string(),
                    [variant] => format!("{}{args}", self.variant_to_py_class(decl, variant)),
                    variants => format!(
                        "Union[{}]",
                        variants
                            .iter()
                            .map(|v| format!("{}{args}", self.variant_to_py_class(decl, v)))
                            .join(", ")
                    ),
                };
                format!(
                    "{classes}\n{}{name}: TypeAlias = \"{union}\"\n",
                    alias_comment(&decl.item_meta.attr_info)
                )
            }
        }
    }

    pub fn type_decls_to_py(&self, tys: Vec<&TypeDecl>) -> String {
        let manual_impls = self.names_to_type_id_map(MANUAL_IMPLS);
        tys.into_iter()
            .map(|decl| match manual_impls.get(&decl.def_id) {
                Some(def) => format!("{def}\n"),
                None => self.type_decl_to_py(decl),
            })
            .join("\n\n")
    }
}
