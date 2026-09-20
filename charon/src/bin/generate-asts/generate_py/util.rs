use charon_lib::ast::*;
use convert_case::{Case, Casing};
use itertools::Itertools;

use crate::codegen::GenerateCtx;

/// Python keywords, plus the names we give to the generated functions' own parameters. A field or
/// local that would collide with one of those gets a trailing underscore.
const RESERVED: &[&str] = &[
    "and", "as", "assert", "async", "await", "break", "class", "continue", "ctx", "def", "del",
    "elif", "else", "except", "false", "finally", "for", "from", "global", "if", "import", "in",
    "is", "js", "lambda", "none", "nonlocal", "not", "or", "pass", "raise", "return", "st", "true",
    "try", "while", "with", "yield",
];

/// The python spelling of a rust field or variable name.
pub fn make_py_ident(name: &str) -> String {
    let leading_underscores = name.len() - name.trim_start_matches('_').len();
    let mut name = "_".repeat(leading_underscores) + &name.to_case(Case::Snake);
    if RESERVED.contains(&name.as_str()) {
        name += "_";
    }
    name
}

/// The python spelling of a rust type or variant name. Those are already in the case python uses
/// for classes, except for the few that `#[charon::rename]` spells the way OCaml wants them.
pub fn make_py_class_name(name: &str) -> String {
    if name.starts_with(char::is_lowercase) {
        name.to_case(Case::Pascal)
    } else {
        name.to_string()
    }
}

/// Indent every line of `text` by `level` levels of four spaces.
pub fn indent(text: &str, level: usize) -> String {
    let prefix = "    ".repeat(level);
    text.lines()
        .map(|line| {
            if line.is_empty() {
                String::new()
            } else {
                format!("{prefix}{line}")
            }
        })
        .join("\n")
}

/// The containers the AST is built out of. Python spells each of them its own way instead of
/// generating a class for them, so we must recognize them by name.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Container {
    /// `Vec<T>`.
    Vec,
    /// `IndexVec<I, T>`: a list whose indices are meaningful.
    IndexVec,
    /// `IndexedMap<I, T>`: serialized as a list of optional values indexed by `I`.
    IndexedMap,
    /// `indexmap::IndexMap<K, V, S>`: serialized as a list of key/value pairs.
    KeyValueMap,
    /// `Option<T>`.
    Option,
    /// `RangeInclusive<T>`: a pair of endpoints.
    RangeInclusive,
    /// Anything that python represents with `str`.
    Str,
    /// A wrapper that python doesn't represent at all, such as rust's hash-consing wrapper.
    Transparent,
}

impl Container {
    /// Recognize a container from the name of its type.
    pub fn from_name(name: &str) -> Option<Container> {
        Some(match name {
            "Vec" => Container::Vec,
            "IndexVec" => Container::IndexVec,
            "IndexedMap" => Container::IndexedMap,
            "IndexMap" => Container::KeyValueMap,
            "Option" => Container::Option,
            "RangeInclusive" => Container::RangeInclusive,
            "String" | "Ustr" | "PathBuf" => Container::Str,
            "HashConsed" => Container::Transparent,
            _ => return None,
        })
    }
}

impl<'a> GenerateCtx<'a> {
    /// The rust name of this type, after `#[charon::rename]`.
    pub fn type_rust_name(&self, td: &TypeDecl) -> &'a str {
        let Some(td) = self.crate_data.type_decls.get(td.def_id) else {
            unreachable!()
        };
        td.item_meta
            .attr_info
            .rename
            .as_deref()
            .unwrap_or(td.item_meta.name.short_str().unwrap())
    }

    /// The name of the python class or type alias that represents this type. Rust type names are
    /// already valid python class names, so we keep them as they are.
    pub fn type_to_py_class(&self, td: &TypeDecl) -> String {
        let name = make_py_class_name(self.type_rust_name(td));
        match self.ambiguous_types.get(&td.def_id) {
            // Everything lives in one module, so instead of qualifying uses of the type like OCaml
            // does, we make its name unique.
            Some((_, qualifier)) => format!("{qualifier}{name}"),
            None => name.to_string(),
        }
    }

    /// The base name of the functions that handle this type, e.g. `ty_kind` for `TyKind`.
    pub fn type_to_py_fn(&self, td: &TypeDecl) -> String {
        make_py_ident(&self.type_to_py_class(td))
    }

    /// The name of the class that represents one variant of an enum. Variants share the module's
    /// namespace, so they are named after the enum they belong to; the ones that were renamed
    /// (typically through `#[charon::variants_prefix]`) already say which enum they come from.
    pub fn variant_to_py_class(&self, td: &TypeDecl, variant: &Variant) -> String {
        let ty_name = self.type_to_py_class(td);
        let name = make_py_class_name(variant.renamed_name());
        if name.starts_with(&ty_name) {
            name
        } else {
            format!("{ty_name}{name}")
        }
    }

    /// The python type annotation for this type. As the generated module is full of mutually
    /// recursive definitions, these are only ever used inside strings.
    pub fn type_to_py_name(&self, ty: &Ty) -> String {
        match ty.kind() {
            TyKind::Scalar(ScalarTy::Bool) => "bool".to_string(),
            // Python has no character type; we use one-character strings.
            TyKind::Scalar(ScalarTy::Char) => "str".to_string(),
            // Python integers are arbitrary-precision, so even `u128` fits.
            TyKind::Scalar(ScalarTy::Integer(_)) => "int".to_string(),
            TyKind::Scalar(ScalarTy::Float(_)) => "float".to_string(),
            TyKind::Adt(tref) => {
                let args = tref
                    .generics
                    .types
                    .iter()
                    .map(|ty| self.type_to_py_name(ty))
                    .collect_vec();
                match tref.as_builtin() {
                    Some(BuiltinAdt::Box) => args[0].clone(),
                    Some(BuiltinAdt::Tuple) => format!("tuple[{}]", args.iter().join(", ")),
                    None => {
                        let Some(tdecl) = self.crate_data.type_decls.get(tref.id) else {
                            eprintln!(
                                "Warning: type {} missing from llbc",
                                self.crate_data
                                    .item_name(tref.id)
                                    .debug_repr(self.crate_data)
                            );
                            return "Any".to_string();
                        };
                        match Container::from_name(self.type_rust_name(tdecl)) {
                            Some(Container::Transparent) => args[0].clone(),
                            Some(Container::Str) => "str".to_string(),
                            Some(Container::Vec) => format!("list[{}]", args[0]),
                            // The index is implicit in the position of each element.
                            Some(Container::IndexVec) => format!("list[{}]", args[1]),
                            Some(Container::IndexedMap) => {
                                format!("dict[{}, {}]", args[0], args[1])
                            }
                            Some(Container::KeyValueMap) => {
                                format!("list[tuple[{}, {}]]", args[0], args[1])
                            }
                            Some(Container::Option) => format!("Optional[{}]", args[0]),
                            Some(Container::RangeInclusive) => {
                                format!("tuple[{}, {}]", args[0], args[0])
                            }
                            None => {
                                let base = self.type_to_py_class(tdecl);
                                if args.is_empty() {
                                    base
                                } else {
                                    format!("{base}[{}]", args.iter().join(", "))
                                }
                            }
                        }
                    }
                    _ => unimplemented!("{ty:?}"),
                }
            }
            TyKind::TypeVar(DeBruijnVar::Free(id) | DeBruijnVar::Bound(_, id)) => format!("T{id}"),
            _ => unimplemented!("{ty:?}"),
        }
    }
}
