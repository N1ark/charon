use charon_lib::ast::*;
use convert_case::{Case, Casing};
use itertools::Itertools;

use crate::codegen::GenerateCtx;

pub fn make_ocaml_ident(name: &str) -> String {
    let leading_underscores = name.len() - name.trim_start_matches('_').len();
    let mut name = "_".repeat(leading_underscores) + &name.to_case(Case::Snake);
    if matches!(
        &*name,
        "assert"
            | "bool"
            | "char"
            | "end"
            | "float"
            | "fun"
            | "function"
            | "include"
            | "let"
            | "method"
            | "open"
            | "rec"
            | "struct"
            | "to"
            | "type"
            | "virtual"
    ) {
        name += "_";
    }
    name
}

impl<'a> GenerateCtx<'a> {
    /// Returns the OCaml identifier corresponding to this type,
    /// and the generated module name + short module name associated to it if
    /// they exist.
    pub fn type_to_ocaml_ident_raw(&self, td: &TypeDecl) -> (String, Option<(String, String)>) {
        let name = td
            .item_meta
            .attr_info
            .rename
            .as_deref()
            .unwrap_or(td.item_meta.name.short_str().unwrap());
        let module = self.ambiguous_types.get(&td.def_id);
        (make_ocaml_ident(name), module.cloned())
    }

    pub fn type_to_ocaml_ident(&self, td: &TypeDecl) -> String {
        let (name, module) = self.type_to_ocaml_ident_raw(td);
        match module {
            Some((module, _)) if self.current_module.as_ref().is_none_or(|m| m != &module) => {
                format!("{module}.{name}")
            }
            _ => name,
        }
    }

    /// Converts a type to the appropriate ocaml name. In case of generics, this provides appropriate
    /// parameters.
    pub fn type_to_ocaml_name(&self, ty: &Ty) -> String {
        match ty.kind() {
            TyKind::Scalar(ScalarTy::Bool) => "bool".to_string(),
            TyKind::Scalar(ScalarTy::Char) => "char_value".to_string(),
            TyKind::Scalar(ScalarTy::Integer(IntegerTy::Signed(int_ty))) => match int_ty {
                // Even though OCaml ints are only 63 bits, only scalars with their 128 bits should be able to become too large
                IntTy::I128 => "big_int".to_string(),
                _ => "int".to_string(),
            },
            TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(uint_ty))) => match uint_ty {
                // Even though OCaml ints are only 63 bits, only scalars with their 128 bits should be able to become too large
                UIntTy::U128 => "big_int".to_string(),
                _ => "int".to_string(),
            },
            TyKind::Scalar(ScalarTy::Float(_)) => "float_of_json".to_string(),
            TyKind::Adt(tref) => {
                let mut args = tref
                    .generics
                    .types
                    .iter()
                    .map(|ty| self.type_to_ocaml_name(ty))
                    .map(|name| {
                        if !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
                            format!("({name})")
                        } else {
                            name
                        }
                    })
                    .collect_vec();
                match tref.as_builtin() {
                    None => {
                        let mut base_ty =
                            if let Some(tdecl) = self.crate_data.type_decls.get(tref.id) {
                                self.type_to_ocaml_ident(tdecl)
                            } else {
                                let name = self.crate_data.item_name(tref.id);
                                eprintln!(
                                    "Warning: type {} missing from llbc",
                                    name.debug_repr(self.crate_data)
                                );
                                name.short_str().unwrap().to_lowercase()
                            };
                        if base_ty == "vec" {
                            base_ty = "list".to_string();
                        }
                        if base_ty == "ustr" {
                            base_ty = "string".to_string();
                        }
                        if base_ty == "indexed_map" {
                            let index_name = args.remove(0); // Remove the index generic param
                            base_ty = format!("{index_name}_map");
                        }
                        if base_ty == "index_vec" {
                            base_ty = "list".to_string();
                            args.remove(0); // Remove the index generic param
                        }
                        if base_ty == "index_map" {
                            // That's the `indexmap::IndexMap` case. Translate as a list of pairs.
                            base_ty = "list".to_string();
                            args = vec![format!("( {} * {} )", args[0], args[1])]
                        }
                        let args = match args.as_slice() {
                            [] => String::new(),
                            [arg] => format!("{arg} "),
                            args => format!("({})", args.iter().join(",")),
                        };
                        format!("{args}{base_ty}")
                    }
                    Some(BuiltinAdt::Box) => args[0].clone(),
                    Some(BuiltinAdt::Tuple) => args.iter().join("*"),
                    _ => unimplemented!("{ty:?}"),
                }
            }
            TyKind::TypeVar(DeBruijnVar::Free(id) | DeBruijnVar::Bound(_, id)) => format!("'a{id}"),
            _ => unimplemented!("{ty:?}"),
        }
    }
}
