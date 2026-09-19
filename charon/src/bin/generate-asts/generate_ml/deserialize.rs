//! Code shared between the json and postcard deserializer generators.
//!
//! The two formats differ in how each type is laid out in the input, hence in the body of each
//! generated function. Everything else — the names of the generated functions, their signatures,
//! how generic arguments are threaded through, which types get a hand-written implementation — is
//! the same and lives here.

use std::collections::HashMap;

use charon_lib::ast::*;
use itertools::Itertools;

use super::GenerateCtx;

/// A serialization format we generate OCaml deserializers for.
pub struct Format {
    /// Suffix of the generated function names, e.g. `of_json` in `ty_of_json`.
    pub suffix: &'static str,
    /// The OCaml type of the deserialization context.
    pub ctx_ty: &'static str,
    /// The name of the variable that holds the input being read.
    pub input: &'static str,
    /// The OCaml type of that variable.
    pub input_ty: &'static str,
    /// The name we give to the value being read inside a generated closure. For json this is the
    /// sub-value we matched on, which is not the function argument.
    pub value: &'static str,
    /// The name of the function that reads a scalar of the given type.
    pub scalar_fn: fn(ScalarTy) -> &'static str,
    /// Types whose deserializer we write by hand, by charon name.
    pub manual_impls: &'static [(&'static str, &'static str)],
}

/// Generates the deserializers of a given [`Format`].
pub struct Deserializer<'a, 'ctx> {
    pub ctx: &'a GenerateCtx<'ctx>,
    pub format: &'a Format,
    manual_impls: HashMap<TypeDeclId, String>,
}

impl<'a, 'ctx> Deserializer<'a, 'ctx> {
    pub fn new(ctx: &'a GenerateCtx<'ctx>, format: &'a Format) -> Self {
        let manual_impls = ctx.names_to_type_id_map(format.manual_impls);
        Deserializer {
            ctx,
            format,
            manual_impls,
        }
    }

    /// The name of the function that reads the thing named `base`, e.g. `list` -> `list_of_json`.
    pub fn fn_name(&self, base: &str) -> String {
        format!("{base}_{}", self.format.suffix)
    }

    /// The hand-written body for this type, if any.
    pub fn manual_impl(&self, decl: &TypeDecl) -> Option<&str> {
        self.manual_impls.get(&decl.def_id).map(|s| s.as_str())
    }

    /// Converts a type to the appropriate `*_of_<format>` call. In case of generics, this combines
    /// several functions, e.g. `list_of_json bool_of_json`.
    pub fn call(&self, ty: &Ty) -> String {
        let value = self.format.value;
        match ty.kind() {
            TyKind::Scalar(scalar) => (self.format.scalar_fn)(*scalar).to_string(),
            TyKind::Adt(tref) => {
                let mut expr = Vec::new();
                for ty in &tref.generics.types {
                    expr.push(self.call(ty))
                }
                let mut wrap_in_map = false;
                match tref.as_builtin() {
                    None => {
                        let mut first = if let Some(tdecl) =
                            self.ctx.crate_data.type_decls.get(tref.id)
                        {
                            let (name, module) = self.ctx.type_to_ocaml_ident_raw(tdecl);
                            match module {
                                Some((_, short)) if !self.ctx.current_ids.contains(&tref.id) => {
                                    format!("{short}.{name}")
                                }
                                _ => name,
                            }
                        } else {
                            format!("missing_type_{}", tref.id)
                        };
                        if first == "vec" {
                            first = "list".to_string();
                        }
                        if first == "ustr" {
                            first = "string".to_string();
                        }
                        if first == "index_map" {
                            // That's the `indexmap::IndexMap` case. Pass something dummy for the
                            // `RandomState` parameter.
                            expr[2] = self.fn_name("int");
                        }

                        if first == "indexed_map" {
                            wrap_in_map = true;
                            first = "opt_indexed_map".to_string();
                        }

                        expr.insert(0, self.fn_name(&first));
                    }
                    Some(BuiltinAdt::Box) => expr.insert(0, self.fn_name("box")),
                    Some(BuiltinAdt::Tuple) => {
                        let name = match tref.generics.types.len() {
                            2 => self.fn_name("pair"),
                            3 => self.fn_name("triple"),
                            len => self.fn_name(&format!("tuple_{len}")),
                        };
                        expr.insert(0, name);
                    }
                    _ => unimplemented!("{ty:?}"),
                }
                let mut expr = expr.into_iter().map(|f| format!("({f})")).join(" ");
                if wrap_in_map {
                    let index_name = self.ctx.type_to_rust_name(&tref.generics.types[0]).unwrap();
                    expr = format!(
                        "(fun ctx {value} -> Result.map {index_name}.map_of_indexed_list ({expr} ctx {value}))"
                    );
                }
                expr
            }
            TyKind::TypeVar(DeBruijnVar::Free(id)) => format!("arg{id}_{}", self.format.suffix),
            _ => unimplemented!("{ty:?}"),
        }
    }

    /// `let* <var> = <read a value of type `ty`> ctx <source> in`: the building block of every
    /// deserializer. `source` is the value being read from; for sequential formats that's always
    /// the state, for json it's the sub-value we matched on.
    pub fn bind(&self, var: &str, ty: &Ty, source: &str) -> String {
        let call = self.call(ty);
        format!("let* {var} = {call} ctx {source} in")
    }

    /// The OCaml type these functions return, to annotate constructed records with.
    pub fn return_ty(&self, decl: &TypeDecl) -> String {
        let return_ty = self.ctx.type_to_ocaml_ident(decl);
        if decl.generics.types.is_empty() {
            return_ty
        } else {
            format!("_ {return_ty}")
        }
    }

    /// Wraps a deserializer body into the corresponding (co-recursive) function definition.
    fn build_function(&self, decl: &TypeDecl, body: &str) -> String {
        let Format {
            suffix,
            ctx_ty,
            input,
            input_ty,
            ..
        } = self.format;
        let ty = TyKind::Adt(TypeDeclRef {
            id: decl.def_id,
            generics: decl.generics.identity_args().into(),
            builtin: decl.src.as_builtin().cloned(),
        })
        .into_ty();
        let (ty_name, _) = self.ctx.type_to_ocaml_ident_raw(decl);
        let ty = self.ctx.type_to_ocaml_name(&ty);
        let signature = if decl.generics.types.is_empty() {
            format!(
                "{ty_name}_{suffix} (ctx : {ctx_ty}) ({input} : {input_ty}) : ({ty}, string) result ="
            )
        } else {
            let types = &decl.generics.types;
            let gen_vars_space = types
                .iter()
                .enumerate()
                .map(|(i, _)| format!("'a{i}"))
                .join(" ");

            let mut args = Vec::new();
            let mut ty_args = Vec::new();
            for (i, _) in types.iter().enumerate() {
                args.push(format!("arg{i}_{suffix}"));
                ty_args.push(format!(
                    "({ctx_ty} -> {input_ty} -> ('a{i}, string) result)"
                ));
            }
            args.push("ctx".to_string());
            ty_args.push(ctx_ty.to_string());
            args.push(input.to_string());
            ty_args.push(input_ty.to_string());

            let ty_args = ty_args.into_iter().join(" -> ");
            let args = args.into_iter().join(" ");
            let fun_ty = format!("{gen_vars_space}. {ty_args} -> ({ty}, string) result");
            format!("{ty_name}_{suffix} : {fun_ty} = fun {args} ->")
        };
        format!(
            r#"
        and {signature}
          combine_error_msgs {input} __FUNCTION__
            ({body})
        "#
        )
    }

    /// Generates the whole block of mutually-recursive deserialization functions. `body` computes
    /// the format-specific body of the function for one type.
    pub fn generate(
        &self,
        tys: Vec<&TypeDecl>,
        body: impl Fn(&Self, &TypeDecl) -> String,
    ) -> String {
        let fns = tys
            .iter()
            .map(|decl| self.build_function(decl, &body(self, decl)))
            .format("\n");
        format!("let rec ___ = ()\n{fns}")
    }
}
