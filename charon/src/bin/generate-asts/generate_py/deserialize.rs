//! Code shared between the json and postcard deserializer generators, the python counterpart of
//! [`crate::generate_ml::deserialize`].

use std::collections::HashMap;

use charon_lib::ast::*;
use itertools::Itertools;

use super::util::*;
use crate::codegen::GenerateCtx;

/// A serialization format we generate python deserializers for.
pub struct Format {
    /// Suffix of the generated function names, e.g. `of_json` in `ty_of_json`.
    pub suffix: &'static str,
    /// The python type of the deserialization context.
    pub ctx_ty: &'static str,
    /// The name of the parameter that holds the input being read.
    pub input: &'static str,
    /// The python type of that parameter.
    pub input_ty: &'static str,
    /// The alias for the type of a function that reads a value of this format.
    pub decoder_ty: &'static str,
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

    /// Converts a type to the expression that reads it. Generic types are curried over the readers
    /// of their arguments, e.g. `list_of_json(option_of_json(span_of_json))`.
    pub fn call(&self, ty: &Ty) -> String {
        match ty.kind() {
            TyKind::Scalar(scalar) => (self.format.scalar_fn)(*scalar).to_string(),
            TyKind::Adt(tref) => {
                let mut args = tref
                    .generics
                    .types
                    .iter()
                    .map(|ty| self.call(ty))
                    .collect_vec();
                let name = match tref.as_builtin() {
                    None => {
                        let Some(tdecl) = self.ctx.crate_data.type_decls.get(tref.id) else {
                            return format!("missing_type_{}", tref.id);
                        };
                        match Container::from_name(self.ctx.type_rust_name(tdecl)) {
                            // Hash-consing is invisible in python.
                            Some(Container::Transparent) => return args.remove(0),
                            Some(Container::Str) => {
                                args.clear();
                                self.fn_name("string")
                            }
                            Some(Container::Vec) => self.fn_name("list"),
                            // The key decoder is unused: keys are the positions in the list.
                            Some(Container::IndexedMap) => self.fn_name("indexed_map"),
                            Some(Container::KeyValueMap) => {
                                // `indexmap::IndexMap` has a hasher parameter we never read; pass
                                // something to keep the arity right.
                                args[2] = self.fn_name("int");
                                self.fn_name(&self.ctx.type_to_py_fn(tdecl))
                            }
                            _ => self.fn_name(&self.ctx.type_to_py_fn(tdecl)),
                        }
                    }
                    Some(BuiltinAdt::Box) => self.fn_name("box"),
                    Some(BuiltinAdt::Tuple) => match tref.generics.types.len() {
                        2 => self.fn_name("pair"),
                        3 => self.fn_name("triple"),
                        len => self.fn_name(&format!("tuple_{len}")),
                    },
                    _ => unimplemented!("{ty:?}"),
                };
                if args.is_empty() {
                    name
                } else {
                    format!("{name}({})", args.into_iter().join(", "))
                }
            }
            TyKind::TypeVar(DeBruijnVar::Free(id)) => format!("arg{id}_{}", self.format.suffix),
            _ => unimplemented!("{ty:?}"),
        }
    }

    /// `<var> = <read a value of type `ty` from `source`>`: the building block of every
    /// deserializer. `source` is the value being read from; for a sequential format that's always
    /// the reader, for json it's the sub-value we are looking at.
    pub fn bind(&self, var: &str, ty: &Ty, source: &str) -> String {
        let call = self.call(ty);
        format!("{var} = {call}(ctx, {source})")
    }

    /// The python annotation for the value these functions return.
    pub fn return_ty(&self, decl: &TypeDecl) -> String {
        let class = self.ctx.type_to_py_class(decl);
        if decl.generics.types.is_empty() {
            class
        } else {
            let args = (0..decl.generics.types.len())
                .map(|i| format!("T{i}"))
                .join(", ");
            format!("{class}[{args}]")
        }
    }

    /// Wraps a deserializer body into the corresponding function definition. A type with generic
    /// parameters becomes a function of their deserializers that returns a deserializer.
    fn build_function(&self, decl: &TypeDecl, body: &str) -> String {
        let Format {
            suffix,
            ctx_ty,
            input,
            input_ty,
            decoder_ty,
            ..
        } = self.format;
        let name = format!("{}_{suffix}", self.ctx.type_to_py_fn(decl));
        let ret = self.return_ty(decl);
        let params = format!("ctx: {ctx_ty}, {input}: {input_ty}");
        if decl.generics.types.is_empty() {
            format!("def {name}({params}) -> {ret}:\n{}\n", indent(body, 1))
        } else {
            let args = (0..decl.generics.types.len())
                .map(|i| format!("arg{i}_{suffix}: {decoder_ty}[T{i}]"))
                .join(", ");
            let inner = format!("def read({params}) -> {ret}:\n{}", indent(body, 1));
            format!(
                "def {name}({args}) -> {decoder_ty}[{ret}]:\n{}\n    return read\n",
                indent(&inner, 1),
            )
        }
    }

    /// Generates the whole block of deserialization functions. `body` computes the
    /// format-specific body of the function for one type.
    pub fn generate(
        &self,
        tys: Vec<&TypeDecl>,
        body: impl Fn(&Self, &TypeDecl) -> String,
    ) -> String {
        tys.iter()
            .map(|decl| self.build_function(decl, &body(self, decl)))
            .join("\n")
    }
}
