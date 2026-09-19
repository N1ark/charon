//! Generate OCaml deserialization code for our types.
//!
//! This uses Charon's translated AST definitions to generate the appropriate OCaml type definitions
//! and deserialization functions. The generated code is inserted into the templates in this
//! directory.
//!
//! To run it, call `cargo run --bin generate-asts`. It is also run by `make generate-asts` in the
//! crate root. Don't forget to format the output code after regenerating.

use anyhow::Result;
use charon_lib::ast::*;
use std::path::PathBuf;

use crate::codegen::*;

use self::to_ocaml_ty::DeriveVisitors;

mod deserialize;
mod of_json;
mod of_postcard;
mod to_ocaml_ty;
mod util;

/// The kind of code generation to perform.
#[derive(Clone, Copy)]
enum GenerationKind {
    OfJson,
    OfPostcard,
    TypeDecl(Option<DeriveVisitors>),
}

struct Ocaml;

impl Backend for Ocaml {
    type Kind = GenerationKind;

    fn marker(i: usize) -> String {
        format!("(* __REPLACE{i}__ *)")
    }

    fn generate(ctx: &mut GenerateCtx<'_>, kind: GenerationKind, tys: Vec<&TypeDecl>) -> String {
        match kind {
            GenerationKind::OfJson => of_json::generate(ctx, tys),
            GenerationKind::OfPostcard => of_postcard::generate(ctx, tys),
            GenerationKind::TypeDecl(visitors) => ctx.type_decls_to_ocaml(&visitors, tys),
        }
    }
}

pub(crate) fn generate(
    ctx: &mut GenerateCtx<'_>,
    template_dir: PathBuf,
    output_dir: PathBuf,
) -> Result<()> {
    let ast_types = AstTypes::new(ctx);
    let mut to_generate = ToGenerate::new(ctx);

    #[rustfmt::skip]
    let generate_code_for: Vec<GenerateCodeFor<Ocaml>> = vec![
        GenerateCodeFor {
            template: template_dir.join("Meta.ml"),
            target: output_dir.join("Generated_Meta.ml"),
            markers: to_generate.take(ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["BigInt.big_int"],
                    name: "meta",
                    reduce: true,
                    extra_types: &["path_buf"],
                })), &[
                    "File",
                    "Span",
                    "AttrInfo",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Values.ml"),
            target: output_dir.join("Generated_Values.ml"),
            markers: to_generate.take(ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["Generated_Meta.meta"],
                    name: "scalar",
                    reduce: true,
                    extra_types: &["char_value"],
                })), &[
                    "IntegerValue",
                    "FloatValue",
                    "IntegerTy",
                    "ScalarTy",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Types.ml"),
            target: output_dir.join("Generated_Types.ml"),
            markers: to_generate.take(ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["scalar"],
                    name: "type_vars",
                    reduce: true,
                    extra_types: &[],
                })), &[
                    "TypeVarId",
                    "TraitClauseId",
                    "DeBruijnVar",
                    "ItemId",
                ]),
                // Can't merge into above because aeneas uses the above alongside their own partial
                // copy of `ty`, which causes method type clashes.
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["ty_base"],
                    name: "ty",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "ConstantExpr",
                    "TyKind",
                    "TraitImplRef",
                    "FunDeclRef",
                    "GlobalDeclRef",
                ]),
                // TODO: can't merge into above because of field name clashes (`types`, `regions` etc).
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["ty"],
                    name: "type_decl",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "Binder",
                    "TypeDecl",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("Expressions.ml"),
            target: output_dir.join("Generated_Expressions.ml"),
            markers: to_generate.take(ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["type_decl"],
                    name: "rvalue",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "Rvalue",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("GAst.ml"),
            target: output_dir.join("Generated_GAst.ml"),
            markers: to_generate.take(ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["rvalue"],
                    name: "fun_sig",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "Call",
                    "BorrowckStatement",
                    "DropKind",
                    "Assert",
                    "TypeSource",
                    "FunSource",
                    "GlobalSource",
                    "Locals",
                    "SwitchData",
                    "FunSig",
                    "Error",
                    "AbortKind",
                ]),
                // These have to be kept separate to avoid field name clashes
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["fun_sig"],
                    name: "global_decl",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "GlobalDecl",
                ]),
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["trait_decl_base"],
                    name: "trait_decl",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "TraitDecl",
                ]),
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["trait_decl"],
                    name: "trait_impl",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "TraitImpl",
                    "GExprBody",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("LlbcAst.ml"),
            target: output_dir.join("Generated_LlbcAst.ml"),
            markers: to_generate.take(ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    name: "statement_base",
                    ancestors: &["trait_impl"],
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "charon_lib::ast::bodies::structured::Statement",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("UllbcAst.ml"),
            target: output_dir.join("Generated_UllbcAst.ml"),
            markers: to_generate.take(ctx, &[
                (GenerationKind::TypeDecl(Some(DeriveVisitors {
                    ancestors: &["trait_impl"],
                    name: "ullbc_ast",
                    reduce: false,
                    extra_types: &[],
                })), &[
                    "charon_lib::ast::bodies::unstructured::BodyContents",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("FullAst.ml"),
            target: output_dir.join("Generated_FullAst.ml"),
            markers: to_generate.take(ctx, &[
                (GenerationKind::TypeDecl(None), &[
                    "FunDecl",
                    "Body",
                    "CliOpts",
                    "DeclarationGroup",
                    "TranslatedCrate",
                ]),
            ]),
        },
        GenerateCodeFor {
            template: template_dir.join("OfJson.ml"),
            target: output_dir.join("Generated_OfJson.ml"),
            markers: vec![
                (GenerationKind::OfJson, ast_types.gast.clone()),
                (GenerationKind::OfJson, ast_types.ullbc.clone()),
                (GenerationKind::OfJson, ast_types.llbc.clone()),
                (GenerationKind::OfJson, ast_types.full_ast.clone()),
            ],
        },
        GenerateCodeFor {
            template: template_dir.join("OfPostcard.ml"),
            target: output_dir.join("Generated_OfPostcard.ml"),
            markers: vec![
                (GenerationKind::OfPostcard, ast_types.gast),
                (GenerationKind::OfPostcard, ast_types.ullbc),
                (GenerationKind::OfPostcard, ast_types.llbc),
                (GenerationKind::OfPostcard, ast_types.full_ast),
            ],
        },
    ];
    for file in generate_code_for {
        file.generate(ctx)?;
    }
    Ok(())
}
