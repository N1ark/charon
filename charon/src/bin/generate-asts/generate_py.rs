//! Generate python type definitions and deserialization code for our types.
//!
//! This is the python counterpart of [`crate::generate_ml`]; both are driven by
//! [`crate::codegen`]. Python needs no module gymnastics, so the whole AST fits in three files:
//! the type declarations and one deserializer per serialization format.
//!
//! To run it, call `cargo run --bin generate-asts`. It is also run by `make generate-asts` in the
//! crate root.

use anyhow::Result;
use charon_lib::ast::*;
use std::path::PathBuf;

use crate::codegen::*;

mod deserialize;
mod of_json;
mod of_postcard;
mod to_py_ty;
mod util;

/// The kind of code generation to perform.
#[derive(Clone, Copy)]
enum GenerationKind {
    OfJson,
    OfPostcard,
    TypeDecl,
}

struct Python;

impl Backend for Python {
    type Kind = GenerationKind;

    fn marker(i: usize) -> String {
        format!("# __REPLACE{i}__")
    }

    fn generate(ctx: &mut GenerateCtx<'_>, kind: GenerationKind, tys: Vec<&TypeDecl>) -> String {
        match kind {
            GenerationKind::OfJson => of_json::generate(ctx, tys),
            GenerationKind::OfPostcard => of_postcard::generate(ctx, tys),
            GenerationKind::TypeDecl => ctx.type_decls_to_py(tys),
        }
    }
}

pub(crate) fn generate(
    ctx: &mut GenerateCtx<'_>,
    template_dir: PathBuf,
    output_dir: PathBuf,
) -> Result<()> {
    // Python has no ordering constraint between declarations, so each file takes the AST in one go.
    let all_types = AstTypes::new(ctx).all();
    let mut to_generate = ToGenerate::new(ctx);

    let generate_code_for: Vec<GenerateCodeFor<Python>> = vec![
        GenerateCodeFor {
            template: template_dir.join("types.py"),
            target: output_dir.join("types.py"),
            markers: to_generate.take(ctx, &[(GenerationKind::TypeDecl, &["TranslatedCrate"])]),
        },
        GenerateCodeFor {
            template: template_dir.join("of_json.py"),
            target: output_dir.join("of_json.py"),
            markers: vec![(GenerationKind::OfJson, all_types.clone())],
        },
        GenerateCodeFor {
            template: template_dir.join("of_postcard.py"),
            target: output_dir.join("of_postcard.py"),
            markers: vec![(GenerationKind::OfPostcard, all_types)],
        },
    ];
    for file in generate_code_for {
        file.generate(ctx)?;
    }
    Ok(())
}
