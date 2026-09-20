//! The language-agnostic half of AST generation.
//!
//! Generating the AST for a language means answering the same questions every time: which types
//! belong to the AST, which of them go in which file, which ones need disambiguating, and how each
//! type is serialized. None of that depends on the target language, so it lives here; a [`Backend`]
//! only has to say how to spell things.

use anyhow::{Context, Result};
use charon_lib::ast::*;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::PathBuf;

/// Types for which we don't want to generate a type declaration at all. Some of them still get a
/// deserializer; the ones that don't are in [`SPELLED_OUT_AT_USE_SITE`].
const DONT_GENERATE: &[&str] = &[
    "TraitTypeConstraintId",
    "charon_lib::ids::index_vec::IndexVec",
    "charon_lib::ids::index_map::IndexMap",
];

/// Types that every backend spells out where they are used rather than calling a deserializer for
/// them: the containers, whose declarations say how they store their contents and not how serde
/// writes them, and the hash-consing wrapper, which is read through the deduplication table of the
/// type it wraps.
const SPELLED_OUT_AT_USE_SITE: &[&str] = &[
    "charon_lib::ids::index_vec::IndexVec",
    "charon_lib::ids::index_map::IndexMap",
    "indexmap::map::IndexMap",
    "HashConsed",
];

/// Types whose short name is not unique, along with the module they are declared in and a short
/// qualifier. What a backend does with those is up to it: OCaml qualifies uses of the type with
/// the module it comes from, python prefixes the qualifier to the type name.
#[rustfmt::skip]
const AMBIGUOUS_TYPES: &[(&str, (&str, &str))] = &[
    ("charon_lib::ast::bodies::unstructured::Statement", ("Generated_UllbcAst", "Ullbc")),
    ("charon_lib::ast::bodies::unstructured::StatementKind", ("Generated_UllbcAst", "Ullbc")),
    ("charon_lib::ast::bodies::unstructured::BlockData", ("Generated_UllbcAst", "Ullbc")),
    ("charon_lib::ast::bodies::unstructured::BlockId", ("Generated_UllbcAst", "Ullbc")),
    ("charon_lib::ast::bodies::structured::Statement", ("Generated_LlbcAst", "Llbc")),
    ("charon_lib::ast::bodies::structured::StatementKind", ("Generated_LlbcAst", "Llbc")),
    ("charon_lib::ast::bodies::structured::Block", ("Generated_LlbcAst", "Llbc")),
    ("charon_lib::ast::bodies::structured::BlockId", ("Generated_LlbcAst", "Llbc")),
];

pub struct GenerateCtx<'a> {
    pub crate_data: &'a TranslatedCrate,
    pub name_to_type: HashMap<String, &'a TypeDecl>,
    /// For each type, list the types it contains.
    pub type_tree: HashMap<TypeDeclId, HashSet<TypeDeclId>>,
    /// See [`AMBIGUOUS_TYPES`].
    pub ambiguous_types: HashMap<TypeDeclId, (String, String)>,
    /// The current module name being compiled.
    pub current_module: Option<String>,
    /// The list of types currently being generated.
    pub current_ids: Vec<TypeDeclId>,
}

impl<'a> GenerateCtx<'a> {
    pub fn new(crate_data: &'a TranslatedCrate) -> Self {
        let mut name_to_type: HashMap<String, &TypeDecl> = Default::default();
        let mut type_tree = HashMap::default();
        for ty in &crate_data.type_decls {
            let long_name = ty.item_meta.name.debug_repr(crate_data);
            if long_name.starts_with("charon_lib")
                && let Some(short_name) = ty.item_meta.name.short_str()
            {
                name_to_type.insert(short_name.to_string(), ty);
            }
            name_to_type.insert(long_name, ty);

            let mut contained = HashSet::new();
            ty.dyn_visit(|id: &TypeDeclId| {
                contained.insert(*id);
            });
            type_tree.insert(ty.def_id, contained);
        }

        let mut ctx = GenerateCtx {
            crate_data,
            name_to_type,
            type_tree,
            ambiguous_types: Default::default(),
            current_module: None,
            current_ids: vec![],
        };

        ctx.ambiguous_types = AMBIGUOUS_TYPES
            .iter()
            .map(|(name, (m1, m2))| (ctx.id_from_name(name), (m1.to_string(), m2.to_string())))
            .collect();

        ctx
    }

    pub fn id_from_name(&self, name: &str) -> TypeDeclId {
        self.name_to_type
            .get(name)
            .unwrap_or_else(|| panic!("Name not found: `{name}`"))
            .def_id
    }

    /// List the (recursive) children of this type.
    pub fn children_of(&self, name: &str) -> HashSet<TypeDeclId> {
        let start_id = self.id_from_name(name);
        self.children_of_inner(vec![start_id], |_| true)
    }

    /// List the (recursive) children of these types.
    pub fn children_of_many(&self, names: &[&str]) -> HashSet<TypeDeclId> {
        self.children_of_inner(
            names.iter().map(|name| self.id_from_name(name)).collect(),
            |_| true,
        )
    }

    pub fn children_of_inner(
        &self,
        ty: Vec<TypeDeclId>,
        explore: impl Fn(TypeDeclId) -> bool,
    ) -> HashSet<TypeDeclId> {
        let mut children = HashSet::new();
        let mut stack = ty.to_vec();
        while let Some(id) = stack.pop() {
            if !children.contains(&id)
                && explore(id)
                && self
                    .crate_data
                    .type_decls
                    .get(id)
                    .is_some_and(|decl| decl.item_meta.is_local)
            {
                children.insert(id);
                if let Some(contained) = self.type_tree.get(&id) {
                    stack.extend(contained);
                }
            }
        }
        children
    }

    /// For a type that refers to an ADT, return the name of that ADT.
    pub fn type_to_rust_name(&self, ty: &Ty) -> Option<&str> {
        let index_ty = ty.as_adt()?.id;
        self.crate_data.item_name(index_ty).short_str()
    }

    pub fn names_to_type_id_map(&self, data: &[(&str, &str)]) -> HashMap<TypeDeclId, String> {
        data.iter()
            .map(|(name, def)| (self.id_from_name(name), def.to_string()))
            .collect()
    }

    pub fn names_to_type_id_set(&self, data: &[&str]) -> HashSet<TypeDeclId> {
        data.iter().map(|name| self.id_from_name(name)).collect()
    }
}

/// How a type is (de)serialized, with the details of its rust declaration normalized away.
///
/// All the generators must agree on this classification, otherwise the types they emit and the
/// deserializers they emit disagree; hence we compute it once here.
pub enum TypeShape<'a> {
    /// An empty struct. Carries no data.
    Unit,
    /// One of our strongly-typed indices (`struct FooId { _raw: usize }`). Carries the name of the
    /// type, which is also the name of the module that defines the id type.
    Index(&'a str),
    /// A wrapper that is serialized exactly like the type it wraps: a one-field tuple struct, a
    /// `#[serde(transparent)]` struct, or a type alias.
    Transparent(&'a Ty),
    /// A struct whose fields are all positional; serialized as a sequence.
    Tuple(&'a IndexVec<FieldId, Field>),
    /// A struct with named fields.
    Record(&'a IndexVec<FieldId, Field>),
    /// An enum.
    Enum(&'a IndexVec<VariantId, Variant>),
}

/// See [`TypeShape`].
pub fn type_shape(decl: &TypeDecl) -> TypeShape<'_> {
    match &decl.kind {
        TypeDeclKind::Struct(fields) if fields.is_empty() => TypeShape::Unit,
        TypeDeclKind::Struct(fields) if fields.len() == 1 && fields[0].name == "_raw" => {
            TypeShape::Index(decl.item_meta.name.short_str().unwrap())
        }
        TypeDeclKind::Struct(fields)
            if fields.len() == 1
                && (fields[0].is_positional
                    || decl
                        .item_meta
                        .attr_info
                        .attributes
                        .iter()
                        .any(|a| a.is_transparent())) =>
        {
            TypeShape::Transparent(&fields[0].ty)
        }
        TypeDeclKind::Alias(ty) => TypeShape::Transparent(ty),
        TypeDeclKind::Struct(fields) if fields.iter().all(|field| field.is_positional) => {
            TypeShape::Tuple(fields)
        }
        TypeDeclKind::Struct(fields) => TypeShape::Record(fields),
        TypeDeclKind::Enum(variants) => TypeShape::Enum(variants),
        TypeDeclKind::Union(..) | TypeDeclKind::Opaque | TypeDeclKind::Error(_) => {
            panic!(
                "cannot generate code for `{}`",
                decl.item_meta.name.short_str().unwrap_or("<unnamed>")
            )
        }
    }
}

/// A target language we generate the AST and its deserializers for.
pub trait Backend {
    /// What to generate at a marker site. Each backend picks its own, because they don't all need
    /// the same knobs: OCaml attaches visitor classes to its type declarations, python doesn't.
    type Kind: Copy;

    /// How the `i`th replacement marker is spelled in this language's templates. It must be
    /// a comment, as the templates have to be valid source files of their own.
    fn marker(i: usize) -> String;

    /// Generate the code that replaces one marker.
    fn generate(ctx: &mut GenerateCtx<'_>, kind: Self::Kind, tys: Vec<&TypeDecl>) -> String;
}

/// Replace markers in `template` with auto-generated code.
pub struct GenerateCodeFor<B: Backend> {
    pub template: PathBuf,
    pub target: PathBuf,
    /// Each list corresponds to a marker. We replace the ith marker with generated code for each
    /// definition in the ith list.
    ///
    /// Eventually we should reorder definitions so the generated ones are all in one block.
    /// Keeping the order is important while we migrate away from hand-written code.
    pub markers: Vec<(B::Kind, HashSet<TypeDeclId>)>,
}

impl<B: Backend> GenerateCodeFor<B> {
    pub fn generate(&self, ctx: &mut GenerateCtx) -> Result<()> {
        ctx.current_module = self
            .target
            .file_prefix()
            .and_then(|s| s.to_str())
            .map(|s| s.to_string());

        let mut template = fs::read_to_string(&self.template)
            .with_context(|| format!("Failed to read template file {}", self.template.display()))?;
        for (i, (kind, names)) in self.markers.iter().enumerate() {
            let tys = names
                .iter()
                .map(|&id| &ctx.crate_data[id])
                .sorted_by_key(|tdecl| (tdecl.item_meta.name.short_str().unwrap(), tdecl.def_id))
                .collect::<Vec<_>>();
            ctx.current_ids = names.iter().copied().collect();
            let generated = B::generate(ctx, *kind, tys);
            template = template.replace(&B::marker(i), &generated);
        }

        fs::write(&self.target, template)
            .with_context(|| format!("Failed to write generated file {}", self.target.display()))?;
        Ok(())
    }
}

/// The types that make up the AST, split according to which body representation they belong to.
/// Deserializers are emitted in this order so that a type is always defined before it is used.
pub struct AstTypes {
    /// Types used by both body representations.
    pub gast: HashSet<TypeDeclId>,
    /// Types specific to the structured (llbc) representation.
    pub llbc: HashSet<TypeDeclId>,
    /// Types specific to the unstructured (ullbc) representation.
    pub ullbc: HashSet<TypeDeclId>,
    /// Everything else, i.e. the types that are not part of a body.
    pub full_ast: HashSet<TypeDeclId>,
}

impl AstTypes {
    pub fn new(ctx: &GenerateCtx<'_>) -> Self {
        let mut this = AstTypes {
            gast: HashSet::new(),
            llbc: HashSet::new(),
            ullbc: HashSet::new(),
            full_ast: HashSet::new(),
        };
        let mut all_types: HashSet<_> = ctx.children_of("TranslatedCrate");
        for name in SPELLED_OUT_AT_USE_SITE {
            all_types.remove(&ctx.id_from_name(name));
        }
        let all_llbc_types: HashSet<_> =
            ctx.children_of_many(&["charon_lib::ast::bodies::structured::Block"]);
        let all_ullbc_types: HashSet<_> = ctx.children_of_many(&[
            "charon_lib::ast::bodies::unstructured::BlockData",
            "charon_lib::ast::bodies::unstructured::BlockId",
        ]);
        for ty in all_types {
            let in_llbc = all_llbc_types.contains(&ty);
            let in_ullbc = all_ullbc_types.contains(&ty);
            match (in_llbc, in_ullbc) {
                (true, false) => this.llbc.insert(ty),
                (false, true) => this.ullbc.insert(ty),
                (true, true) => this.gast.insert(ty),
                (false, false) => this.full_ast.insert(ty),
            };
        }
        this
    }

    /// All the types of the AST, for backends that don't need them grouped.
    pub fn all(&self) -> HashSet<TypeDeclId> {
        self.gast
            .iter()
            .chain(&self.llbc)
            .chain(&self.ullbc)
            .chain(&self.full_ast)
            .copied()
            .collect()
    }
}

/// Hands out the types whose declaration is still to be generated.
///
/// Each call to [`Self::take`] returns the children of the listed types that haven't been handed
/// out yet. By calling it in dependency order, this allows to organize types into files without
/// having to list them all.
pub struct ToGenerate {
    processed: HashSet<TypeDeclId>,
}

impl ToGenerate {
    pub fn new(ctx: &GenerateCtx<'_>) -> Self {
        ToGenerate {
            processed: ctx.names_to_type_id_set(DONT_GENERATE),
        }
    }

    pub fn take<K: Copy>(
        &mut self,
        ctx: &GenerateCtx<'_>,
        markers: &[(K, &[&str])],
    ) -> Vec<(K, HashSet<TypeDeclId>)> {
        markers
            .iter()
            .map(|(kind, type_names)| {
                let unprocessed_types: HashSet<_> = ctx
                    .children_of_many(type_names)
                    .into_iter()
                    .filter(|&id| self.processed.insert(id))
                    .collect();
                (*kind, unprocessed_types)
            })
            .collect_vec()
    }
}
