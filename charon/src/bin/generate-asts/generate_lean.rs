//! Generate Lean definitions that mirror our AST, along with postcard deserializers for them.
//!
//! Like `generate_ml`, this uses Charon's translated AST definitions. The generated files are
//! entirely generated; the hand-written support code lives in `charon-lean/Charon/Basic.lean` and
//! `charon-lean/Charon/Postcard.lean`.
//!
//! The Lean types follow the Rust ones closely: same type, field and variant names, strongly-typed
//! ids and `IndexVec`/`IndexMap`s. Like in OCaml, we hide the implementation details that don't
//! affect the serialized data: hash-consing, type info caches and boxes are transparent, and
//! newtypes are represented by their contents.
//!
//! Lean imposes two constraints on recursive types: the types of a `mutual` block must all have the
//! same parameters, and recursive occurrences can only be nested inside types that are already
//! defined. Generic types that belong to a recursive group (e.g. `RegionBinder<T>`, which contains
//! trait clauses, which contain types) are therefore "lifted": we define `RegionBinder.Gen
//! (GenericParams : Type) (T : Type)` before the group, parameterized by the members of the group
//! it mentions, use `RegionBinder.Gen GenericParams T` inside the group, and define `abbrev
//! RegionBinder := RegionBinder.Gen GenericParams` after it. Similarly, aliases can't be part of a
//! `mutual` block so we expand them until they're defined.

use anyhow::{Context, Result};
use charon_lib::ast::*;
use convert_case::{Case, Casing};
use itertools::Itertools;
use petgraph::graph::DiGraph;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::fs;
use std::path::Path;

use crate::generate_ml::GenerateCtx;

/// The instances we derive for every type, in addition to `Inhabited`. Each class is derived in its
/// own file: this is much faster to compile than deriving everything along with the types, and
/// lets the files be compiled in parallel.
const DERIVED_CLASSES: &[&str] = &["Repr", "BEq", "Hashable"];

/// Types that are ambiguous because they're defined in both `unstructured` and `structured`. We
/// prefix them with the corresponding namespace.
const AMBIGUOUS_TYPES: &[(&str, &str)] = &[
    ("charon_lib::ast::bodies::unstructured::Statement", "Ullbc"),
    (
        "charon_lib::ast::bodies::unstructured::StatementKind",
        "Ullbc",
    ),
    ("charon_lib::ast::bodies::unstructured::BlockData", "Ullbc"),
    ("charon_lib::ast::bodies::unstructured::BlockId", "Ullbc"),
    ("charon_lib::ast::bodies::structured::Statement", "Llbc"),
    ("charon_lib::ast::bodies::structured::StatementKind", "Llbc"),
    ("charon_lib::ast::bodies::structured::Block", "Llbc"),
    ("charon_lib::ast::bodies::structured::BlockId", "Llbc"),
];

/// Types that don't appear in the serialized output.
const HIDDEN_TYPES: &[&str] = &[
    "InternalBitFlags",
    "charon_lib::ast::type_level::type_info::TypeFlags",
    "charon_lib::ast::type_level::type_info::TypeInfo",
    "charon_lib::ast::type_level::type_info::WithCachedTypeInfo",
    "charon_lib::utils::hash_cons::HashConsed",
    "charon_lib::ids::index_vec::IndexVec",
    "charon_lib::ids::index_map::IndexMap",
];

/// Types that are deduplicated in the serialized output, apart from hash-consed ones (which we
/// detect automatically).
const DEDUPLICATED_TYPES: &[&str] = &["Span"];

/// Lean doesn't support polymorphic recursion, e.g. `RegionBinder<T>` containing
/// `RegionBinder<OutlivesPred>`. We instead generate a monomorphic copy of such instances; this
/// gives their names.
const INSTANCE_NAMES: &[(&str, &str)] = &[("RegionBinder<OutlivesPred>", "PolyOutlivesPred")];

/// How we represent a Rust type in Lean.
#[derive(Clone)]
enum DeclKind<'a> {
    /// A strongly-typed index, represented as a structure that wraps a `Nat`.
    Id,
    /// A type represented as another type, e.g. type aliases and newtypes.
    Alias(Ty),
    Struct(Vec<LeanField<'a>>),
    Enum(Vec<&'a Variant>),
}

#[derive(Clone)]
struct LeanField<'a> {
    /// The Lean name of the field.
    name: String,
    ty: Ty,
    attr_info: Option<&'a AttrInfo>,
}

impl DeclKind<'_> {
    /// The types this mentions.
    fn tys(&self) -> Vec<&Ty> {
        match self {
            DeclKind::Id => vec![],
            DeclKind::Alias(ty) => vec![ty],
            DeclKind::Struct(fields) => fields.iter().map(|f| &f.ty).collect(),
            DeclKind::Enum(variants) => variants
                .iter()
                .flat_map(|v| &v.fields)
                .map(|f| &f.ty)
                .collect(),
        }
    }
}

struct Decl<'a> {
    tdecl: &'a TypeDecl,
    /// The Lean name of the type.
    name: String,
    kind: DeclKind<'a>,
    /// Whether this type is deduplicated in the serialized output.
    dedup: bool,
    /// The names of the type parameters.
    params: Vec<String>,
    /// For monomorphic instances of generic types (see `INSTANCE_NAMES`), the type arguments.
    args: Vec<Ty>,
}

/// Where we're generating code.
#[derive(Clone, Copy)]
enum Scope {
    Normal,
    /// In the definition of a lifted generic type of that group, where the other (non-lifted)
    /// members of the group are parameters.
    Lifted(usize),
}

struct LeanCtx<'a> {
    krate: &'a TranslatedCrate,
    decls: HashMap<TypeDeclId, Decl<'a>>,
    /// The monomorphic instances of generic types, by generic type and type arguments.
    instances: HashMap<(TypeDeclId, Vec<Ty>), TypeDeclId>,
    /// The recursive group each type belongs to, if any.
    group_of: HashMap<TypeDeclId, usize>,
    /// For each lifted generic type, the members of its group it is parameterized by.
    lifted: HashMap<TypeDeclId, Vec<TypeDeclId>>,
    /// The types that can be referred to by name, because they're already defined or are being
    /// defined in the current `mutual` block.
    defined: HashSet<TypeDeclId>,
}

fn lean_ident(name: &str) -> String {
    const KEYWORDS: &[&str] = &[
        "abbrev",
        "at",
        "attribute",
        "axiom",
        "break",
        "by",
        "calc",
        "catch",
        "class",
        "continue",
        "def",
        "deriving",
        "do",
        "else",
        "end",
        "example",
        "export",
        "extends",
        "finally",
        "for",
        "from",
        "fun",
        "have",
        "if",
        "import",
        "in",
        "include",
        "inductive",
        "instance",
        "let",
        "local",
        "macro",
        "match",
        "meta",
        "module",
        "mut",
        "mutual",
        "namespace",
        "nomatch",
        "nofun",
        "notation",
        "omit",
        "opaque",
        "open",
        "partial",
        "private",
        "Prop",
        "protected",
        "public",
        "return",
        "section",
        "show",
        "Sort",
        "structure",
        "suffices",
        "syntax",
        "then",
        "theorem",
        "try",
        "Type",
        "universe",
        "unless",
        "unsafe",
        "variable",
        "where",
        "with",
    ];
    if KEYWORDS.contains(&name) {
        format!("«{name}»")
    } else {
        name.to_string()
    }
}

/// Wrap a type or term in parentheses if it is not atomic.
fn paren(s: String) -> String {
    if s.contains(' ') { format!("({s})") } else { s }
}

/// Apply `head` to `args`.
fn app(head: impl Into<String>, args: impl IntoIterator<Item = String>) -> String {
    let mut out = head.into();
    for arg in args {
        out.push(' ');
        out.push_str(&paren(arg));
    }
    out
}

/// Make a doc comment, indented with `indent`, or nothing if there are no docs.
fn doc_comment(doc: &str, indent: &str) -> String {
    let doc = doc.trim_end();
    if doc.trim().is_empty() {
        return String::new();
    }
    // Remove the space that usually follows `///`.
    let doc = doc
        .lines()
        .map(|line| line.strip_prefix(' ').unwrap_or(line))
        .join("\n")
        .replace("-/", "- /")
        .replace("/-", "/ -");
    if doc.contains('\n') {
        let doc = doc
            .lines()
            .map(|line| {
                if line.is_empty() {
                    String::new()
                } else {
                    format!("{indent}{line}")
                }
            })
            .join("\n");
        format!("{indent}/--\n{doc}\n{indent}-/\n")
    } else {
        format!("{indent}/-- {doc} -/\n")
    }
}

fn doc_of(attr_info: &AttrInfo) -> String {
    attr_info
        .attributes
        .iter()
        .filter_map(|a| a.as_doc_comment())
        .join("\n")
}

/// The name of the deduplication table for this type.
fn dedup_table(name: &str) -> String {
    name.to_case(Case::Camel)
}

/// The name of the variable that stands for that type, e.g. in lifted definitions.
fn var_name(name: &str) -> String {
    name.replace('.', "_")
}

impl<'a> LeanCtx<'a> {
    fn new(gen_ctx: &GenerateCtx<'a>) -> Result<Self> {
        let krate = gen_ctx.crate_data;
        let mut ids = gen_ctx.children_of("TranslatedCrate");
        for name in HIDDEN_TYPES {
            ids.remove(&gen_ctx.id_from_name(name));
        }
        let ambiguous: HashMap<TypeDeclId, &str> = AMBIGUOUS_TYPES
            .iter()
            .map(|(name, ns)| (gen_ctx.id_from_name(name), *ns))
            .collect();
        let dedup: HashSet<TypeDeclId> = DEDUPLICATED_TYPES
            .iter()
            .map(|name| gen_ctx.id_from_name(name))
            .collect();
        let is_hash_consed = |ty: &Ty| {
            ty.as_adt().is_some_and(|tref| {
                krate.item_name(tref.id).debug_repr(krate)
                    == "charon_lib::utils::hash_cons::HashConsed"
            })
        };

        let mut decls = HashMap::new();
        for id in ids {
            let tdecl = &krate.type_decls[id];
            let short_name = tdecl.item_meta.name.short_str().unwrap();
            let name = match ambiguous.get(&id) {
                Some(ns) => format!("{ns}.{short_name}"),
                None => short_name.to_string(),
            };
            let mut dedup = dedup.contains(&id);
            let kind = match &tdecl.kind {
                TypeDeclKind::Struct(fields) if fields.len() == 1 && fields[0].name == "_raw" => {
                    DeclKind::Id
                }
                TypeDeclKind::Struct(fields)
                    if fields.len() == 1
                        && (fields[0].is_positional
                            || tdecl
                                .item_meta
                                .attr_info
                                .attributes
                                .iter()
                                .any(|a| a.is_transparent())) =>
                {
                    let ty = &fields[0].ty;
                    if is_hash_consed(ty) {
                        dedup = true;
                    }
                    // Hash-consed constant expressions contain a pair; we give names to its
                    // components.
                    if name == "ConstantExpr" {
                        let mut ty = ty;
                        while let Some(tref) = ty.as_adt()
                            && tref.as_builtin().is_none()
                        {
                            ty = &tref.generics.types[0];
                        }
                        let [kind_ty, ty_ty] = ty.as_adt().unwrap().generics.types.as_raw_slice()
                        else {
                            panic!("unexpected definition of `ConstantExpr`")
                        };
                        let field = |name: &str, ty: &Ty| LeanField {
                            name: name.to_string(),
                            ty: ty.clone(),
                            attr_info: None,
                        };
                        DeclKind::Struct(vec![field("kind", kind_ty), field("ty", ty_ty)])
                    } else {
                        DeclKind::Alias(ty.clone())
                    }
                }
                TypeDeclKind::Alias(ty) => DeclKind::Alias(ty.clone()),
                TypeDeclKind::Struct(fields) => DeclKind::Struct(
                    fields
                        .iter()
                        .enumerate()
                        .map(|(i, f)| LeanField {
                            name: if f.is_positional {
                                format!("_{i}")
                            } else {
                                lean_ident(&f.name)
                            },
                            ty: f.ty.clone(),
                            attr_info: Some(&f.attr_info),
                        })
                        .collect(),
                ),
                TypeDeclKind::Enum(variants) => DeclKind::Enum(variants.iter().collect()),
                TypeDeclKind::Union(..) | TypeDeclKind::Opaque | TypeDeclKind::Error(_) => {
                    panic!("unsupported type declaration: {name}")
                }
            };
            let params = tdecl
                .generics
                .types
                .iter()
                .map(|p| p.name.clone())
                .collect();
            decls.insert(
                id,
                Decl {
                    tdecl,
                    name,
                    kind,
                    dedup,
                    params,
                    args: vec![],
                },
            );
        }

        // Find the instances of generic types involved in polymorphic recursion, and replace them
        // with monomorphic copies.
        let mut instances = HashMap::new();
        let mut new_decls = vec![];
        let generic_decls = decls.values().filter(|d| !d.params.is_empty());
        for decl in generic_decls.sorted_by_key(|d| &d.name) {
            for ty in decl.kind.tys() {
                ty.dyn_visit(|tref: &TypeDeclRef| {
                    let args = tref.generics.types.as_raw_slice();
                    let is_identity = args.iter().enumerate().all(|(i, ty)| {
                        matches!(ty.kind(), TyKind::TypeVar(DeBruijnVar::Free(id)) if id.index() == i)
                    });
                    let key = (tref.id, args.to_vec());
                    if tref.id != decl.tdecl.def_id || is_identity || instances.contains_key(&key) {
                        return;
                    }
                    let rust_name = format!(
                        "{}<{}>",
                        decl.tdecl.item_meta.name.short_str().unwrap(),
                        args.iter()
                            .map(|ty| match ty.kind() {
                                TyKind::Adt(tref) => krate.item_name(tref.id).short_str().unwrap(),
                                _ => panic!("unsupported polymorphic recursion in `{}`", decl.name),
                            })
                            .join(", ")
                    );
                    let Some((_, name)) = INSTANCE_NAMES.iter().find(|(n, _)| *n == rust_name)
                    else {
                        panic!("polymorphic recursion: name `{rust_name}` in `INSTANCE_NAMES`")
                    };
                    let id = TypeDeclId::from_usize(krate.type_decls.slot_count() + new_decls.len());
                    instances.insert(key, id);
                    let instance = Decl {
                        name: name.to_string(),
                        kind: decl.kind.clone(),
                        params: vec![],
                        args: args.to_vec(),
                        ..*decl
                    };
                    new_decls.push((id, instance));
                });
            }
        }
        decls.extend(new_decls);

        // Types with the same name, e.g. our `InlineAttr` and rustc's, are disambiguated using
        // their `charon::rename` attribute.
        let names = decls.values().map(|d| d.name.clone()).counts();
        for decl in decls.values_mut() {
            if names[&decl.name] > 1
                && let Some(rename) = &decl.tdecl.item_meta.attr_info.rename
            {
                decl.name = rename.clone();
            }
        }
        let names = decls.values().map(|d| &d.name).counts();
        if let Some((name, _)) = names.into_iter().find(|(_, n)| *n > 1) {
            anyhow::bail!("ambiguous type name `{name}`; add it to `AMBIGUOUS_TYPES`");
        }

        Ok(LeanCtx {
            krate,
            decls,
            instances,
            group_of: HashMap::new(),
            lifted: HashMap::new(),
            defined: HashSet::new(),
        })
    }

    /// The generated type that `tref` refers to, along with the type arguments to apply it to.
    fn resolve<'b>(&self, tref: &'b TypeDeclRef) -> (TypeDeclId, &'b [Ty]) {
        let args = tref.generics.types.as_raw_slice();
        match self.instances.get(&(tref.id, args.to_vec())) {
            Some(&id) => (id, &[]),
            None => (tref.id, args),
        }
    }

    /// The generated types referenced by this declaration.
    fn refs_of(&self, decl: &Decl) -> HashSet<TypeDeclId> {
        fn visit(ctx: &LeanCtx, ty: &Ty, args: &[Ty], refs: &mut HashSet<TypeDeclId>) {
            match ty.kind() {
                TyKind::Adt(tref) => {
                    let (id, tys) = ctx.resolve(tref);
                    if ctx.decls.contains_key(&id) {
                        refs.insert(id);
                    }
                    for ty in tys {
                        visit(ctx, ty, args, refs);
                    }
                }
                TyKind::TypeVar(DeBruijnVar::Free(id)) if let Some(arg) = args.get(id.index()) => {
                    visit(ctx, arg, &[], refs)
                }
                _ => {}
            }
        }
        let mut refs = HashSet::new();
        for ty in decl.kind.tys() {
            visit(self, ty, &decl.args, &mut refs);
        }
        refs
    }

    /// The Lean types that the type variables of `decl` stand for.
    fn type_args(&self, decl: &Decl, scope: Scope) -> Vec<String> {
        if decl.args.is_empty() {
            decl.params.clone()
        } else {
            decl.args
                .iter()
                .map(|ty| self.ty_to_lean(ty, scope, &[]))
                .collect()
        }
    }

    /// The deserializers for the type variables of `decl`.
    fn deserializer_args(&self, decl: &Decl, scope: Scope) -> Vec<String> {
        if decl.args.is_empty() {
            decl.params.iter().map(|p| format!("dec_{p}")).collect()
        } else {
            decl.args
                .iter()
                .map(|ty| self.deserializer(ty, scope, &[]))
                .collect()
        }
    }

    fn sorted_ids(&self, ids: impl IntoIterator<Item = TypeDeclId>) -> Vec<TypeDeclId> {
        ids.into_iter()
            .sorted_by_key(|id| &self.decls[id].name)
            .collect()
    }

    /// Group the types into strongly-connected components, in dependency order.
    fn compute_groups(&mut self) -> Vec<Vec<TypeDeclId>> {
        let mut graph = DiGraph::<TypeDeclId, ()>::new();
        let ids = self.sorted_ids(self.decls.keys().copied());
        let nodes: HashMap<TypeDeclId, _> =
            ids.iter().map(|&id| (id, graph.add_node(id))).collect();
        for &id in &ids {
            for dep in self.sorted_ids(self.refs_of(&self.decls[&id])) {
                graph.add_edge(nodes[&id], nodes[&dep], ());
            }
        }
        // `tarjan_scc` returns the components in reverse topological order, i.e. dependencies
        // first.
        let groups = petgraph::algo::tarjan_scc(&graph)
            .into_iter()
            .map(|scc| self.sorted_ids(scc.into_iter().map(|n| graph[n])))
            .collect_vec();
        for (i, group) in groups.iter().enumerate() {
            let recursive =
                group.len() > 1 || self.refs_of(&self.decls[&group[0]]).contains(&group[0]);
            if recursive {
                for &id in group {
                    self.group_of.insert(id, i);
                }
            }
        }
        groups
    }

    /// Whether the type `id`, which belongs to a recursive group, is a parameter of the lifted
    /// types of that group. Other members are either lifted themselves or expanded aliases.
    /// Deduplicated aliases (e.g. `Ty`) can't be expanded because their deserializer is special.
    fn is_group_param(&self, id: TypeDeclId) -> bool {
        let decl = &self.decls[&id];
        decl.params.is_empty() && (!matches!(decl.kind, DeclKind::Alias(_)) || decl.dedup)
    }

    /// The members of `group` that `id` mentions, seeing through aliases and lifted types.
    fn group_params_of(
        &self,
        id: TypeDeclId,
        group: usize,
        seen: &mut Vec<TypeDeclId>,
    ) -> Vec<TypeDeclId> {
        if seen.contains(&id) {
            panic!(
                "cyclic lifted generic types: {}",
                seen.iter().map(|id| &self.decls[id].name).join(", ")
            )
        }
        seen.push(id);
        let mut params = HashSet::new();
        for dep in self.refs_of(&self.decls[&id]) {
            if self.group_of.get(&dep) != Some(&group) {
                continue;
            }
            if self.is_group_param(dep) {
                params.insert(dep);
            } else {
                params.extend(self.group_params_of(dep, group, seen));
            }
        }
        seen.pop();
        self.sorted_ids(params)
    }

    /// The lifted types of `group`, sorted so that each comes after the lifted types it mentions.
    fn lifted_order(&self, group: usize, members: &[TypeDeclId]) -> Vec<TypeDeclId> {
        // Visits the lifted types and expanded aliases of the group.
        fn visit(ctx: &LeanCtx, id: TypeDeclId, group: usize, order: &mut Vec<TypeDeclId>) {
            if order.contains(&id) {
                return;
            }
            for dep in ctx.sorted_ids(ctx.refs_of(&ctx.decls[&id])) {
                if ctx.group_of.get(&dep) == Some(&group) && !ctx.is_group_param(dep) {
                    visit(ctx, dep, group, order);
                }
            }
            if ctx.lifted.contains_key(&id) {
                order.push(id);
            }
        }
        let mut order = vec![];
        for &id in members {
            if self.lifted.contains_key(&id) {
                visit(self, id, group, &mut order);
            }
        }
        order
    }

    /// The Lean type and deserializer for a scalar type.
    fn scalar_to_lean(ty: &ScalarTy) -> (&'static str, &'static str) {
        match ty {
            ScalarTy::Bool => ("Bool", "Postcard.bool"),
            ScalarTy::Char => ("Char", "Postcard.char"),
            ScalarTy::Integer(IntegerTy::Signed(int_ty)) => match int_ty {
                IntTy::I8 => ("Int8", "Postcard.i8"),
                IntTy::I16 => ("Int16", "Postcard.i16"),
                IntTy::I32 => ("Int32", "Postcard.i32"),
                IntTy::I64 => ("Int64", "Postcard.i64"),
                IntTy::Isize => ("Int", "Postcard.int"),
                IntTy::I128 => ("Int", "Postcard.i128"),
            },
            ScalarTy::Integer(IntegerTy::Unsigned(uint_ty)) => match uint_ty {
                UIntTy::U8 => ("UInt8", "Postcard.u8"),
                UIntTy::U16 => ("UInt16", "Postcard.u16"),
                UIntTy::U32 => ("UInt32", "Postcard.u32"),
                UIntTy::U64 => ("UInt64", "Postcard.u64"),
                UIntTy::Usize => ("Nat", "Postcard.nat"),
                UIntTy::U128 => ("Nat", "Postcard.u128"),
            },
            ScalarTy::Float(FloatTy::F32) => ("Float32", "Postcard.f32"),
            ScalarTy::Float(FloatTy::F64) => ("Float", "Postcard.f64"),
            ScalarTy::Float(_) => unimplemented!("{ty:?}"),
        }
    }

    /// The type arguments of a non-generated type that matter to us: we ignore the hasher of
    /// `indexmap::IndexMap`.
    fn foreign_type_args<'b>(&self, tref: &'b TypeDeclRef) -> &'b [Ty] {
        let args = tref.generics.types.as_raw_slice();
        if tref.as_builtin().is_none()
            && self.krate.item_name(tref.id).debug_repr(self.krate) == "indexmap::map::IndexMap"
        {
            &args[..2]
        } else {
            args
        }
    }

    /// Whether `ty` is known to be inhabited, assuming that among the members of the current
    /// `mutual` block (`block`), only those in `inhabited` are. `args` gives the types that the
    /// type variables stand for.
    fn is_inhabited(
        &self,
        ty: &Ty,
        args: &[Ty],
        block: &HashSet<TypeDeclId>,
        inhabited: &HashSet<TypeDeclId>,
    ) -> bool {
        let all_inhabited = |tys: &[Ty]| {
            tys.iter()
                .all(|ty| self.is_inhabited(ty, args, block, inhabited))
        };
        match ty.kind() {
            TyKind::TypeVar(DeBruijnVar::Free(id)) => args
                .get(id.index())
                .is_none_or(|arg| self.is_inhabited(arg, &[], block, inhabited)),
            TyKind::Adt(tref)
                if tref.as_builtin().is_none() && self.decls.contains_key(&tref.id) =>
            {
                let (id, tys) = self.resolve(tref);
                self.is_decl_inhabited(id, block, inhabited) && all_inhabited(tys)
            }
            TyKind::Adt(tref) => {
                // Containers are always inhabited.
                let is_container = tref.as_builtin().is_none()
                    && matches!(
                        self.krate
                            .item_name(tref.id)
                            .debug_repr(self.krate)
                            .as_str(),
                        "alloc::vec::Vec"
                            | "core::option::Option"
                            | "charon_lib::ids::index_vec::IndexVec"
                            | "charon_lib::ids::index_map::IndexMap"
                            | "indexmap::map::IndexMap"
                    );
                is_container || all_inhabited(self.foreign_type_args(tref))
            }
            _ => true,
        }
    }

    fn is_decl_inhabited(
        &self,
        id: TypeDeclId,
        block: &HashSet<TypeDeclId>,
        inhabited: &HashSet<TypeDeclId>,
    ) -> bool {
        let decl = &self.decls[&id];
        if block.contains(&id) {
            inhabited.contains(&id)
        } else if let Some(group_params) = self.lifted.get(&id) {
            // The derived instance requires all the parameters to be inhabited.
            group_params
                .iter()
                .all(|&p| self.is_decl_inhabited(p, block, inhabited))
        } else if let DeclKind::Alias(ty) = &decl.kind
            && !self.defined.contains(&id)
        {
            self.is_inhabited(ty, &decl.args, block, inhabited)
        } else {
            true
        }
    }

    /// Sort the members of a `mutual` block so that each can derive `Inhabited` from the instances
    /// of the previous ones. Lean can't derive these instances for a whole `mutual` block at once.
    fn inhabited_order(&self, block: &[TypeDeclId]) -> Vec<TypeDeclId> {
        let block_set: HashSet<_> = block.iter().copied().collect();
        let mut inhabited = HashSet::new();
        let mut order = vec![];
        while order.len() < block.len() {
            let next = block.iter().copied().find(|id| {
                let decl = &self.decls[id];
                let is_inhabited = |ty| self.is_inhabited(ty, &decl.args, &block_set, &inhabited);
                !inhabited.contains(id)
                    && match &decl.kind {
                        DeclKind::Struct(fields) => fields.iter().all(|f| is_inhabited(&f.ty)),
                        DeclKind::Enum(variants) => variants
                            .iter()
                            .any(|v| v.fields.iter().all(|f| is_inhabited(&f.ty))),
                        DeclKind::Id | DeclKind::Alias(_) => unreachable!(),
                    }
            });
            let Some(next) = next else {
                panic!(
                    "can't find `Inhabited` instances for: {}",
                    block
                        .iter()
                        .filter(|id| !inhabited.contains(id))
                        .map(|id| &self.decls[id].name)
                        .join(", ")
                )
            };
            inhabited.insert(next);
            order.push(next);
        }
        order
    }

    /// Convert a type to Lean. `params` gives the Lean types to use for the type variables.
    fn ty_to_lean(&self, ty: &Ty, scope: Scope, params: &[String]) -> String {
        match ty.kind() {
            TyKind::Scalar(scalar) => Self::scalar_to_lean(scalar).0.to_string(),
            TyKind::TypeVar(DeBruijnVar::Free(id)) => params[id.index()].clone(),
            TyKind::Adt(tref)
                if tref.as_builtin().is_none() && self.decls.contains_key(&tref.id) =>
            {
                let (id, tys) = self.resolve(tref);
                let args = tys.iter().map(|ty| self.ty_to_lean(ty, scope, params));
                self.decl_ref(id, args.collect(), scope)
            }
            TyKind::Adt(tref) => {
                let mut args = self
                    .foreign_type_args(tref)
                    .iter()
                    .map(|ty| self.ty_to_lean(ty, scope, params))
                    .collect_vec();
                match tref.as_builtin() {
                    Some(BuiltinAdt::Box) => args.remove(0),
                    Some(BuiltinAdt::Tuple) if args.is_empty() => "Unit".to_string(),
                    Some(BuiltinAdt::Tuple) => args.into_iter().map(paren).join(" × "),
                    Some(BuiltinAdt::Str) => unimplemented!("{ty:?}"),
                    None => match self
                        .krate
                        .item_name(tref.id)
                        .debug_repr(self.krate)
                        .as_str()
                    {
                        "alloc::vec::Vec" => app("Array", args),
                        "core::option::Option" => app("Option", args),
                        "alloc::string::String" | "ustr::Ustr" | "std::path::PathBuf" => {
                            "String".to_string()
                        }
                        "charon_lib::utils::hash_cons::HashConsed"
                        | "charon_lib::ast::type_level::type_info::WithCachedTypeInfo" => {
                            args.remove(0)
                        }
                        "core::ops::range::RangeInclusive" => app("RangeInclusive", args),
                        "charon_lib::ids::index_vec::IndexVec" => app("IndexVec", args),
                        "charon_lib::ids::index_map::IndexMap" => app("IndexMap", args),
                        "indexmap::map::IndexMap" => {
                            format!(
                                "Array ({} × {})",
                                paren(args.remove(0)),
                                paren(args.remove(0))
                            )
                        }
                        name => panic!("unsupported type `{name}`"),
                    },
                }
            }
            _ => unimplemented!("{ty:?}"),
        }
    }

    /// Refer to the generated type `id` applied to `args`.
    fn decl_ref(&self, id: TypeDeclId, args: Vec<String>, scope: Scope) -> String {
        let decl = &self.decls[&id];
        let in_lifted_group =
            matches!(scope, Scope::Lifted(g) if self.group_of.get(&id) == Some(&g));
        if in_lifted_group && self.is_group_param(id) {
            var_name(&decl.name)
        } else if self.defined.contains(&id) && !in_lifted_group {
            app(&decl.name, args)
        } else if let Some(group_params) = self.lifted.get(&id) {
            let group_args = group_params
                .iter()
                .map(|&p| self.decl_ref(p, vec![], scope));
            app(format!("{}.Gen", decl.name), group_args.chain(args))
        } else if let DeclKind::Alias(ty) = &decl.kind {
            self.ty_to_lean(ty, scope, &args)
        } else {
            panic!("type `{}` is used before being defined", decl.name)
        }
    }

    /// The deserializer for a type. `params` gives the deserializers to use for the type variables.
    fn deserializer(&self, ty: &Ty, scope: Scope, params: &[String]) -> String {
        match ty.kind() {
            TyKind::Scalar(scalar) => Self::scalar_to_lean(scalar).1.to_string(),
            TyKind::TypeVar(DeBruijnVar::Free(id)) => params[id.index()].clone(),
            TyKind::Adt(tref)
                if tref.as_builtin().is_none() && self.decls.contains_key(&tref.id) =>
            {
                let (id, tys) = self.resolve(tref);
                let args = tys.iter().map(|ty| self.deserializer(ty, scope, params));
                self.decl_deserializer(id, args.collect(), scope)
            }
            TyKind::Adt(tref) => {
                let mut args = self
                    .foreign_type_args(tref)
                    .iter()
                    .map(|ty| self.deserializer(ty, scope, params))
                    .collect_vec();
                match tref.as_builtin() {
                    Some(BuiltinAdt::Box) => args.remove(0),
                    Some(BuiltinAdt::Tuple) => match args.pop() {
                        None => "(pure ())".to_string(),
                        Some(last) => args
                            .into_iter()
                            .rfold(last, |acc, arg| app("Postcard.pair", [arg, acc])),
                    },
                    Some(BuiltinAdt::Str) => unimplemented!("{ty:?}"),
                    None => match self
                        .krate
                        .item_name(tref.id)
                        .debug_repr(self.krate)
                        .as_str()
                    {
                        "alloc::vec::Vec" => app("Postcard.array", args),
                        "core::option::Option" => app("Postcard.option", args),
                        "alloc::string::String" | "ustr::Ustr" | "std::path::PathBuf" => {
                            "Postcard.string".to_string()
                        }
                        "charon_lib::utils::hash_cons::HashConsed"
                        | "charon_lib::ast::type_level::type_info::WithCachedTypeInfo" => {
                            args.remove(0)
                        }
                        "core::ops::range::RangeInclusive" => app("Postcard.rangeInclusive", args),
                        "charon_lib::ids::index_vec::IndexVec" => {
                            app("Postcard.indexVec", [args.remove(1)])
                        }
                        "charon_lib::ids::index_map::IndexMap" => {
                            app("Postcard.indexMap", [args.remove(1)])
                        }
                        "indexmap::map::IndexMap" => {
                            app("Postcard.array", [app("Postcard.pair", args)])
                        }
                        name => panic!("unsupported type `{name}`"),
                    },
                }
            }
            _ => unimplemented!("{ty:?}"),
        }
    }

    fn decl_deserializer(&self, id: TypeDeclId, args: Vec<String>, scope: Scope) -> String {
        let decl = &self.decls[&id];
        match scope {
            Scope::Lifted(g) if self.group_of.get(&id) == Some(&g) => {
                if self.is_group_param(id) {
                    format!("dec_{}", var_name(&decl.name))
                } else if let Some(group_params) = self.lifted.get(&id) {
                    let group_args = group_params
                        .iter()
                        .map(|&p| self.decl_deserializer(p, vec![], scope));
                    app(
                        format!("{}.Gen.ofPostcard", decl.name),
                        group_args.chain(args),
                    )
                } else if let DeclKind::Alias(ty) = &decl.kind {
                    self.deserializer(ty, scope, &args)
                } else {
                    unreachable!()
                }
            }
            _ => app(format!("{}.ofPostcard", decl.name), args),
        }
    }

    fn type_params(params: &[String]) -> String {
        params.iter().map(|p| format!(" ({p} : Type)")).join("")
    }

    /// Generate the definition of a structure or inductive type.
    fn type_definition(
        &self,
        decl: &Decl,
        name: &str,
        group_params: &[String],
        scope: Scope,
    ) -> String {
        let mut doc = doc_of(&decl.tdecl.item_meta.attr_info);
        if !decl.args.is_empty() {
            let generic = decl.tdecl.item_meta.name.short_str().unwrap();
            let _ = write!(
                doc,
                "\n\nThis is a copy of `{generic}` specialized to the arguments \
                `{}`, because Lean doesn't support polymorphic recursion.",
                self.type_args(decl, scope).join(", ")
            );
        }
        let mut out = doc_comment(&doc, "");
        let all_params = group_params
            .iter()
            .chain(&decl.params)
            .cloned()
            .collect_vec();
        let params = Self::type_params(&all_params);
        let type_args = self.type_args(decl, scope);
        match &decl.kind {
            DeclKind::Id => {
                let _ = writeln!(out, "structure {name} where\n  index : Nat");
            }
            DeclKind::Alias(_) => unreachable!(),
            DeclKind::Struct(fields) => {
                let _ = writeln!(out, "structure {name}{params} where");
                for f in fields {
                    if let Some(attr_info) = f.attr_info {
                        out += &doc_comment(&doc_of(attr_info), "  ");
                    }
                    let ty = self.ty_to_lean(&f.ty, scope, &type_args);
                    let _ = writeln!(out, "  {} : {ty}", f.name);
                }
            }
            DeclKind::Enum(variants) => {
                let _ = writeln!(out, "inductive {name}{params} where");
                for v in variants {
                    let mut doc = doc_of(&v.attr_info);
                    if !v.fields.is_empty() && v.fields.iter().all(|f| !f.is_positional) {
                        let field_docs = v
                            .fields
                            .iter()
                            .map(|f| {
                                let fdoc = doc_of(&f.attr_info);
                                if fdoc.is_empty() {
                                    format!("\n- `{}`", f.name)
                                } else {
                                    format!("\n- `{}`: {}", f.name, fdoc.trim())
                                }
                            })
                            .join("");
                        if v.fields.iter().any(|f| !doc_of(&f.attr_info).is_empty()) {
                            let _ = write!(doc, "\n\nFields:{field_docs}");
                        }
                    }
                    out += &doc_comment(&doc, "  ");
                    let _ = write!(out, "  | {}", lean_ident(&v.name));
                    for (i, f) in v.fields.iter().enumerate() {
                        let fname = if f.is_positional {
                            format!("_{i}")
                        } else {
                            lean_ident(&f.name)
                        };
                        let ty = self.ty_to_lean(&f.ty, scope, &type_args);
                        let _ = write!(out, " ({fname} : {ty})");
                    }
                    out += "\n";
                }
            }
        }
        out
    }

    fn alias_definition(&self, decl: &Decl) -> String {
        let DeclKind::Alias(ty) = &decl.kind else {
            unreachable!()
        };
        let doc = doc_comment(&doc_of(&decl.tdecl.item_meta.attr_info), "");
        let params = Self::type_params(&decl.params);
        let ty = self.ty_to_lean(ty, Scope::Normal, &decl.params);
        format!("{doc}abbrev {}{params} := {ty}\n", decl.name)
    }

    /// Returns the definitions, along with the types to derive instances for (as lists of
    /// mutually-recursive types), in order.
    fn generate_types(&mut self, groups: &[Vec<TypeDeclId>]) -> (String, Vec<String>) {
        let mut out = String::new();
        let mut derive_for = vec![];
        for (i, group) in groups.iter().enumerate() {
            if !self.group_of.contains_key(&group[0]) {
                // Not recursive.
                let id = group[0];
                let decl = &self.decls[&id];
                let def = match &decl.kind {
                    DeclKind::Alias(_) => self.alias_definition(decl),
                    DeclKind::Id => {
                        let mut def = self.type_definition(decl, &decl.name, &[], Scope::Normal);
                        let _ = write!(
                            def,
                            "  deriving Inhabited, Ord\n\ninstance : Idx {0} := ⟨{0}.index, {0}.mk⟩\n",
                            decl.name
                        );
                        derive_for.push(decl.name.clone());
                        def
                    }
                    _ => {
                        let mut def = self.type_definition(decl, &decl.name, &[], Scope::Normal);
                        let _ = writeln!(def, "  deriving Inhabited");
                        derive_for.push(decl.name.clone());
                        def
                    }
                };
                let _ = writeln!(out, "{def}");
                self.defined.insert(id);
                continue;
            }

            let (generic, monomorphic): (Vec<_>, Vec<_>) = group
                .iter()
                .copied()
                .filter(|id| !matches!(self.decls[id].kind, DeclKind::Alias(_)))
                .partition(|id| !self.decls[id].params.is_empty());
            let aliases = group
                .iter()
                .copied()
                .filter(|id| matches!(self.decls[id].kind, DeclKind::Alias(_)))
                .collect_vec();
            assert!(
                !monomorphic.is_empty(),
                "recursive group with only generic types: {}",
                group.iter().map(|id| &self.decls[id].name).join(", ")
            );

            // Lift the generic types, in dependency order.
            for &id in &generic {
                let group_params = self.group_params_of(id, i, &mut vec![]);
                self.lifted.insert(id, group_params);
            }
            let lifted_order = self.lifted_order(i, group);
            for &id in &lifted_order {
                let decl = &self.decls[&id];
                let group_params = self.lifted[&id]
                    .iter()
                    .map(|p| var_name(&self.decls[p].name))
                    .collect_vec();
                let name = format!("{}.Gen", decl.name);
                let mut def = self.type_definition(decl, &name, &group_params, Scope::Lifted(i));
                let _ = writeln!(def, "  deriving Inhabited");
                let _ = writeln!(out, "{def}");
                derive_for.push(name);
            }

            // The mutual block itself.
            self.defined.extend(&monomorphic);
            out += "mutual\n\n";
            for &id in &monomorphic {
                let decl = &self.decls[&id];
                let def = self.type_definition(decl, &decl.name, &[], Scope::Normal);
                let _ = writeln!(out, "{def}");
            }
            out += "end\n\n";
            derive_for.push(monomorphic.iter().map(|id| &self.decls[id].name).join(", "));
            for id in self.inhabited_order(&monomorphic) {
                let _ = writeln!(
                    out,
                    "deriving instance Inhabited for {}",
                    self.decls[&id].name
                );
            }
            out += "\n";

            // Define the lifted types and the aliases.
            for &id in &lifted_order {
                let decl = &self.decls[&id];
                let group_args = self.lifted[&id]
                    .iter()
                    .map(|&p| self.decl_ref(p, vec![], Scope::Normal));
                let doc = doc_comment(&doc_of(&decl.tdecl.item_meta.attr_info), "");
                let def = app(format!("{}.Gen", decl.name), group_args);
                let _ = writeln!(out, "{doc}abbrev {} := {def}\n", decl.name);
                self.defined.insert(id);
            }
            for &id in &aliases {
                let def = self.alias_definition(&self.decls[&id]);
                let _ = writeln!(out, "{def}");
                self.defined.insert(id);
            }
        }
        (out, derive_for)
    }

    /// The body of the deserializer for a structure or inductive.
    fn deserializer_body(&self, decl: &Decl, constructor: &str, scope: Scope) -> String {
        let params = &self.deserializer_args(decl, scope);
        let fields_deserializer = |fields: &mut dyn Iterator<Item = &Ty>, constructor: &str| {
            let mut out = String::new();
            let mut args = vec![];
            for (i, ty) in fields.enumerate() {
                let de = self.deserializer(ty, scope, params);
                let _ = write!(out, "let x{i} ← {de}; ");
                args.push(format!("x{i}"));
            }
            format!("do {out}return {}", app(constructor, args))
        };
        match &decl.kind {
            DeclKind::Id => "return ⟨← Postcard.nat⟩".to_string(),
            DeclKind::Alias(ty) => self.deserializer(ty, scope, params),
            DeclKind::Struct(fields) => {
                let mut fields = fields.iter().map(|f| &f.ty);
                fields_deserializer(&mut fields, &format!("{constructor}.mk"))
            }
            DeclKind::Enum(variants) => {
                let mut out = "do\n    match ← Postcard.variant with\n".to_string();
                for (i, v) in variants.iter().enumerate() {
                    let mut fields = v.fields.iter().map(|f| &f.ty);
                    let constructor = format!("{constructor}.{}", lean_ident(&v.name));
                    let body = fields_deserializer(&mut fields, &constructor);
                    let _ = writeln!(out, "    | {i} => {body}");
                }
                let _ = write!(
                    out,
                    "    | n => Postcard.fail s!\"unknown variant {{n}} of `{}`\"",
                    decl.name
                );
                out
            }
        }
    }

    fn generate_deserializers(&mut self, groups: &[Vec<TypeDeclId>]) -> String {
        let mut out = String::new();
        let signature = |decl: &Decl, name: &str, group_params: &[String]| {
            let all_params = group_params
                .iter()
                .chain(&decl.params)
                .cloned()
                .collect_vec();
            let mut sig = format!("{name}.ofPostcard");
            if !all_params.is_empty() {
                let _ = write!(sig, " {{{} : Type}}", all_params.iter().join(" "));
            }
            for p in &all_params {
                let _ = write!(sig, " (dec_{p} : M {p})");
            }
            let _ = write!(sig, " : M {}", paren(app(name, all_params.iter().cloned())));
            sig
        };
        let body = |ctx: &Self, decl: &Decl, constructor: &str, scope: Scope| {
            let mut body = ctx.deserializer_body(decl, constructor, scope);
            if decl.dedup {
                let table = dedup_table(&decl.name);
                body = format!(
                    "Postcard.dedup (·.{table}) (fun t v => {{ t with {table} := v }}) <| {body}"
                );
            }
            body
        };

        for (i, group) in groups.iter().enumerate() {
            if !self.group_of.contains_key(&group[0]) {
                let decl = &self.decls[&group[0]];
                let sig = signature(decl, &decl.name, &[]);
                let body = body(self, decl, &decl.name, Scope::Normal);
                let _ = writeln!(out, "def {sig} :=\n  {body}\n");
                continue;
            }
            let members = self.sorted_ids(group.iter().copied());
            // Deserializers for the lifted types, which take the deserializers for the other
            // members of the group as parameters.
            for id in self.lifted_order(i, &members) {
                let decl = &self.decls[&id];
                let group_params = self.lifted[&id]
                    .iter()
                    .map(|p| var_name(&self.decls[p].name))
                    .collect_vec();
                let name = format!("{}.Gen", decl.name);
                let sig = signature(decl, &name, &group_params);
                let body = body(self, decl, &name, Scope::Lifted(i));
                let _ = writeln!(out, "def {sig} :=\n  {body}\n");
            }

            out += "mutual\n\n";
            for &id in &members {
                let decl = &self.decls[&id];
                let sig = signature(decl, &decl.name, &[]);
                let body = if let Some(group_params) = self.lifted.get(&id) {
                    let group_args = group_params
                        .iter()
                        .map(|&p| self.decl_deserializer(p, vec![], Scope::Normal));
                    let args = self.deserializer_args(decl, Scope::Normal);
                    app(
                        format!("{}.Gen.ofPostcard", decl.name),
                        group_args.chain(args),
                    )
                } else {
                    body(self, decl, &decl.name, Scope::Normal)
                };
                let _ = writeln!(out, "partial def {sig} :=\n  {body}\n");
            }
            out += "end\n\n";
        }
        out
    }

    fn generate_dedup_tables(&self) -> String {
        let mut out = String::new();
        let dedup_decls = self
            .decls
            .values()
            .filter(|d| d.dedup)
            .sorted_by_key(|d| &d.name)
            .collect_vec();
        out += "/-- The tables of deduplicated values (see `Postcard.dedup`). -/\nstructure DedupTables where\n";
        for decl in dedup_decls {
            let _ = writeln!(
                out,
                "  {} : Array (Option {}) := #[]",
                dedup_table(&decl.name),
                decl.name
            );
        }
        out
    }
}

const HEADER: &str = "-- This file is automatically generated by `make generate-asts` in the root of the charon repository.\n-- Do not edit it by hand. The code-generation code is in `charon/src/bin/generate-asts`.\n";

pub(crate) fn generate(crate_data: &TranslatedCrate, output_dir: &Path) -> Result<()> {
    let gen_ctx = GenerateCtx::new(crate_data, &[]);
    let mut ctx = LeanCtx::new(&gen_ctx)?;
    let groups = ctx.compute_groups();

    let (types, derive_for) = ctx.generate_types(&groups);
    let ast = format!(
        "{HEADER}\nimport Charon.Basic\n\n/-! The Charon AST. -/\n\nnamespace Charon\n\n{types}end Charon\n"
    );

    let tables = ctx.generate_dedup_tables();
    let deserializers = ctx.generate_deserializers(&groups);
    let of_postcard = format!(
        "{HEADER}\nimport Charon.Generated.Ast\nimport Charon.Postcard\n\n/-! Postcard deserializers for the Charon AST. -/\n\nnamespace Charon\n\n{tables}\nabbrev M := Postcard.M DedupTables\n\n{deserializers}end Charon\n"
    );

    let mut files = vec![
        ("Ast".to_string(), ast),
        ("OfPostcard".to_string(), of_postcard),
    ];
    for class in DERIVED_CLASSES {
        let derives = derive_for
            .iter()
            .map(|tys| format!("deriving instance {class} for {tys}\n"))
            .join("");
        let contents = format!(
            "{HEADER}\nimport Charon.Generated.Ast\n\n/-! `{class}` instances for the Charon AST. -/\n\nnamespace Charon\n\n{derives}\nend Charon\n"
        );
        files.push((class.to_string(), contents));
    }

    fs::create_dir_all(output_dir)?;
    for (file, contents) in files {
        let file = format!("{file}.lean");
        let path = output_dir.join(file);
        fs::write(&path, contents)
            .with_context(|| format!("Failed to write generated file {}", path.display()))?;
    }
    Ok(())
}
