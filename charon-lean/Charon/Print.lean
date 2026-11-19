import Std.Data.HashMap
import Charon.Generated.BEq
import Charon.Generated.Hashable
import Charon.Generated.Repr

/-!
A pretty-printer for the Charon AST, modelled after the one in `charon/src/pretty`. Its output is
close to that of `charon pretty-print`, but isn't meant to match it exactly.
-/

namespace Charon

/-! Simple types. -/

def IntTy.toString : IntTy → String
  | .Isize => "isize" | .I8 => "i8" | .I16 => "i16" | .I32 => "i32" | .I64 => "i64"
  | .I128 => "i128"

def UIntTy.toString : UIntTy → String
  | .Usize => "usize" | .U8 => "u8" | .U16 => "u16" | .U32 => "u32" | .U64 => "u64"
  | .U128 => "u128"

def IntegerTy.toString : IntegerTy → String
  | .Signed ty => IntTy.toString ty
  | .Unsigned ty => UIntTy.toString ty

def FloatTy.toString : FloatTy → String
  | .F16 => "f16" | .F32 => "f32" | .F64 => "f64" | .F128 => "f128"

def ScalarTy.toString : ScalarTy → String
  | .Integer ty => IntegerTy.toString ty
  | .Float ty => FloatTy.toString ty
  | .Char => "char"
  | .Bool => "bool"

def IntegerValue.toString : IntegerValue → String
  | .Signed ty v => s!"{v}{IntTy.toString ty}"
  | .Unsigned ty v => s!"{v}{UIntTy.toString ty}"

def FloatValue.toString (v : FloatValue) : String := v.value ++ FloatTy.toString v.ty

def OverflowMode.toString : OverflowMode → String
  | .Panic => "panic" | .Wrap => "wrap" | .UB => "ub"

def BinOp.toString : BinOp → String
  | .BitXor => "^" | .BitAnd => "&" | .BitOr => "|" | .Eq => "==" | .Lt => "<" | .Le => "<="
  | .Ne => "!=" | .Ge => ">=" | .Gt => ">" | .Cmp => "cmp"
  | .Add m => s!"{m.toString}.+" | .Sub m => s!"{m.toString}.-" | .Mul m => s!"{m.toString}.*"
  | .Div m => s!"{m.toString}./" | .Rem m => s!"{m.toString}.%"
  | .Shl m => s!"{m.toString}.<<" | .Shr m => s!"{m.toString}.>>"

def NullOp.toString : NullOp → String
  | .UbChecks => "ub_checks" | .OverflowChecks => "overflow_checks"
  | .ContractChecks => "contract_checks"

def Abi.rustName : Abi → String
  | .Rust => "Rust" | .C => "C" | .Other name => name

def BuiltinPathElem.ident : BuiltinPathElem → String
  | .Tuple 0 => "unit" | .Tuple _ => "tuple" | .Str => "str" | .Closure => "closure"
  | .Use => "use" | .AnonConst => "const" | .PromotedConst => "promoted_const"
  | .ClosureAsFn => "as_fn" | .DropGlue => "drop_glue" | .VTable => "vtable"
  | .VTableMethod => "vtable_method" | .VTableDropShim => "vtable_drop_shim"
  | .IntrinsicFallback => "fallback"

def BuiltinPathElem.isRustName : BuiltinPathElem → Bool
  | .Str | .Tuple _ | .DropGlue => true
  | _ => false

def MetadataValue.toString : MetadataValue → String
  | .DynSize => "dyn_size" | .DynAlign => "dyn_align" | .SliceLength => "slice_length"

def ItemId.toPrettyString : ItemId → String
  | .«Type» id => s!"@Type{id.index}"
  | .Fun id => s!"@Fun{id.index}"
  | .Global id => s!"@Global{id.index}"
  | .TraitDecl id => s!"@TraitDecl{id.index}"
  | .TraitImpl id => s!"@TraitImpl{id.index}"

def DeBruijnVar.toString {Id : Type} [Idx Id] : DeBruijnVar Id → String
  | .Bound dbid id => s!"Bound({dbid}, {Idx.index id})"
  | .Free id => s!"Free({Idx.index id})"

/-- Approximates Rust's `char::escape_debug`, which escapes the characters that aren't printable. -/
def escapeDebug (c : Char) : String :=
  match c with
  | '\x00' => "\\0" | '\t' => "\\t" | '\r' => "\\r" | '\n' => "\\n" | '\\' => "\\\\"
  | '\'' => "\\'" | '"' => "\\\""
  | c =>
    let n := c.toNat
    let nonPrintable := n < 0x20 || (0x7f ≤ n && n ≤ 0x9f) || n == 0xad
      || (0x200b ≤ n && n ≤ 0x200f) || n == 0x2028 || n == 0x2029 || n == 0xfeff
      || (0xe000 ≤ n && n ≤ 0xf8ff) || (0xfdd0 ≤ n && n ≤ 0xfdef) || n % 0x10000 ≥ 0xfffe
      || (0xe0000 ≤ n && n ≤ 0xe0fff) || n ≥ 0xf0000
    if nonPrintable then "\\u{" ++ String.ofList (Nat.toDigits 16 n) ++ "}" else c.toString

/-! Helpers to inspect the AST. -/

def TypeDeclRef.isTuple (tref : TypeDeclRef) : Bool := tref.builtin == some .Tuple

/-- Whether this is `Ty::mk_unit()`. -/
def TyKind.isUnit : TyKind → Bool
  | .Adt tref => tref.isTuple && tref.id.index == 0 && tref.generics.types.isEmpty
  | _ => false

def Operand.ty : Operand → Ty
  | .Copy p _ | .Read p | .Move p => p.ty
  | .Const c => c.ty

def GenericArgs.hasExplicits (g : GenericArgs) : Bool :=
  !g.regions.isEmpty || !g.types.isEmpty || !g.const_generics.isEmpty

def GenericParams.hasExplicits (g : GenericParams) : Bool :=
  !g.regions.isEmpty || !g.types.isEmpty || !g.const_generics.isEmpty

def GenericParams.hasPredicates (g : GenericParams) : Bool :=
  !g.trait_clauses.isEmpty || !g.outlives.isEmpty || !g.trait_type_constraints.isEmpty

def GenericParams.isEmpty (g : GenericParams) : Bool := !g.hasExplicits && !g.hasPredicates

/-- If the switch is over a boolean, its `then` and `else` branches. -/
def SwitchData.asIf (data : SwitchData) : Option (BranchId × BranchId) := do
  let .Value scrutinee := data.scrutinee | none
  let .Scalar .Bool := scrutinee.ty | none
  let branchFor (value : Bool) : Option BranchId :=
    (data.branches.findSome? fun (case, branch) =>
      match case.kind with
      | .Bool b => if b == value then some branch else none
      | _ => none) <|> data.fallback
  return (← branchFor true, ← branchFor false)

/-- The explicit switch values, grouped by the branch they select. -/
def SwitchData.groupByBranch (data : SwitchData) (branchCount : Nat) : Array (Array ConstantExpr) :=
  data.branches.foldl (init := Array.replicate branchCount #[]) fun acc (value, branch) =>
    acc.modify branch.index (·.push value)

def DeclarationGroup.ids : DeclarationGroup → Array ItemId
  | .«Type» g => ids g .«Type»
  | .Fun g => ids g .Fun
  | .Global g => ids g .Global
  | .TraitDecl g => ids g .TraitDecl
  | .TraitImpl g => ids g .TraitImpl
  | .Mixed g => ids g id
where
  ids {Id : Type} (g : GDeclarationGroup Id) (f : Id → ItemId) : Array ItemId :=
    match g with
    | .NonRec id => #[f id]
    | .Rec ids => ids.map f

namespace Print

/-- The indentation step. -/
def tab : String := "    "

structure Ctx where
  krate : TranslatedCrate
  itemNames : Std.HashMap ItemId Name
  shortNames : Std.HashMap ItemId Name
  /-- The generic parameters in scope, innermost binder first. -/
  generics : List GenericParams := []
  /-- The names of the locals of the current body. -/
  localNames : Option (Array String) := none
  /-- The type whose declaration we're printing, used to name variants and fields in layouts. -/
  currentType : Option TypeDeclId := none
  indentLevel : Nat := 0

def Ctx.new (krate : TranslatedCrate) : Ctx where
  krate
  itemNames := Std.HashMap.ofList krate.item_names.toList
  shortNames := Std.HashMap.ofList krate.short_names.toList

def Ctx.indent (ctx : Ctx) : String := String.join (List.replicate ctx.indentLevel tab)
def Ctx.increaseIndent (ctx : Ctx) : Ctx := { ctx with indentLevel := ctx.indentLevel + 1 }
def Ctx.resetIndent (ctx : Ctx) : Ctx := { ctx with indentLevel := 0 }
def Ctx.setGenerics (ctx : Ctx) (generics : GenericParams) : Ctx := { ctx with generics := [generics] }
def Ctx.noGenerics (ctx : Ctx) : Ctx := { ctx with generics := [] }
def Ctx.pushBinder (ctx : Ctx) (params : GenericParams) : Ctx :=
  { ctx with generics := params :: ctx.generics }
def Ctx.pushBoundRegions (ctx : Ctx) (regions : IndexVec RegionId RegionParam) : Ctx :=
  ctx.pushBinder {
    regions := regions
    types := {}
    const_generics := {}
    trait_clauses := {}
    outlives := #[]
    trait_type_constraints := {} }

def sep (s : String) (xs : List String) : String := s.intercalate xs

/-- Formats `xs` as a comma-separated tuple, with a trailing comma for 1-tuples. -/
def tuple (xs : List String) : String :=
  "(" ++ sep ", " xs ++ (if xs.length == 1 then "," else "") ++ ")"

/-- Compute a unique name for each local. -/
def computeLocalNames (locals : Locals) : Array String := Id.run do
  let base := locals.locals.vec.map fun l => s!"{l.name.getD ""}_{l.index.index}"
  let mut counts : Std.HashMap String Nat := {}
  for l in locals.locals.vec do
    counts := counts.alter base[l.index.index]! (some <| ·.getD 0 + 1)
    if let some name := l.name then
      counts := counts.alter name (some <| ·.getD 0 + 1)
  let mut names := base
  for l in locals.locals.vec do
    if let some name := l.name then
      if !name.isEmpty && counts.get? name == some 1 then
        names := names.set! l.index.index name
  return names

def Ctx.setLocals (ctx : Ctx) (locals : Locals) : Ctx :=
  { ctx with localNames := some (computeLocalNames locals) }

/-! Names of things. -/

def Ctx.assocName (ctx : Ctx) (traitId : TraitDeclId) (get : AssocItemNames → Option String)
    (default : String) : String :=
  (ctx.krate.assoc_item_names.get? traitId >>= get).getD default

def Ctx.methodName (ctx : Ctx) (traitId : TraitDeclId) (id : TraitMethodId) : String :=
  ctx.assocName traitId (·.methods[id]?) s!"@TraitMethod{id.index}"

def Ctx.assocTypeName (ctx : Ctx) (traitId : TraitDeclId) (id : AssocTypeId) : String :=
  ctx.assocName traitId (·.types[id]?) s!"@AssocType{id.index}"

def Ctx.assocConstName (ctx : Ctx) (traitId : TraitDeclId) (id : AssocConstId) : String :=
  ctx.assocName traitId (·.consts[id]?) s!"@AssocConst{id.index}"

def Ctx.variantName (ctx : Ctx) (typeId : TypeDeclId) (variantId : VariantId) : String :=
  match (ctx.krate.type_decls.get? typeId).map TypeDecl.kind with
  | some (.Enum variants) => (variants[variantId]?.map (·.name)).getD s!"@Variant{variantId.index}"
  | some (.Struct _) | some (.Union _) => "_"
  | some .Opaque | some (.Alias _) | some (.Error _) | none => s!"@Variant{variantId.index}"

def Ctx.fieldName (ctx : Ctx) (typeId : TypeDeclId) (variantId : Option VariantId)
    (fieldId : FieldId) : String :=
  let name := match (ctx.krate.type_decls.get? typeId).map TypeDecl.kind, variantId with
    | some (.Enum variants), some v => (variants[v]? >>= (·.fields[fieldId]?)).map Field.name
    | some (.Struct fields), _ | some (.Union fields), _ => fields[fieldId]?.map Field.name
    | _, _ => none
  name.getD (toString fieldId.index)

/-- The short name of a trait impl, if it has a nice one. -/
def Ctx.traitImplShortName (ctx : Ctx) (id : TraitImplId) : Option Name :=
  match ctx.shortNames.get? (.TraitImpl id) with
  | some name => if name.size > 0 && (name[0]! matches .Ident ..) then some name else none
  | none => none

/-- Formats a variable bound by the generic parameters in scope. `paramName` returns `none` if
the parameter doesn't exist, and `some name` otherwise. -/
def Ctx.boundVar {Id : Type} [Idx Id] (ctx : Ctx) (var : DeBruijnVar Id) (pre : String)
    (paramName : GenericParams → Nat → Option (Option String)) : String :=
  if ctx.generics.isEmpty then pre ++ var.toString else
  let depth := ctx.generics.length - 1
  let (dbid, varid) := match var with
    | .Bound dbid id => (dbid, Idx.index id)
    | .Free id => (depth, Idx.index id)
  match ctx.generics[dbid]? >>= (paramName · varid) with
  | none => s!"missing({pre}{var.toString})"
  | some (some name) => name
  | some none => if depth - dbid == 0 then s!"{pre}{varid}" else s!"{pre}{varid}_{depth - dbid}"

def regionParamName (g : GenericParams) (i : Nat) : Option (Option String) :=
  g.regions.vec[i]?.map (·.name)
def typeParamName (g : GenericParams) (i : Nat) : Option (Option String) :=
  g.types.vec[i]?.map (some ·.name)
def constGenericParamName (g : GenericParams) (i : Nat) : Option (Option String) :=
  g.const_generics.vec[i]?.map (some ·.name)
def clauseParamName (g : GenericParams) (i : Nat) : Option (Option String) :=
  g.trait_clauses.vec[i]?.map (fun _ => none)

def RegionParam.fmt (ctx : Ctx) (r : RegionParam) : String :=
  let mut_ := match r.mutability with | .Mutable => "mut " | _ => ""
  match r.name with
  | some name => mut_ ++ name
  | none =>
    let d := ctx.generics.length - 1
    mut_ ++ s!"'_{r.index.index}" ++ (if ctx.generics.length > 1 then s!"_{d}" else "")

/-! The main printer. -/

mutual

partial def ItemId.fmt (ctx : Ctx) (id : ItemId) : String :=
  match ctx.shortNames.get? id <|> ctx.itemNames.get? id with
  | some name => Name.fmt ctx name
  | none => id.toPrettyString

partial def Name.fmt (ctx : Ctx) (name : Name) : String :=
  let ctx := ctx.noGenerics
  sep "::" (name.toList.map (PathElem.fmt ctx))

/-- The full name, which doesn't use the short names of trait impls. -/
partial def Name.fmtFull (ctx : Ctx) (name : Name) : String :=
  let ctx := ctx.noGenerics
  sep "::" <| name.toList.map fun
    | .Impl elem => ImplElem.fmt ctx elem
    | elem => PathElem.fmt ctx elem

partial def PathElem.fmt (ctx : Ctx) : PathElem → String
  | .Ident s d => s ++ (if d.index != 0 then s!"#{d.index}" else "")
  | .Impl elem =>
    match elem with
    | .Trait implId =>
      match ctx.traitImplShortName implId with
      | some short => Name.fmt ctx short
      | none => ImplElem.fmt ctx elem
    | _ => ImplElem.fmt ctx elem
  | .Builtin (.Tuple n) _ => tuple (List.replicate n "_")
  | .Builtin elem d =>
    let s := elem.ident ++ (if d.index != 0 then s!"#{d.index}" else "")
    if elem.isRustName then s else "{" ++ s ++ "}"
  | .Instantiated binder =>
    -- Anonymize all parameters.
    let params := binder.params
    let params := { params with
      regions := ⟨params.regions.vec.map ({ · with name := some "_" })⟩
      types := ⟨params.types.vec.map ({ · with name := "_" })⟩
      const_generics := ⟨params.const_generics.vec.map ({ · with name := "_" })⟩ }
    "<" ++ sep ", " (GenericArgs.fmtExplicits (ctx.pushBinder params) binder.skip_binder) ++ ">"
  | .Target t => t

partial def ImplElem.fmt (ctx : Ctx) (elem : ImplElem) : String :=
  let inner := match elem with
    | .Ty bound => Ty.fmt (ctx.setGenerics bound.params) bound.skip_binder
    | .Trait implId =>
      match ctx.krate.trait_impls.get? implId with
      | none => s!"impl#{implId.index}"
      | some timpl =>
        let ctx := ctx.setGenerics timpl.generics
        let negative := if timpl.is_negative then "!" else ""
        s!"impl {negative}{TraitDeclRef.fmtAsImpl ctx timpl.impl_trait}"
  "{" ++ inner ++ "}"

partial def GenericArgs.fmtExplicits (ctx : Ctx) (g : GenericArgs) : List String :=
  g.regions.toList.map (Region.fmt ctx) ++ g.types.toList.map (Ty.fmt ctx)
    ++ g.const_generics.toList.map (ConstantExpr.fmt ctx)

partial def GenericArgs.fmt (ctx : Ctx) (g : GenericArgs) : String :=
  let explicits := if g.hasExplicits then "<" ++ sep ", " (GenericArgs.fmtExplicits ctx g) ++ ">" else ""
  let implicits := if g.trait_refs.isEmpty then "" else
    "[" ++ sep ", " (g.trait_refs.toList.map (PolyTraitRef.fmt ctx)) ++ "]"
  explicits ++ implicits

partial def RegionArgs.fmt (ctx : Ctx) (args : RegionArgs) : String :=
  if args.regions.isEmpty then "" else
    "<" ++ sep ", " (args.regions.toList.map (Region.fmt ctx)) ++ ">"

partial def Region.fmt (ctx : Ctx) : Region → String
  | .Lub ty => s!"'lub<{Ty.fmt ctx ty}>"
  | .Static => "'static"
  | .Var v => ctx.boundVar v "'_" regionParamName
  | .Body id => s!"'{id.index}"
  | .Erased => "'_"

partial def TypeDeclRef.fmt (ctx : Ctx) (tref : TypeDeclRef) : String :=
  ItemId.fmt ctx (.«Type» tref.id) ++ GenericArgs.fmt ctx tref.generics

/-- The types of the fields of a tuple. -/
partial def tupleFields (ctx : Ctx) (tref : TypeDeclRef) : List Ty :=
  if tref.generics.types.isEmpty then
    -- Monomorphized tuples have no arguments.
    match (ctx.krate.type_decls.get? tref.id).map TypeDecl.kind with
    | some (.Struct fields) => fields.toList.map (·.ty)
    | _ => []
  else tref.generics.types.toList

partial def Ty.fmt (ctx : Ctx) : Ty → String
  | .Adt tref =>
    if tref.isTuple then tuple ((tupleFields ctx tref).map (Ty.fmt ctx))
    else if tref.builtin == some .Str then "str"
    else TypeDeclRef.fmt ctx tref
  | .TypeVar v => ctx.boundVar v "@Type" typeParamName
  | .Scalar s => s.toString
  | .Never => "!"
  | .Pattern ty pat => s!"{Ty.fmt ctx ty} is {TypePattern.fmt ctx pat}"
  | .Ref r ty kind =>
    let mut_ := match kind with | .Mut => "mut " | .Shared => ""
    s!"&{Region.fmt ctx r} {mut_}{Ty.fmt ctx ty}"
  | .RawPtr ty kind =>
    let kind := match kind with | .Shared => "const" | .Mut => "mut"
    s!"*{kind} {Ty.fmt ctx ty}"
  | .Array ty len _ => s!"[{Ty.fmt ctx ty}; {ConstantExpr.fmt ctx len}]"
  | .Slice ty _ => s!"[{Ty.fmt ctx ty}]"
  | .TraitType tref typeId generics =>
    s!"{TraitRef.fmt ctx tref}::{ctx.assocTypeName tref.trait_decl_ref.id typeId}\
      {GenericArgs.fmt ctx generics}"
  | .DynTrait pred => s!"(dyn {DynPredicate.fmt ctx pred})"
  | .FnPtr sig => RegionBinder.fmtFunSig ctx sig
  | .FnDef binder => RegionBinder.fmtAsFor ctx binder FnPtr.fmt
  | .PtrMetadata ty => s!"PtrMetadata<{Ty.fmt ctx ty}>"
  | .Error msg => s!"type_error(\"{msg}\")"

partial def TypePattern.fmt (ctx : Ctx) : TypePattern → String
  | .Range start stop => s!"{ConstantExpr.fmt ctx start}..={ConstantExpr.fmt ctx stop}"
  | .OrPattern pats => "(" ++ sep " | " (pats.toList.map (TypePattern.fmt ctx)) ++ ")"
  | .NotNull => "!null"

partial def DynPredicate.fmt (ctx : Ctx) (pred : DynPredicate) : String :=
  let params := pred.binder.params
  let ctx := ctx.pushBinder params
  -- Gather the associated type constraints of each clause, e.g. `Iterator<Item = ...>`.
  let cstrs : Array (Option Nat × String) := params.trait_type_constraints.vec.map fun cstr =>
    let ctx := ctx.pushBoundRegions cstr.regions
    let c := cstr.skip_binder
    let rec target (tref : TraitRef) (path : List TraitClauseId) :
        Option Nat × List TraitClauseId :=
      match tref.kind with
      | .ParentClause parent clauseId _ => target parent (clauseId :: path)
      | .Clause (.Bound _ clauseId) _ => (some clauseId.index, path)
      | _ => (none, path)
    let (clause, path) := target c.trait_ref []
    let path := path.map (s!"ImpliedClause{·.index}::")
    (clause, String.join path ++ ctx.assocTypeName c.trait_ref.trait_decl_ref.id c.type_id ++
      s!" = {Ty.fmt ctx c.ty}")
  let clauses := params.trait_clauses.vec.toList.map fun clause =>
    RegionBinder.fmtAsFor ctx clause.trait_ fun ctx tref =>
      let cstrs := (cstrs.filter (·.1 == some clause.clause_id.index)).toList.map (·.2)
      let explicits := (GenericArgs.fmtExplicits ctx { tref.generics with
        types := ⟨tref.generics.types.vec.extract 1⟩ })
      let args := explicits ++ cstrs
      ItemId.fmt ctx (.TraitDecl tref.id) ++ (if args.isEmpty then "" else "<" ++ sep ", " args ++ ">")
  let outlives := params.outlives.toList.filterMap fun pred =>
    if pred.skip_binder._1 matches .Erased then none else
    some (RegionBinder.fmtAsFor ctx (toRegionBinder pred) fun ctx p =>
      Region.fmt ctx p._1)
  sep " + " (clauses ++ outlives)

partial def toRegionBinder (p : PolyOutlivesPred) : RegionBinder OutlivesPred :=
  { regions := p.regions, outlives := p.outlives, skip_binder := p.skip_binder }

/-- Formats `for<params> value`. -/
partial def RegionBinder.fmtAsFor {T : Type} (ctx : Ctx) (b : RegionBinder T)
    (fmtInner : Ctx → T → String) : String :=
  let (params, value) := RegionBinder.fmtSplit ctx b fmtInner
  (if params.isEmpty then "" else s!"for<{params}> ") ++ value

partial def RegionBinder.fmtSplit {T : Type} (ctx : Ctx) (b : RegionBinder T)
    (fmtInner : Ctx → T → String) : String × String :=
  let ctx := ctx.pushBoundRegions b.regions
  (RegionBinder.fmtParams ctx b.regions b.outlives, fmtInner ctx b.skip_binder)

partial def RegionBinder.fmtParams (ctx : Ctx) (regions : IndexVec RegionId RegionParam)
    (outlives : Array PolyOutlivesPred) : String :=
  let params := sep ", " (regions.toList.map (RegionParam.fmt ctx))
  let preds := sep ", " (outlives.toList.map fun p =>
    RegionBinder.fmtAsFor ctx (toRegionBinder p) OutlivesPred.fmt)
  if preds.isEmpty then params else params ++ (if params.isEmpty then "" else " ") ++ "where " ++ preds

partial def RegionBinder.fmtFunSig (ctx : Ctx) (b : RegionBinder FunSig) : String :=
  let ctx := ctx.pushBoundRegions b.regions
  let sig := b.skip_binder
  let unsafe_ := if sig.is_unsafe then "unsafe " else ""
  let abi := if sig.abi matches .Rust then "" else s!"extern \"{sig.abi.rustName}\" "
  let params := RegionBinder.fmtParams ctx b.regions b.outlives
  let params := if params.isEmpty then "" else s!"<{params}>"
  let inputs := sig.inputs.toList.map (Ty.fmt ctx)
  let inputs := if sig.is_variadic then inputs ++ ["..."] else inputs
  let output := if sig.output.isUnit then "" else s!" -> {Ty.fmt ctx sig.output}"
  s!"{unsafe_}{abi}fn{params}({sep ", " inputs}){output}"

partial def OutlivesPred.fmt (ctx : Ctx) (p : OutlivesPred) : String :=
  let lhs := match p._0 with
    | .Lub ty => Ty.fmt ctx ty
    | r => Region.fmt ctx r
  s!"{lhs}: {Region.fmt ctx p._1}"

partial def TraitDeclRef.fmt (ctx : Ctx) (tref : TraitDeclRef) : String :=
  ItemId.fmt ctx (.TraitDecl tref.id) ++ GenericArgs.fmt ctx tref.generics

/-- Splits off the `Self` type (which monomorphized traits don't have). -/
partial def TraitDeclRef.splitSelf (tref : TraitDeclRef) : Option Ty × TraitDeclRef :=
  (tref.generics.types.vec[0]?,
    { tref with generics := { tref.generics with types := ⟨tref.generics.types.vec.extract 1⟩ } })

partial def TraitDeclRef.fmtAsPred (ctx : Ctx) (tref : TraitDeclRef) : String :=
  match TraitDeclRef.splitSelf tref with
  | (some self, pred) => s!"{Ty.fmt ctx self}: {TraitDeclRef.fmt ctx pred}"
  | (none, pred) => TraitDeclRef.fmt ctx pred

partial def TraitDeclRef.fmtAsImpl (ctx : Ctx) (tref : TraitDeclRef) : String :=
  match TraitDeclRef.splitSelf tref with
  | (some self, pred) => s!"{TraitDeclRef.fmt ctx pred} for {Ty.fmt ctx self}"
  | (none, pred) => TraitDeclRef.fmt ctx pred

partial def PolyTraitDeclRef.fmtAsPred (ctx : Ctx) (b : RegionBinder TraitDeclRef) : String :=
  RegionBinder.fmtAsFor ctx b fun ctx tref => s!"({TraitDeclRef.fmtAsPred ctx tref})"

partial def TraitImplRef.fmt (ctx : Ctx) (iref : TraitImplRef) : String :=
  ItemId.fmt ctx (.TraitImpl iref.id) ++ GenericArgs.fmt ctx iref.generics

partial def PolyTraitRef.fmt (ctx : Ctx) (tref : PolyTraitRef) : String :=
  RegionBinder.fmtAsFor ctx tref TraitRef.fmt

partial def TraitRef.fmt (ctx : Ctx) (tref : TraitRef) : String :=
  match tref.kind with
  | .SelfId => "Self"
  | .ParentClause sub clauseId args =>
    s!"{TraitRef.fmt ctx sub}::ImpliedClause{clauseId.index}{RegionArgs.fmt ctx args}"
  | .ItemClause sub typeId generics clauseId args =>
    s!"{TraitRef.fmt ctx sub}::{ctx.assocTypeName sub.trait_decl_ref.id typeId}\
      {GenericArgs.fmt ctx generics}::ImpliedClause{clauseId.index}{RegionArgs.fmt ctx args}"
  | .TraitImpl iref => TraitImplRef.fmt ctx iref
  | .Clause v args => ctx.boundVar v "TraitClause" clauseParamName ++ RegionArgs.fmt ctx args
  | .BuiltinOrAuto _ _ types _ =>
    let impl := TraitDeclRef.fmtAsImpl ctx tref.trait_decl_ref
    let types := (IndexMap.enumerate types).toList.map fun (typeId, assoc) =>
      s!"{ctx.assocTypeName tref.trait_decl_ref.id typeId}  = {Ty.fmt ctx assoc.value}"
    "{built_in impl " ++ impl ++ (if types.isEmpty then "" else " where " ++ sep ", " types) ++ "}"
  | .Dyn => TraitDeclRef.fmt ctx tref.trait_decl_ref
  | .Unknown msg => s!"UNKNOWN({msg})"

partial def FnPtr.fmt (ctx : Ctx) (fnPtr : FnPtr) : String :=
  let head := match fnPtr.kind with
    | .Fun id => ItemId.fmt ctx (.Fun id)
    | .Trait tref methodId =>
      s!"{TraitRef.fmt ctx tref}::{ctx.methodName tref.trait_decl_ref.id methodId}"
  head ++ GenericArgs.fmt ctx fnPtr.generics

partial def FunDeclRef.fmt (ctx : Ctx) (fref : FunDeclRef) : String :=
  ItemId.fmt ctx (.Fun fref.id) ++ GenericArgs.fmt ctx fref.generics

partial def GlobalDeclRef.fmt (ctx : Ctx) (gref : GlobalDeclRef) : String :=
  ItemId.fmt ctx (.Global gref.id) ++ GenericArgs.fmt ctx gref.generics

partial def fmtEnumVariant (ctx : Ctx) (typeId : TypeDeclId) (variantId : VariantId) : String :=
  s!"{ItemId.fmt ctx (.«Type» typeId)}::{ctx.variantName typeId variantId}"

/-- Formats `values` as a struct literal `Name { field: value, .. }`. -/
partial def fmtAdtValue (ctx : Ctx) (tref : TypeDeclRef) (variantId : Option VariantId)
    (fields : List (FieldId × String)) : String :=
  if tref.isTuple then tuple (fields.map (·.2)) else
  let head := match variantId with
    | none => ItemId.fmt ctx (.«Type» tref.id)
    | some v => fmtEnumVariant ctx tref.id v
  let fields := fields.map fun (fieldId, v) => s!"{ctx.fieldName tref.id variantId fieldId}: {v}"
  s!"{head} \{ {sep ", " fields} }"

partial def ConstantExpr.fmt (ctx : Ctx) (c : ConstantExpr) : String :=
  match c.kind with
  | .Integer v => v.toString
  | .Float v => v.toString
  | .Bool b => toString b
  | .Char ch => s!"'{escapeDebug ch}'"
  | .Str s => "\"" ++ (s.replace "\\" "\\\\" |>.replace "\n" "\\n") ++ "\""
  | .ByteStr bytes => toString bytes.toList
  | .Adt variantId values =>
    match c.ty with
    | .Adt tref =>
      fmtAdtValue ctx tref variantId <|
        (IndexVec.enumerate values).toList.map fun (i, v) => (i, ConstantExpr.fmt ctx v)
    | _ => "<ill-typed ADT constant>"
  | .Array values => "[" ++ sep ", " (values.toList.map (ConstantExpr.fmt ctx)) ++ "]"
  | .Repeat value count _ => s!"[{ConstantExpr.fmt ctx value}; {ConstantExpr.fmt ctx count}]"
  | .Global gref => GlobalDeclRef.fmt ctx gref
  | .TraitConst tref constId =>
    s!"{TraitRef.fmt ctx tref}::{ctx.assocConstName tref.trait_decl_ref.id constId}"
  | .VTableRef tref => s!"&vtable_of({PolyTraitRef.fmt ctx tref})"
  | .Discriminant tref variantId => s!"discriminant_of({fmtEnumVariant ctx tref.id variantId})"
  | .Ref place md => s!"&{GlobalPlace.fmt ctx place}{fmtMetadata ctx md}"
  | .Ptr kind place md =>
    let kind := match kind with | .Mut => "&raw mut" | .Shared => "&raw const"
    s!"{kind} {GlobalPlace.fmt ctx place}{fmtMetadata ctx md}"
  | .Var v => ctx.boundVar v "@ConstGeneric" constGenericParamName
  | .Call fnPtr args =>
    s!"{FnPtr.fmt ctx fnPtr}({sep ", " (args.toList.map (ConstantExpr.fmt ctx))})"
  | .FnDef fnPtr => FnPtr.fmt ctx fnPtr
  | .FnPtr fnPtr => s!"fnptr({FnPtr.fmt ctx fnPtr})"
  | .Cast value kind => s!"{CastKind.fmt ctx kind}({ConstantExpr.fmt ctx value})"
  | .TypeId ty => s!"TypeId({Ty.fmt ctx ty})"
  | .SizeOf ty => s!"size_of::<{Ty.fmt ctx ty}>()"
  | .AlignOf ty => s!"align_of::<{Ty.fmt ctx ty}>()"
  | .OffsetOf tref variant field =>
    let variantStr := match variant with
      | some v => ctx.variantName tref.id v ++ "."
      | none => ""
    s!"offset_of({TypeDeclRef.fmt ctx tref}.{variantStr}{ctx.fieldName tref.id variant field})"
  | .PtrNoProvenance v => s!"no-provenance {v}"
  | .ExternSymbol name => s!"&raw const <extern:{name}>"
  | .RawMemory bytes => "RawMemory(" ++ sep ", " (bytes.toList.map (Byte.fmt ctx)) ++ ")"
  | .Opaque cause => s!"Opaque({cause})"

partial def fmtMetadata (ctx : Ctx) : Option UnsizingMetadata → String
  | some md => s!" with_metadata({UnsizingMetadata.fmt ctx md})"
  | none => ""

/-- Formats a constant used as a switch case. -/
partial def ConstantExpr.fmtAsPattern (ctx : Ctx) (c : ConstantExpr) : String :=
  match c.kind with
  | .Discriminant tref variantId => fmtEnumVariant ctx tref.id variantId
  | _ => ConstantExpr.fmt ctx c

partial def Byte.fmt (ctx : Ctx) : Byte → String
  | .Value x =>
    let hex := (Nat.toDigits 16 x.toNat)
    "0x" ++ String.ofList (List.replicate (2 - hex.length) '0' ++ hex)
  | .Uninit => "--"
  | .Provenance p ofs i =>
    let ofs : Int := match ofs with | .Signed _ v => v | .Unsigned _ v => v
    s!"&{GlobalProvenance.fmt ctx p}" ++ (if ofs != 0 then s!"+{ofs}" else "") ++ s!"[{i}]"

partial def GlobalProvenance.fmt (ctx : Ctx) : GlobalProvenance → String
  | .Global g => GlobalDeclRef.fmt ctx g
  | .Function f _ => FnPtr.fmt ctx f
  | .TypeId ty => s!"TypeId({Ty.fmt ctx ty})"

partial def GlobalPlace.fmt (ctx : Ctx) (place : GlobalPlace) : String :=
  match place.kind with
  | .Global prov => GlobalProvenance.fmt ctx prov
  | .Value v => ConstantExpr.fmt ctx v
  | .Projection sub proj =>
    let subStr := GlobalPlace.fmt ctx sub
    match proj with
    | .Field variantId fieldId => fmtFieldProjection ctx subStr sub.ty variantId fieldId
    | .Index i => s!"{subStr}[{i.toString}]"
    | .Subslice start stop => s!"{subStr}[{start.toString}..{stop.toString}]"
    | .Offset count ty inBounds _ =>
      let method := if inBounds then "offset" else "wrapping_offset"
      match ty with
      | none => s!"{subStr}.{method}!({count.toString})"
      | some ty => s!"{subStr}.{method}!({count.toString} * size_of::<{Ty.fmt ctx ty}>())"

partial def fmtFieldProjection (ctx : Ctx) (sub : String) (subTy : Ty)
    (variantId : Option VariantId) (fieldId : FieldId) : String :=
  match subTy with
  | .Adt tref =>
    let sub := match variantId with
      | none => s!"{sub}."
      | some v => s!"({sub} as variant {fmtEnumVariant ctx tref.id v})."
    sub ++ ctx.fieldName tref.id variantId fieldId
  | _ => s!"{sub}.{fieldId.index}"

partial def UnsizingMetadata.fmt (ctx : Ctx) : UnsizingMetadata → String
  | .Length len => ConstantExpr.fmt ctx len
  | .VTable _ vtable => ConstantExpr.fmt ctx vtable
  | .VTableUpcast fields => " at [" ++ sep ", " (fields.toList.map (toString ·.index)) ++ "]"
  | .Unknown => "?"

partial def CastKind.fmt (ctx : Ctx) : CastKind → String
  | .Scalar tgt => s!"cast<{tgt.toString}>"
  | .PtrExposeProvenance tgt => s!"cast_expose<{tgt.toString}>"
  | .PtrWithExposedProvenance tgt => s!"cast_with_exposed<{Ty.fmt ctx tgt}>"
  | .FnDefToFnPtr => "fn_def_to_fn_ptr"
  | .FnPtrToUnsafe => "fn_ptr_to_unsafe"
  | .Subtype tgt => s!"subtype<{Ty.fmt ctx tgt}>"
  | .RawPtr tgt => s!"cast<{Ty.fmt ctx tgt}>"
  | .Unsize tgt md _ => s!"unsize_cast<{Ty.fmt ctx tgt}, {UnsizingMetadata.fmt ctx md}>"
  | .Transmute tgt => s!"transmute<{Ty.fmt ctx tgt}>"
  | .Concretize tgt _ => s!"concretize<{Ty.fmt ctx tgt}>"

partial def LocalId.fmt (ctx : Ctx) (id : LocalId) : String :=
  match ctx.localNames >>= (·[id.index]?) with
  | some name => name
  | none => s!"_{id.index}"

partial def Place.fmt (ctx : Ctx) (place : Place) : String :=
  match place.kind with
  | .Local id => LocalId.fmt ctx id
  | .Global gref => GlobalDeclRef.fmt ctx gref
  | .Projection sub proj =>
    let s := Place.fmt ctx sub
    match proj with
    | .Deref => s!"(*{s})"
    | .Field variantId fieldId => fmtFieldProjection ctx s sub.ty variantId fieldId
    | .PtrMetadata => s!"{s}.metadata"
    | .Index offset fromEnd =>
      s!"{s}[{if fromEnd then "-" else ""}{Operand.fmt ctx offset}]"
    | .Subslice start stop fromEnd =>
      s!"{s}[{Operand.fmt ctx start}..{if fromEnd then "-" else ""}{Operand.fmt ctx stop}]"
    | .Offset bytes inBounds _ _ =>
      let method := if inBounds then "offset" else "wrapping_offset"
      s!"{s}.{method}!({Operand.fmt ctx bytes})"

partial def Operand.fmt (ctx : Ctx) : Operand → String
  | .Copy p _ => s!"copy {Place.fmt ctx p}"
  | .Read p => s!"read {Place.fmt ctx p}"
  | .Move p => s!"move {Place.fmt ctx p}"
  | .Const c => s!"const {ConstantExpr.fmt ctx c}"

partial def UnOp.fmt (ctx : Ctx) : UnOp → String
  | .Not => "~"
  | .Neg mode => s!"{mode.toString}.-"
  | .Cast kind => CastKind.fmt ctx kind

/-- Formats `place`, followed by `ptr_metadata` unless it is unit. -/
partial def fmtWithMetadata (ctx : Ctx) (place : Place) (md : Operand) : String :=
  if md.ty.isUnit then Place.fmt ctx place
  else s!"{Place.fmt ctx place} with_metadata({Operand.fmt ctx md})"

partial def Rvalue.fmt (ctx : Ctx) : Rvalue → String
  | .Use op retag => (if retag matches .No then "noretag " else "") ++ Operand.fmt ctx op
  | .Ref place kind md =>
    let kind := match kind with
      | .Shared => "&" | .Mut => "&mut " | .TwoPhaseMut => "&two-phase-mut "
      | .UniqueImmutable => "&uniq " | .Shallow => "&shallow "
    kind ++ fmtWithMetadata ctx place md
  | .RawPtr place kind md =>
    let kind := match kind with | .Shared => "&raw const " | .Mut => "&raw mut "
    kind ++ fmtWithMetadata ctx place md
  | .BinaryOp op x y => s!"{Operand.fmt ctx x} {op.toString} {Operand.fmt ctx y}"
  | .UnaryOp op x => s!"{UnOp.fmt ctx op}({Operand.fmt ctx x})"
  | .NullaryOp op => op.toString
  | .Discriminant p => s!"@discriminant({Place.fmt ctx p})"
  | .Aggregate kind ops =>
    let opsStr := ops.toList.map (Operand.fmt ctx)
    match kind with
    | .Adt tref variantId fieldId =>
      let fieldIds := match fieldId with
        | some fieldId => [fieldId]
        | none => (List.range ops.size).map FieldId.mk
      fmtAdtValue ctx tref variantId (fieldIds.zip opsStr)
    | .Array .. => "[" ++ sep ", " opsStr ++ "]"
    | .RawPtr _ kind =>
      let kind := match kind with | .Shared => "const" | .Mut => "mut "
      s!"*{kind} ({sep ", " opsStr})"
  | .Repeat op count _ _ => s!"[{Operand.fmt ctx op}; {ConstantExpr.fmt ctx count}]"

partial def BorrowckStatement.fmt (ctx : Ctx) : BorrowckStatement → String
  | .FakeRead place => s!"fake_read({Place.fmt ctx place})"
  | .SetType place ty variance =>
    let rel := match variance with
      | .Covariant => "<=" | .Contravariant => ">=" | .Invariant => "=="
      | .Bivariant => panic! "bivariant SetType statement"
      | .Unknown => panic! "SetType statement with unknown variance"
    s!"set_type(typeof({Place.fmt ctx place}) {rel} {Ty.fmt ctx ty})"
  | .SetOutlives ty r => s!"set_outlives({Ty.fmt ctx ty}, {Region.fmt ctx r})"
  | .PredicateHolds pred => s!"predicate_holds({PolyTraitRef.fmt ctx pred})"

partial def BuiltinAssertKind.fmt : BuiltinAssertKind → String
  | .BoundsCheck .. => "bounds_check"
  | .Overflow .. => "overflow"
  | .OverflowNeg .. => "overflow_neg"
  | .DivisionByZero .. => "division_by_zero"
  | .RemainderByZero .. => "remainder_by_zero"
  | .MisalignedPointerDereference .. => "misaligned_pointer_dereference"
  | .NullPointerDereference => "null_pointer_dereference"
  | .NullReferenceCreated => "null_reference_created"
  | .InvalidEnumConstruction .. => "invalid_enum_construction"
  | .ResumedAfterReturn => "resumed_after_return"
  | .ResumedAfterDrop => "resumed_after_drop"
  | .ResumedAfterPanic => "resumed_after_panic"

partial def Assert.fmt (ctx : Ctx) (a : Assert) : String :=
  s!"assert({Operand.fmt ctx a.cond} == {a.expected})" ++
    match a.check_kind with
    | some kind => s!" ({BuiltinAssertKind.fmt kind})"
    | none => ""

partial def AbortKind.fmt (ctx : Ctx) : AbortKind → String
  | .Panic (some name) => s!"panic({Name.fmt ctx name})"
  | .Panic none => "panic"
  | .UndefinedBehavior => "undefined_behavior"
  | .UnwindTerminate => "unwind_terminate"

partial def FnOperand.fmt (ctx : Ctx) : FnOperand → String
  | .Regular f => FnPtr.fmt ctx f
  | .Dynamic op regions => s!"({Operand.fmt ctx op}){RegionArgs.fmt ctx regions}"

partial def Call.fmt (ctx : Ctx) (call : Call) : String :=
  s!"{FnOperand.fmt ctx call.func}({sep ", " (call.args.toList.map (Operand.fmt ctx))})"

partial def AsmOperand.fmt (ctx : Ctx) : AsmOperand → String
  | .In reg value => s!"in({AsmRegister.fmt reg}) {Operand.fmt ctx value}"
  | .Out reg late place =>
    s!"{if late then "lateout" else "out"}({AsmRegister.fmt reg}) \
      {(place.map (Place.fmt ctx)).getD "_"}"
  | .InOut reg late inValue outPlace =>
    s!"{if late then "inlateout" else "inout"}({AsmRegister.fmt reg}) \
      {Operand.fmt ctx inValue} => {(outPlace.map (Place.fmt ctx)).getD "_"}"
  | .Const value => s!"const {ConstantExpr.fmt ctx value}"
  | .SymFn f => s!"sym {FnPtr.fmt ctx f}"
  | .SymStatic g => s!"sym {GlobalDeclRef.fmt ctx g}"
  | .Label branch => s!"label(branch {branch.index})"

partial def AsmRegister.fmt : AsmRegister → String
  | .Explicit reg => reg.quote
  | .Class cls => cls

partial def InlineAsm.fmt (ctx : Ctx) (asm : InlineAsm) : String :=
  let mac := match asm.kind with | .Asm => "asm" | .NakedAsm => "naked_asm"
  let template := String.join <| asm.template.toList.map fun
    | .Text text => text.replace "{" "{{" |>.replace "}" "}}"
    | .Placeholder operandId modifier _ =>
      "{" ++ toString operandId.index ++ ((modifier.map (":" ++ ·.toString)).getD "") ++ "}"
  let operands := asm.operands.toList.map (", " ++ AsmOperand.fmt ctx ·)
  let o := asm.options
  let flags := [(o.pure, "pure"), (o.nomem, "nomem"), (o.readonly, "readonly"),
    (o.preserves_flags, "preserves_flags"), (o.noreturn, "noreturn"), (o.nostack, "nostack"),
    (o.att_syntax, "att_syntax"), (o.may_unwind, "may_unwind")].filterMap fun (set, name) =>
      if set then some name else none
  let options := if flags.isEmpty then "" else s!", options({sep ", " flags})"
  s!"{mac}!({template.quote}{String.join operands}{options})"

-- ULLBC bodies.

partial def Ullbc.Statement.fmt (ctx : Ctx) (st : Ullbc.Statement) : String :=
  let t := ctx.indent
  let comments := String.join (st.comments_before.toList.map (s!"{t}// {·}\n"))
  let body := match st.kind with
    | .Assign place rv => s!"{Place.fmt ctx place} = {Rvalue.fmt ctx rv}"
    | .Borrowck s => BorrowckStatement.fmt ctx s
    | .SetDiscriminant place variantId => s!"@discriminant({Place.fmt ctx place}) = {variantId.index}"
    | .StorageLive id => s!"storage_live({LocalId.fmt ctx id})"
    | .StorageDead id => s!"storage_dead({LocalId.fmt ctx id})"
    | .PlaceMention place => s!"_ = {Place.fmt ctx place}"
    | .Assert a onFailure => s!"{Assert.fmt ctx a} else {AbortKind.fmt ctx onFailure}"
    | .Nop => "nop"
  s!"{comments}{t}{body};\n"

partial def Terminator.fmt (ctx : Ctx) (term : Terminator) : String :=
  let t := ctx.indent
  let comments := String.join (term.comments_before.toList.map (s!"{t}// {·}\n"))
  let bb (id : Ullbc.BlockId) : String := s!"bb{id.index}"
  let body := match term.kind with
    | .Goto target => s!"goto {bb target}"
    | .Switch data branches =>
      let target (b : BranchId) : String := (branches[b]?.map bb).getD s!"<missing branch {b.index}>"
      match data.asIf with
      | some (thenB, elseB) =>
        s!"if {SwitchScrutinee.fmt ctx data.scrutinee} -> {target thenB} else -> {target elseB}"
      | none =>
        let cases := data.branches.toList.map (fun (v, b) =>
          s!"{ConstantExpr.fmtAsPattern ctx v}: {target b}") ++
          (data.fallback.toList.map (s!"otherwise: {target ·}"))
        let kw := match data.scrutinee with | .Value _ => "switch" | .Discriminant _ => "match"
        s!"{kw} {SwitchScrutinee.fmt ctx data.scrutinee} -> {sep ", " cases}"
    | .Call call dest target onUnwind =>
      s!"{Place.fmt ctx dest} = {Call.fmt ctx call} -> {bb target} (unwind: {bb onUnwind})"
    | .Drop kind place fnPtr target onUnwind =>
      let kind := match kind with | .Precise => "drop" | .Conditional => "conditional_drop"
      s!"{kind}[{FnPtr.fmt ctx fnPtr}] {Place.fmt ctx place} -> {bb target} (unwind: {bb onUnwind})"
    | .DropEmptyBox place target onUnwind =>
      s!"drop_empty_box {Place.fmt ctx place} -> {bb target} (unwind: {bb onUnwind})"
    | .Assert a target onUnwind => s!"assert {Assert.fmt ctx a} -> {bb target} (unwind: {bb onUnwind})"
    | .InlineAsm asm fallthrough labels onUnwind =>
      let targets := fallthrough.toList.map (s!"fallthrough: {bb ·}") ++
        (IndexVec.enumerate labels).toList.map (fun ((b : BranchId), target) =>
          s!"label {b.index}: {bb target}") ++
        [s!"unwind: {bb onUnwind}"]
      s!"{InlineAsm.fmt ctx asm} -> {sep ", " targets}"
    | .Panic name onUnwind => s!"{AbortKind.fmt ctx (.Panic (some name))} -> (unwind: {bb onUnwind})"
    | .UndefinedBehavior => AbortKind.fmt ctx .UndefinedBehavior
    | .UnwindTerminate => AbortKind.fmt ctx .UnwindTerminate
    | .Return => "return"
    | .UnwindResume => "unwind_continue"
  s!"{comments}{t}{body}"

partial def SwitchScrutinee.fmt (ctx : Ctx) : SwitchScrutinee → String
  | .Value op => Operand.fmt ctx op
  | .Discriminant place => Place.fmt ctx place

partial def Ullbc.BlockData.fmt (ctx : Ctx) (block : Ullbc.BlockData) : String :=
  String.join (block.statements.toList.map (Ullbc.Statement.fmt ctx)) ++
    Terminator.fmt ctx block.terminator ++ ";"

partial def fmtUllbcBlocks (ctx : Ctx) (blocks : IndexVec Ullbc.BlockId Ullbc.BlockData) : String :=
  let t := ctx.indent
  let ctx := ctx.increaseIndent
  String.join <| (IndexVec.enumerate blocks).toList.map fun (id, block) =>
    let kind := match block.kind with
      | .Regular => "" | .Cleanup => " (cleanup)" | .Terminate => " (terminate)"
    s!"\n{t}bb{id.index}{kind}: \{\n{Ullbc.BlockData.fmt ctx block}\n{t}}\n"

-- LLBC bodies.

partial def Llbc.Block.fmt (ctx : Ctx) (block : Llbc.Block) : String :=
  String.join (block.statements.toList.map (Llbc.Statement.fmt ctx))

partial def fmtUnwindBlock (ctx : Ctx) (onUnwind : Llbc.Block) : String :=
  let t := ctx.indent
  match (Llbc.Block.fmt ctx.resetIndent onUnwind).splitOn "\n" |>.filter (!·.isEmpty) with
  | [] => ""
  | first :: rest =>
    let t1 := ctx.increaseIndent.indent
    s!"\n{t}↳⚡ {first}" ++ String.join (rest.map (s!"\n{t1}{·}"))

partial def Llbc.Statement.fmt (ctx : Ctx) (st : Llbc.Statement) : String :=
  let t := ctx.indent
  let comments := String.join (st.comments_before.toList.map (s!"{t}// {·}\n"))
  if st.kind matches .Nop then comments else
  let unwind := fmtUnwindBlock ctx
  let body := match st.kind with
    | .Assign place rv => s!"{Place.fmt ctx place} = {Rvalue.fmt ctx rv}"
    | .Borrowck s => BorrowckStatement.fmt ctx s
    | .SetDiscriminant place variantId => s!"@discriminant({Place.fmt ctx place}) = {variantId.index}"
    | .StorageLive id => s!"storage_live({LocalId.fmt ctx id})"
    | .StorageDead id => s!"storage_dead({LocalId.fmt ctx id})"
    | .PlaceMention place => s!"_ = {Place.fmt ctx place}"
    | .Drop place fnPtr kind onUnwind =>
      let kind := match kind with | .Precise => "drop" | .Conditional => "conditional_drop"
      s!"{kind}[{FnPtr.fmt ctx fnPtr}] {Place.fmt ctx place}" ++ unwind onUnwind
    | .DropEmptyBox place onUnwind => s!"drop_empty_box {Place.fmt ctx place}" ++ unwind onUnwind
    | .Assert a onFailure onUnwind =>
      s!"{Assert.fmt ctx a} else {AbortKind.fmt ctx onFailure}" ++ unwind onUnwind
    | .InlineAsm asm fallthrough labels onUnwind =>
      let ctx1 := ctx.increaseIndent
      let t1 := ctx1.indent
      let ctx2 := ctx1.increaseIndent
      let branches := fallthrough.toList.map (fun b =>
          s!"\n{t1}fallthrough => \{\n{Llbc.Block.fmt ctx2 b}{t1}}") ++
        (IndexVec.enumerate labels).toList.map (fun ((id : BranchId), b) =>
          s!"\n{t1}label {id.index} => \{\n{Llbc.Block.fmt ctx2 b}{t1}}")
      InlineAsm.fmt ctx asm ++ (if branches.isEmpty then "" else
        " {" ++ String.join branches ++ s!"\n{t}}") ++ unwind onUnwind
    | .Call call dest onUnwind => s!"{Place.fmt ctx dest} = {Call.fmt ctx call}" ++ unwind onUnwind
    | .Panic name onUnwind => AbortKind.fmt ctx (.Panic (some name)) ++ unwind onUnwind
    | .UndefinedBehavior => AbortKind.fmt ctx .UndefinedBehavior
    | .UnwindTerminate => AbortKind.fmt ctx .UnwindTerminate
    | .Return => "return"
    | .UnwindResume => "unwind_continue"
    | .Break i => s!"break {i}"
    | .Continue i => s!"continue {i}"
    | .Loop body => "loop {\n" ++ Llbc.Block.fmt ctx.increaseIndent body ++ t ++ "}"
    | .Switch data branches =>
      match data.scrutinee, data.asIf with
      | .Value discr, some (thenB, elseB) =>
        let ctx' := ctx.increaseIndent
        let block (b : BranchId) := (branches[b]?.map (Llbc.Block.fmt ctx')).getD ""
        s!"if {Operand.fmt ctx discr} \{\n{block thenB}{t}} else \{\n{block elseB}{t}}"
      | scrutinee, _ =>
        let kw := match scrutinee with | .Value _ => "switch" | .Discriminant _ => "match"
        let ctx1 := ctx.increaseIndent
        let t1 := ctx1.indent
        let ctx2 := ctx1.increaseIndent
        let casesByBranch := data.groupByBranch branches.size
        let arms := (IndexVec.enumerate branches).toList.map fun ((b : BranchId), block) =>
          let cases := (casesByBranch[b.index]?.getD #[]).toList.map (ConstantExpr.fmtAsPattern ctx)
          let cases := if data.fallback == some b then cases ++ ["_"] else cases
          let cases := if cases.isEmpty then "_" else sep " | " cases
          s!"{t1}{cases} => \{\n{Llbc.Block.fmt ctx2 block}{t1}},\n"
        s!"{kw} {SwitchScrutinee.fmt ctx scrutinee} \{\n{String.join arms}{t}}"
    | .Nop => ""
  s!"{comments}{t}{body}\n"

-- Items.

partial def GenericParams.fmtParams (ctx : Ctx) (g : GenericParams) : List String :=
  g.regions.toList.map (RegionParam.fmt ctx) ++ g.types.toList.map (·.name) ++
    g.const_generics.toList.map fun c => s!"const {c.name} : {Ty.fmt ctx c.ty}"

partial def TraitParam.fmt (ctx : Ctx) (p : TraitParam) : String :=
  let d := ctx.generics.length - 1
  s!"TraitClause{p.clause_id.index}" ++ (if d ≥ 1 then s!"_{d}" else "") ++
    s!": {PolyTraitDeclRef.fmtAsPred ctx p.trait_}"

partial def GenericParams.fmtClauses (ctx : Ctx) (g : GenericParams) : List String :=
  g.trait_clauses.toList.map (TraitParam.fmt ctx) ++
    (g.outlives.toList.zipIdx.map fun (p, i) =>
      s!"Outlives{i}: ({RegionBinder.fmtAsFor ctx (toRegionBinder p) OutlivesPred.fmt})") ++
    (g.trait_type_constraints.toList.zipIdx.map fun (c, i) =>
      s!"TypeConstraint{i}: {RegionBinder.fmtAsFor ctx c TraitTypeConstraint.fmt}")

partial def TraitTypeConstraint.fmt (ctx : Ctx) (c : TraitTypeConstraint) : String :=
  s!"{TraitRef.fmt ctx c.trait_ref}::{ctx.assocTypeName c.trait_ref.trait_decl_ref.id c.type_id} \
    = {Ty.fmt ctx c.ty}"

/-- Formats the parameters as `<...>` and the predicates as a `where` clause. -/
partial def GenericParams.fmtWithClauses (ctx : Ctx) (g : GenericParams) : String × String :=
  let t := ctx.indent
  let params := if g.hasExplicits then "<" ++ sep ", " (GenericParams.fmtParams ctx g) ++ ">" else ""
  let clauses := if g.hasPredicates then
    s!"\n{t}where" ++ String.join ((GenericParams.fmtClauses ctx g).map (s!"\n{t}{tab}{·},"))
    else ""
  (params, clauses)

partial def GenericParams.fmtSingleLine (ctx : Ctx) (g : GenericParams) : String :=
  if g.isEmpty then "" else "<" ++ sep ", " (GenericParams.fmtParams ctx g ++ GenericParams.fmtClauses ctx g) ++ ">"

partial def Binder.fmtSplit {T : Type} (ctx : Ctx) (b : Binder T) (fmtInner : Ctx → T → String) :
    String × String :=
  let ctx := ctx.pushBinder b.params
  (GenericParams.fmtSingleLine ctx b.params, fmtInner ctx b.skip_binder)

partial def fmtWhereClauses (clauses : List String) (indent : String) : String :=
  if clauses.isEmpty then "" else
  s!"\n{indent}where" ++ String.join (clauses.mapIdx fun i c =>
    s!"\n{indent}{tab}{c}{if i + 1 == clauses.length then ";" else ","}")

partial def Attribute.fmt (ctx : Ctx) : Attribute → String
  | .Opaque => "#[charon::opaque]"
  | .Exclude => "#[charon::exclude]"
  | .Rename name => s!"#[charon::rename(\"{name}\")]"
  | .VariantsPrefix p => s!"#[charon::variants_prefix(\"{p}\")]"
  | .VariantsSuffix p => s!"#[charon::variants_suffix(\"{p}\")]"
  | .Transparent => "#[charon::transparent]"
  | .IsContract kind target =>
    let target := match target with
      | .Free id => ItemId.fmt ctx id
      | .Assoc traitId item =>
        let name := match item with
          | .«Type» id => ctx.assocTypeName traitId id
          | .Method id => ctx.methodName traitId id
          | .Const id => ctx.assocConstName traitId id
        s!"{ItemId.fmt ctx (.TraitDecl traitId)}::{name}"
    s!"#[charon::contract(kind = {kind.quote}, for = {target.quote})]"
  | .HasContract kind contract =>
    s!"#[charon::has_contract(kind = {kind.quote}, contract = {ItemId.fmt ctx (.Fun contract)})]"
  | .DocComment c => sep "\n" ((c.splitOn "\n").map ("///" ++ ·))
  | .Builtin kind => s!"#[{AttributeKind.fmt kind}]"
  | .Unknown attr => s!"#[{attr.path}{(attr.args.map (s!"({·})")).getD ""}]"

partial def AttributeKind.fmt : AttributeKind → String
  | .AutomaticallyDerived => "automatically_derived"
  | .Cold => "cold"
  | .Deprecated dep _ =>
    let since := match dep.since with
      | .RustcVersion v => some s!"{v.major}.{v.minor}.{v.patch}"
      | .Future => some "future"
      | .NonStandard s => some s
      | .Unspecified | .Err => none
    let args := (since.map (s!"since = \"{·}\"")).toList ++
      (dep.note.map (s!"note = \"{·.name}\"")).toList
    "deprecated" ++ (if args.isEmpty then "" else s!"({sep ", " args})")
  | .ExportName name _ => s!"export_name = \"{name}\""
  | .Fundamental => "fundamental"
  | .Ignore _ reason => "ignore" ++ ((reason.map (s!" = \"{·}\"")).getD "")
  | .Inline inline _ => match inline with
    | .None => "inline" | .Hint => "inline(hint)" | .Always => "inline(always)"
    | .Never => "inline(never)" | .Force .. => "rustc_force_inline"
  | .LinkSection name => s!"link_section = \"{name}\""
  | .Linkage linkage _ =>
    let l := match linkage with
      | .AvailableExternally => "available_externally" | .Common => "common"
      | .ExternalWeak => "extern_weak" | .External => "external" | .Internal => "internal"
      | .LinkOnceAny => "linkonce" | .LinkOnceODR => "linkonce_odr" | .WeakAny => "weak"
      | .WeakODR => "weak_odr"
    s!"linkage = \"{l}\""
  | .MayDangle _ => "may_dangle"
  | .Naked _ => "naked"
  | .NoLink => "no_link"
  | .NoMangle _ => "no_mangle"
  | .NonExhaustive _ => "non_exhaustive"
  | .Optimize o _ => match o with
    | .Default => "optimize(default)" | .DoNotOptimize => "optimize(none)"
    | .Speed => "optimize(speed)" | .Size => "optimize(size)"
  | .RustcAlign align _ => s!"rustc_align({align})"
  | .RustcIntrinsic => "rustc_intrinsic"
  | .ShouldPanic reason => "should_panic" ++ ((reason.map (s!"(expected = \"{·}\")")).getD "")
  | .TargetFeature features _ forced =>
    let features := sep "," (features.toList.map (·.1))
    s!"target_feature({if forced then "force" else "enable"} = \"{features}\")"
  | .TrackCaller _ => "track_caller"

/-- Formats the start of an item definition, up to the name. -/
partial def ItemMeta.fmtIntro (ctx : Ctx) (md : ItemMeta) (keyword : String) (id : ItemId) :
    String := Id.run do
  let t := ctx.indent
  let mut out := ""
  let mut name := md.name
  let mut nameIsFull := true
  if let some short := ctx.shortNames.get? id then
    name := short
    nameIsFull := false
  else if md.name.any (fun elem => match elem with
      | .Impl (.Trait implId) => (ctx.traitImplShortName implId).isSome
      | _ => false) then
    nameIsFull := false
  if !nameIsFull then
    out := out ++ s!"// Full name: {Name.fmtFull ctx md.name}\n"
  for attr in md.attr_info.attributes do
    -- Doc-comments are long and don't affect the semantics; skip them.
    if !(attr matches .DocComment _) then
      out := out ++ t ++ (sep s!"\n{t}" ((Attribute.fmt ctx attr).splitOn "\n")) ++ "\n"
  if let some item := md.lang_item then
    out := out ++ s!"{t}#[lang_item({(repr item).pretty.replace "Charon.LangItem." ""})]\n"
  if let some item := md.diagnostic_item then
    out := out ++ s!"{t}#[diagnostic_item(\"{item}\")]\n"
  out := out ++ t ++ (if md.attr_info.public then "pub " else "") ++
    (if md.is_extern then "extern " else "") ++ s!"{keyword} {Name.fmt ctx name}"
  return out

partial def Local.fmtDecl (ctx : Ctx) (locals : Locals) (l : Local) : String :=
  let t := ctx.indent
  let mut_ := if l.mutable then "mut " else ""
  let kind := if l.index.index == 0 then "return"
    else if l.index.index ≤ locals.arg_count then s!"arg #{l.index.index}"
    else if l.name.isSome then "local" else "anonymous local"
  let dropFlag := (l.drop_flag_for.map (s!"; drop flag for {Place.fmt ctx ·}")).getD ""
  s!"{t}let {mut_}{LocalId.fmt ctx l.index}: {Ty.fmt ctx l.ty}; // {kind}{dropFlag}\n"

partial def GExprBody.fmt {T : Type} (ctx : Ctx) (body : GExprBody T) (fmtBody : Ctx → T → String) :
    String :=
  let ctx := (ctx.setLocals body.locals).increaseIndent
  String.join (body.locals.locals.toList.map (Local.fmtDecl ctx body.locals)) ++
    fmtBody ctx body.body

partial def Body.fmt (ctx : Ctx) (body : Body) : String :=
  let t := ctx.indent
  "\n" ++ t ++ match body with
  | .Unstructured b => "{\n" ++ GExprBody.fmt ctx b fmtUllbcBlocks ++ t ++ "}"
  | .Structured b =>
    "{\n" ++ GExprBody.fmt ctx b (fun ctx b => "\n" ++ Llbc.Block.fmt ctx b) ++ t ++ "}"
  | .Extern name => s!"= <extern:{name}>"
  | .Intrinsic name _ fallback isSpec =>
    s!"= <intrinsic:{name}>" ++ match fallback with
      | some f => s!" with fallback{if isSpec then " (spec)" else ""} {FunDeclRef.fmt ctx f}"
      | none => ""
  | .Opaque => "= <opaque>"
  | .Missing => "= <missing>"
  | .Error e => s!"= error(\"{e.msg}\")"
  | .TargetDispatch targets =>
    "= target_dispatch {\n" ++ String.join (targets.toList.map fun (target, f) =>
      s!"{t}{tab}{target} => {FunDeclRef.fmt ctx f},\n") ++ t ++ "}"

partial def FunDecl.fmt (ctx : Ctx) (decl : FunDecl) : String :=
  let sig := decl.signature
  let keyword := (if sig.is_unsafe then "unsafe " else "") ++
    (if sig.abi matches .Rust then "" else s!"extern \"{sig.abi.rustName}\" ") ++ "fn"
  let intro := ItemMeta.fmtIntro ctx decl.item_meta keyword (.Fun decl.def_id)
  let ctx := ctx.setGenerics decl.generics
  let (params, preds) := GenericParams.fmtWithClauses ctx decl.generics
  let nArgs := sig.inputs.size
  let argsOfLocals (locals : Locals) : List String :=
    let ctx := ctx.setLocals locals
    (locals.locals.toList.drop 1).take nArgs |>.map (LocalId.fmt ctx ·.index)
  let argNames := match decl.body with
    | .Unstructured b => argsOfLocals b.locals
    | .Structured b => argsOfLocals b.locals
    | .Intrinsic _ argNames .. => argNames.toList.zipIdx.map fun (name, i) =>
      s!"{name.getD ""}_{i + 1}"
    | .Error _ | .Extern _ | .Missing | .Opaque | .TargetDispatch _ =>
      (List.range nArgs).map (s!"_{· + 1}")
  let args := (sig.inputs.toList.zip argNames).map fun (ty, name) => s!"{name}: {Ty.fmt ctx ty}"
  let args := if sig.is_variadic then args ++ ["..."] else args
  let output := if sig.output.isUnit then "" else s!" -> {Ty.fmt ctx sig.output}"
  s!"{intro}{params}({sep ", " args}){output}{preds}{Body.fmt ctx decl.body}"

partial def GlobalDecl.fmt (ctx : Ctx) (decl : GlobalDecl) : String :=
  let keyword := match decl.global_kind with
    | .Static isMut isSafe isThreadLocal =>
      (if isSafe then "" else "unsafe ") ++ (if isThreadLocal then "thread_local" else "static") ++
        (if isMut then " mut" else "")
    | .AnonConst | .NamedConst => "const"
    | .VTable => "vtable"
  let intro := ItemMeta.fmtIntro ctx decl.item_meta keyword (.Global decl.def_id)
  let ctx := ctx.setGenerics decl.generics
  let (params, preds) := GenericParams.fmtWithClauses ctx decl.generics
  let md := if decl.ptr_metadata.ty.isUnit then "" else
    s!" with_metadata({ConstantExpr.fmt ctx decl.ptr_metadata})"
  s!"{intro}{params}: {Ty.fmt ctx decl.ty}{preds}" ++
    (if decl.generics.hasPredicates then "\n" else "") ++
    s!" = {ConstantExpr.fmt ctx decl.value}{md}"

partial def Field.fmt (ctx : Ctx) (f : Field) : String := s!"{f.name}: {Ty.fmt ctx f.ty}"

partial def Variant.fmt (ctx : Ctx) (v : Variant) : String :=
  v.name ++ (if v.fields.isEmpty then "" else
    " { " ++ sep ", " (v.fields.toList.map (Field.fmt ctx)) ++ " }")

partial def TypeDecl.fmt (ctx : Ctx) (decl : TypeDecl) : String :=
  let keyword := match decl.kind with
    | .Struct _ => "struct" | .Union _ => "union" | .Enum _ => "enum" | .Alias _ => "type"
    | .Opaque | .Error _ => "opaque type"
  let intro := ItemMeta.fmtIntro ctx decl.item_meta keyword (.«Type» decl.def_id)
  let ctx := { ctx.setGenerics decl.generics with currentType := some decl.def_id }
  let (params, preds) := GenericParams.fmtWithClauses ctx decl.generics
  let nlOrSpace := if decl.generics.hasPredicates then "\n" else " "
  let lines (xs : List String) : String := String.join (xs.map (s!"  {·},\n"))
  let body := match decl.kind with
    | .Struct fields =>
      nlOrSpace ++ "{" ++ (if fields.isEmpty then "" else "\n" ++ lines (fields.toList.map (Field.fmt ctx))) ++ "}"
    | .Union fields => nlOrSpace ++ "{\n" ++ lines (fields.toList.map (Field.fmt ctx)) ++ "}"
    | .Enum variants => nlOrSpace ++ "{\n" ++ lines (variants.toList.map (Variant.fmt ctx)) ++ "}"
    | .Alias ty => s!" = {Ty.fmt ctx ty}"
    | .Opaque => ""
    | .Error msg => s!" = ERROR({msg})"
  intro ++ params ++ preds ++ body

partial def TraitDecl.fmt (ctx : Ctx) (decl : TraitDecl) : String := Id.run do
  let ctx := ctx.setGenerics decl.generics
  let keyword := if decl.is_unsafe then "unsafe trait" else "trait"
  let mut out := ItemMeta.fmtIntro ctx decl.item_meta keyword (.TraitDecl decl.def_id)
  let (generics, clauses) := GenericParams.fmtWithClauses ctx decl.generics
  out := out ++ generics ++ clauses
  let types := decl.types.values
  let methods := decl.methods.values
  let consts := decl.consts.values
  if decl.implied_clauses.isEmpty && consts.isEmpty && types.isEmpty && methods.isEmpty then
    return out
  out := out ++ "\n{\n"
  for c in decl.implied_clauses.vec do
    out := out ++ s!"{tab}proof ImpliedClause{c.clause_id.index}: \
      {PolyTraitDeclRef.fmtAsPred ctx c.trait_}\n"
  for c in consts do
    out := out ++ s!"{tab}const {c.name} : {Ty.fmt ctx c.ty}\n"
  for assocTy in types do
    let ctx := ctx.pushBinder assocTy.params
    let clauses := GenericParams.fmtClauses ctx assocTy.params ++
      assocTy.skip_binder.implied_clauses.toList.map fun c =>
        s!"proof ImpliedClause{c.clause_id.index}: {PolyTraitDeclRef.fmtAsPred ctx c.trait_}"
    let params := if assocTy.params.hasExplicits then
      "<" ++ sep ", " (GenericParams.fmtParams ctx assocTy.params) ++ ">" else ""
    let default := (assocTy.skip_binder.default.map (s!" = {Ty.fmt ctx ·.value}")).getD ""
    out := out ++ s!"{tab}type {assocTy.skip_binder.name}{params}{default}\
      {fmtWhereClauses clauses tab}\n"
  for method in methods do
    for attr in method.skip_binder.item_meta.attr_info.attributes do
      if !(attr matches .DocComment _) then
        out := out ++ s!"{tab}{Attribute.fmt ctx attr}\n"
    let (params, body) := Binder.fmtSplit ctx method fun ctx m =>
      match m.default with
      | some f => s!" = {FunDeclRef.fmt ctx f}"
      | none => ";"
    out := out ++ s!"{tab}fn {method.skip_binder.name}{params}{body}\n"
  out := out ++ match decl.vtable with
    | some vtable => s!"{tab}vtable: {TypeDeclRef.fmt ctx vtable}\n"
    | none => s!"{tab}non-dyn-compatible\n"
  return out ++ "}"

partial def TraitImpl.fmt (ctx : Ctx) (decl : TraitImpl) : String := Id.run do
  let traitId := decl.impl_trait.id
  let mut out := s!"// Full name: {Name.fmtFull ctx decl.item_meta.name}\n"
  let ctx := ctx.setGenerics decl.generics
  let (generics, clauses) := GenericParams.fmtWithClauses ctx decl.generics
  if decl.is_unsafe then out := out ++ "unsafe "
  out := out ++ s!"impl{generics}"
  if let some short := ctx.traitImplShortName decl.def_id then
    out := out ++ s!" \"{Name.fmt ctx short}\""
  let negative := if decl.is_negative then "!" else ""
  out := out ++ s!" {negative}{TraitDeclRef.fmtAsImpl ctx decl.impl_trait}{clauses}"
  out := out ++ (if clauses.isEmpty then " " else "\n") ++ "{\n"
  for (id, tref) in IndexVec.enumerate decl.implied_trait_refs do
    out := out ++ tab ++ RegionBinder.fmtAsFor ctx tref (fun ctx tref =>
      s!"proof ImpliedClause{id.index}: ({TraitDeclRef.fmtAsPred ctx tref.trait_decl_ref}) = \
        {TraitRef.fmt ctx tref}") ++ "\n"
  for (constId, g) in IndexMap.enumerate decl.consts do
    out := out ++ s!"{tab}const {ctx.assocConstName traitId constId} = {GlobalDeclRef.fmt ctx g}\n"
  for (typeId, assocTy) in IndexMap.enumerate decl.types do
    let ctx := ctx.pushBinder assocTy.params
    let params := if assocTy.params.hasExplicits then
      "<" ++ sep ", " (GenericParams.fmtParams ctx assocTy.params) ++ ">" else ""
    let clauses := GenericParams.fmtClauses ctx assocTy.params ++
      (IndexVec.enumerate assocTy.skip_binder.implied_trait_refs).toList.map fun (id, tref) =>
        RegionBinder.fmtAsFor ctx tref fun ctx tref =>
          s!"proof ImpliedClause{id.index}: ({TraitDeclRef.fmtAsPred ctx tref.trait_decl_ref}) = \
            {TraitRef.fmt ctx tref}"
    out := out ++ s!"{tab}type {ctx.assocTypeName traitId typeId}{params} = \
      {Ty.fmt ctx assocTy.skip_binder.value}{fmtWhereClauses clauses tab}\n"
  for (methodId, f) in IndexMap.enumerate decl.methods do
    let (params, fref) := Binder.fmtSplit ctx f FunDeclRef.fmt
    out := out ++ s!"{tab}fn {ctx.methodName traitId methodId}{params} = {fref}\n"
  out := out ++ match decl.vtable with
    | .VTable g => s!"{tab}vtable: {GlobalDeclRef.fmt ctx g}\n"
    | .Lazy => s!"{tab}vtable: lazy\n"
    | .Unknown msg => s!"{tab}vtable: unknown // {msg}\n"
    | .NotDynCompatible => s!"{tab}non-dyn-compatible\n"
  return out ++ "}"

end

/-- Formats the item with this id. -/
def Ctx.fmtItem (ctx : Ctx) (id : ItemId) : String :=
  let krate := ctx.krate
  let item := match id with
    | .«Type» id => krate.type_decls.get? id |>.map (TypeDecl.fmt ctx)
    | .Fun id => krate.fun_decls.get? id |>.map (FunDecl.fmt ctx)
    | .Global id => krate.global_decls.get? id |>.map (GlobalDecl.fmt ctx)
    | .TraitDecl id => krate.trait_decls.get? id |>.map (TraitDecl.fmt ctx)
    | .TraitImpl id => krate.trait_impls.get? id |>.map (TraitImpl.fmt ctx)
  item.getD s!"Missing decl: {id.toPrettyString} ({ItemId.fmt ctx id})"

end Print

/-- Pretty-prints the whole crate. -/
def TranslatedCrate.toPrettyString (krate : TranslatedCrate) : String :=
  let ctx := Print.Ctx.new krate
  let ids : Array ItemId := match krate.ordered_decls with
    | some groups => groups.flatMap DeclarationGroup.ids
    | none =>
      -- Types, globals, traits, functions.
      (IndexMap.enumerate krate.type_decls).map (.«Type» ·.1) ++
      (IndexMap.enumerate krate.global_decls).map (.Global ·.1) ++
      (IndexMap.enumerate krate.trait_decls).map (.TraitDecl ·.1) ++
      (IndexMap.enumerate krate.trait_impls).map (.TraitImpl ·.1) ++
      (IndexMap.enumerate krate.fun_decls).map (.Fun ·.1)
  String.join (ids.toList.map (ctx.fmtItem · ++ "\n\n"))

end Charon
