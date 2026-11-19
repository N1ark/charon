/-!
Hand-written definitions that the generated AST (`Charon.Generated.Ast`) relies on.
-/

namespace Charon

/-- Strongly-typed indices, mirroring `charon_lib::ids::Idx`. Instances are generated for every id
type of the AST. -/
class Idx (α : Type) where
  index : α → Nat
  ofIndex : Nat → α

/-- A vector indexed by the strongly-typed index `I`; mirrors `charon_lib::ids::IndexVec`. -/
structure IndexVec (I : Type) (α : Type) where
  vec : Array α

/-- A map from the strongly-typed index `I` to values, where some indices may have no value;
mirrors `charon_lib::ids::IndexMap`. -/
structure IndexMap (I : Type) (α : Type) where
  vec : Array (Option α)

/-- Mirrors `core::ops::RangeInclusive`. -/
structure RangeInclusive (α : Type) where
  start : α
  «end» : α
  deriving Repr, BEq, Hashable, Inhabited

namespace IndexVec
variable {I α : Type}

instance [Repr α] : Repr (IndexVec I α) := ⟨fun v p => reprPrec v.vec p⟩
instance [BEq α] : BEq (IndexVec I α) := ⟨fun a b => a.vec == b.vec⟩
instance [Hashable α] : Hashable (IndexVec I α) := ⟨fun v => hash v.vec⟩
instance : Inhabited (IndexVec I α) := ⟨⟨#[]⟩⟩
instance : EmptyCollection (IndexVec I α) := ⟨⟨#[]⟩⟩

def size (v : IndexVec I α) : Nat := v.vec.size
def isEmpty (v : IndexVec I α) : Bool := v.vec.isEmpty
def toArray (v : IndexVec I α) : Array α := v.vec
def toList (v : IndexVec I α) : List α := v.vec.toList

instance [Idx I] : GetElem (IndexVec I α) I α (fun v i => Idx.index i < v.vec.size) where
  getElem v i h := v.vec[Idx.index i]

instance [Idx I] : GetElem? (IndexVec I α) I α (fun v i => Idx.index i < v.vec.size) where
  getElem? v i := v.vec[Idx.index i]?

/-- The elements along with their index. -/
def enumerate [Idx I] (v : IndexVec I α) : Array (I × α) :=
  v.vec.mapIdx fun i x => (Idx.ofIndex i, x)

end IndexVec

namespace IndexMap
variable {I α : Type}

instance [Repr α] : Repr (IndexMap I α) := ⟨fun v p => reprPrec v.vec p⟩
instance [BEq α] : BEq (IndexMap I α) := ⟨fun a b => a.vec == b.vec⟩
instance [Hashable α] : Hashable (IndexMap I α) := ⟨fun v => hash v.vec⟩
instance : Inhabited (IndexMap I α) := ⟨⟨#[]⟩⟩
instance : EmptyCollection (IndexMap I α) := ⟨⟨#[]⟩⟩

/-- The number of slots, including the empty ones. -/
def slotCount (v : IndexMap I α) : Nat := v.vec.size

def get? [Idx I] (v : IndexMap I α) (i : I) : Option α := v.vec[Idx.index i]?.join

instance [Idx I] : GetElem? (IndexMap I α) I α (fun v i => (v.get? i).isSome) where
  getElem v i h := (v.get? i).get h
  getElem? v i := v.get? i

/-- The present elements along with their index. -/
def enumerate [Idx I] (v : IndexMap I α) : Array (I × α) := Id.run do
  let mut out := #[]
  for h : i in [0:v.vec.size] do
    if let some x := v.vec[i] then
      out := out.push (Idx.ofIndex i, x)
  return out

/-- The present elements. -/
def values (v : IndexMap I α) : Array α := v.vec.filterMap id

end IndexMap

end Charon
