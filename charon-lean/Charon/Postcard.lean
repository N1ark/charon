import Charon.Basic

/-!
A decoder for the [postcard](https://postcard.jamesmunns.com/wire-format) format, used by the
generated deserializers in `Charon.Generated.OfPostcard`.

The whole input is kept in memory as a `ByteArray` and the decoders thread the current position
through an `EStateM`, which the Lean compiler turns into tight code: no intermediate allocations
apart from the decoded values themselves.
-/

namespace Charon.Postcard

structure State (σ : Type) where
  /-- The position of the next byte to read. -/
  pos : Nat
  /-- The deduplication tables (see `dedup`). -/
  tables : σ

/-- The decoding monad; `σ` is the type of the deduplication tables. -/
abbrev M (σ α : Type) := ReaderT ByteArray (EStateM String (State σ)) α

variable {σ α β : Type}

@[inline] def fail (msg : String) : M σ α := fun _ s =>
  .error s!"at byte {s.pos}: {msg}" s

@[inline] private def eof (s : State σ) : EStateM.Result String (State σ) α :=
  .error s!"at byte {s.pos}: unexpected end of input" s

@[inline] def u8 : M σ UInt8 := fun data s =>
  if h : s.pos < data.size then .ok data[s.pos] { s with pos := s.pos + 1 } else eof s

def bool : M σ Bool := do
  match ← u8 with
  | 0 => return false
  | 1 => return true
  | b => fail s!"invalid bool {b}"

/-- The multi-byte case of `varint`. -/
private def varintSlow (data : ByteArray) (maxBytes : Nat) (maxLast : UInt8) (s : State σ) :
    EStateM.Result String (State σ) UInt64 :=
  go 0 s.pos 0 0
where
  go (i pos : Nat) (shift acc : UInt64) : EStateM.Result String (State σ) UInt64 :=
    if hi : i ≥ maxBytes then
      .error s!"at byte {s.pos}: varint is too long" s
    else if h : pos < data.size then
      let b := data[pos]
      let acc := acc ||| ((b &&& 0x7f).toUInt64 <<< shift)
      if b &&& 0x80 == 0 then
        if i + 1 == maxBytes && b > maxLast then
          .error s!"at byte {s.pos}: varint is out of range" s
        else
          .ok acc { s with pos := pos + 1 }
      else
        go (i + 1) (pos + 1) (shift + 7) acc
    else
      eof { s with pos }
  termination_by maxBytes - i

/-- Reads an unsigned varint of at most `maxBytes` bytes, whose last byte is at most `maxLast`
(these two numbers depend on the bit width of the integer). -/
@[inline] def varint (maxBytes : Nat) (maxLast : UInt8) : M σ UInt64 := fun data s =>
  if h : s.pos < data.size then
    let b := data[s.pos]
    -- Fast path for the very common single-byte case.
    if b < 0x80 then .ok b.toUInt64 { s with pos := s.pos + 1 }
    else varintSlow data maxBytes maxLast s
  else eof s

@[inline] def u16 : M σ UInt16 := return (← varint 3 0x03).toUInt16
@[inline] def u32 : M σ UInt32 := return (← varint 5 0x0f).toUInt32
@[inline] def u64 : M σ UInt64 := varint 10 0x01
/-- `usize`s are serialized as `u64`s by 64-bit hosts. -/
@[inline] def usize : M σ USize := return (← u64).toUSize
/-- An `usize` (e.g. an index or a length), as a `Nat`. -/
@[inline] def nat : M σ Nat := return (← u64).toNat

/-- Signed integers are zigzag-encoded. -/
@[inline] private def unzigzag (z : UInt64) : UInt64 := (z >>> 1) ^^^ (0 - (z &&& 1))

@[inline] def i8 : M σ Int8 := return (← u8).toInt8
@[inline] def i16 : M σ Int16 := return (unzigzag (← varint 3 0x03)).toInt64.toInt16
@[inline] def i32 : M σ Int32 := return (unzigzag (← varint 5 0x0f)).toInt64.toInt32
@[inline] def i64 : M σ Int64 := return (unzigzag (← varint 10 0x01)).toInt64
@[inline] def isize : M σ ISize := return (← i64).toISize
/-- An `isize`, as an `Int`. -/
@[inline] def int : M σ Int := return (← i64).toInt

/-- Enum variants are identified by their index, as a `u32`. -/
@[inline] def variant : M σ Nat := return (← varint 5 0x0f).toNat

/-- Reads `len` raw bytes. -/
def bytes (len : Nat) : M σ ByteArray := fun data s =>
  if s.pos + len ≤ data.size then
    .ok (data.extract s.pos (s.pos + len)) { s with pos := s.pos + len }
  else eof s

def string : M σ String := do
  let bytes ← bytes (← nat)
  match String.fromUTF8? bytes with
  | some s => return s
  | none => fail "invalid UTF-8 string"

/-- Chars are serialized as strings. -/
def char : M σ Char := do
  let s ← string
  if s.length == 1 then return s.front else fail s!"expected a single char, got {s.quote}"

/-- Charon serializes 128-bit integers as strings. -/
def u128 : M σ Nat := do
  let s ← string
  match s.toNat? with
  | some n => return n
  | none => fail s!"invalid u128 {s.quote}"

/-- Charon serializes 128-bit integers as strings. -/
def i128 : M σ Int := do
  let s ← string
  match s.toInt? with
  | some n => return n
  | none => fail s!"invalid i128 {s.quote}"

def f32 : M σ Float32 := do
  let b ← bytes 4
  return Float32.ofBits ((b.get! 0).toUInt32 ||| ((b.get! 1).toUInt32 <<< 8) |||
    ((b.get! 2).toUInt32 <<< 16) ||| ((b.get! 3).toUInt32 <<< 24))

def f64 : M σ Float := do
  let b ← bytes 8
  return Float.ofBits (b.toUInt64LE!)

@[specialize] def array (f : M σ α) : M σ (Array α) := fun data s =>
  match nat data s with
  | .error e s => .error e s
  | .ok len s =>
    -- Each element takes at least one byte; checking this protects against huge allocations.
    if s.pos + len > data.size then
      .error s!"at byte {s.pos}: sequence length {len} exceeds the input size" s
    else
      go len (Array.mkEmpty len) data s
where
  go : Nat → Array α → M σ (Array α)
    | 0, acc => pure acc
    | n + 1, acc => do go n (acc.push (← f))

@[specialize] def option (f : M σ α) : M σ (Option α) := do
  match ← u8 with
  | 0 => return none
  | 1 => return some (← f)
  | b => fail s!"invalid option tag {b}"

@[inline] def pair (f : M σ α) (g : M σ β) : M σ (α × β) := do
  let a ← f
  let b ← g
  return (a, b)

@[inline] def rangeInclusive (f : M σ α) : M σ (RangeInclusive α) := do
  let start ← f
  let «end» ← f
  return { start, «end» }

@[inline] def indexVec {I : Type} (f : M σ α) : M σ (IndexVec I α) := return ⟨← array f⟩
@[inline] def indexMap {I : Type} (f : M σ α) : M σ (IndexMap I α) := return ⟨← array (option f)⟩

/-- Records a deduplicated value in its table, updating the table in place. -/
@[inline] private def storeDedup (get : σ → Array (Option α)) (set : σ → Array (Option α) → σ)
    (id : Nat) (v : α) : M σ Unit := fun _ s =>
  let { pos, tables } := s
  let arr := get tables
  -- Release the table's reference to `arr`, so that it can be updated in place.
  let tables := set tables #[]
  let arr := if id < arr.size then arr.set! id (some v) else
    (Nat.fold (id - arr.size) (fun _ _ arr => arr.push none) arr).push (some v)
  .ok () { pos, tables := set tables arr }

/-- Values that come up often are deduplicated in the serialized output (see
`charon_lib::utils::dedup`): the first occurrence of a value is serialized in full along with an id,
later occurrences only mention that id. `get` and `set` access the table of values of this type. -/
@[inline] def dedup (get : σ → Array (Option α)) (set : σ → Array (Option α) → σ) (f : M σ α) :
    M σ α := do
  match ← variant with
  | 0 =>
    let id ← u32
    let v ← f
    storeDedup get set id.toNat v
    return v
  | 1 =>
    let id ← u32
    match (get (← getThe (State σ)).tables)[id.toNat]? with
    | some (some v) => return v
    | _ => fail s!"deduplicated value {id} was not previously defined; \
        the Rust and Lean (de)serializers are likely out of sync"
  | 2 => f
  | n => fail s!"invalid deduplicated value tag {n}"

@[inline] def atEnd : M σ Bool := fun data s => .ok (s.pos ≥ data.size) s

/-- Decodes `data` with `x`, returning the decoded value and the position after it. -/
def run (x : M σ α) (data : ByteArray) (tables : σ) : Except String (α × Nat) :=
  match x data { pos := 0, tables } with
  | .ok a s => .ok (a, s.pos)
  | .error e _ => .error e

end Charon.Postcard
