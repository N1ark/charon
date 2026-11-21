//! An opt-in persistent cache of translated items, shared across charon invocations. Set
//! `CHARON_TRANSLATION_CACHE` to enable it.
//!
//! The unit of caching is the translation of one item (`translate_item`). An item can be cached if
//! its `TransItemSource` mentions no item of the local crate and has a session-independent
//! encoding (`DefPathHash`es instead of `DefId`s, see [`KeyEncoder`]). The hash of that encoding
//! is the item's key.
//!
//! The cache is a snapshot of the items that earlier sessions stored, with their ids. A session
//! loads it before it registers items of its own and gives the snapshot's items and files the same
//! ids, so that stored values load as they are. The new items a session can store get the next ids
//! of the snapshot; at the end, the session writes the snapshot it loaded plus these items.
//!
//! Besides producing the item, translating it registers (and maybe enqueues) the items it refers
//! to. We record these registrations and store them with the item. Loading an item replays them,
//! and the other effects of its translation on the translation context that we know how to replay
//! (see [`Effect`]). We don't store items whose translation has effects we can't replay (errors,
//! linking extern functions, ...).
//!
//! We also store the name of each item, with the registrations computing it did. This lets us
//! register the items that a loaded item refers to without decoding their sources ("unbound"
//! items): decoding is costly, as it resolves trait references. We decode the source of an unbound
//! item only when we need it, e.g. to translate the item if its translation isn't cached.
//!
//! Translation rarely reads translated items, so loading an item only replays its registrations
//! and effects: we decode most items at the end of the translation, in parallel.
//!
//! The snapshot lives in `$CHARON_TRANSLATION_CACHE/<env>/`, where `<env>` hashes everything else
//! the translation depends on: the charon binary, the options and the upstream crates.
use std::path::PathBuf;
use std::rc::Rc;

use rayon::prelude::*;
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::memmap::Mmap;
use rustc_data_structures::stable_hash::StableHasher;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash, LOCAL_CRATE, StableCrateId};
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc};
use rustc_middle::ty::codec::{TyDecoder, TyEncoder};
use rustc_middle::ty::{self, TyCtxt};
use rustc_serialize::opaque::{MAGIC_END_BYTES, MemDecoder};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder, leb128};
use rustc_span::{
    AttrId, BlobDecoder, ByteSymbol, DUMMY_SP, ExpnId, Span, SpanDecoder, SpanEncoder, Symbol,
    SyntaxContext,
};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};
use serde_state_perfect_derive as serde_state;

use super::translate_crate::RustcItem;
use super::translate_ctx::*;
use crate::hax;
use crate::hax::{AssocItemResolution, BaseState, DefIdBase, SInto, SyntheticItem};
use charon_lib::ast::*;
use charon_lib::options::CliOpts;

/// Encodes rustc data in a session-independent way.
struct KeyEncoder<'tcx> {
    tcx: TyCtxt<'tcx>,
    buf: Vec<u8>,
    /// Whether we met something that has no session-independent encoding.
    unencodable: bool,
    /// Whether we met an item of the local crate.
    mentions_local: bool,
    /// Whether we met an allocation. Decoding creates a new one with the same contents.
    mentions_alloc: bool,
    type_shorthands: FxHashMap<ty::Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
}

macro_rules! emit_leb128 {
    ($name:ident, $ty:ty, $write:ident) => {
        fn $name(&mut self, v: $ty) {
            let mut out = [0u8; leb128::max_leb128_len::<$ty>()];
            let n = leb128::$write(&mut out, v);
            self.buf.extend_from_slice(&out[..n]);
        }
    };
}

// The same format as `FileEncoder`, so that `MemDecoder` can read it.
impl Encoder for KeyEncoder<'_> {
    emit_leb128!(emit_usize, usize, write_usize_leb128);
    emit_leb128!(emit_u128, u128, write_u128_leb128);
    emit_leb128!(emit_u64, u64, write_u64_leb128);
    emit_leb128!(emit_u32, u32, write_u32_leb128);
    emit_leb128!(emit_isize, isize, write_isize_leb128);
    emit_leb128!(emit_i128, i128, write_i128_leb128);
    emit_leb128!(emit_i64, i64, write_i64_leb128);
    emit_leb128!(emit_i32, i32, write_i32_leb128);
    fn emit_u16(&mut self, v: u16) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }
    fn emit_i16(&mut self, v: i16) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }
    fn emit_u8(&mut self, v: u8) {
        self.buf.push(v);
    }
    fn emit_raw_bytes(&mut self, s: &[u8]) {
        self.buf.extend_from_slice(s);
    }
}

impl SpanEncoder for KeyEncoder<'_> {
    // Decoded as a dummy span; the round-trip check rejects keys where that matters.
    fn encode_span(&mut self, _span: Span) {}
    fn encode_symbol(&mut self, sym: Symbol) {
        self.emit_str(sym.as_str());
    }
    fn encode_byte_symbol(&mut self, sym: ByteSymbol) {
        self.emit_byte_str(sym.as_byte_str());
    }
    fn encode_expn_id(&mut self, _: ExpnId) {
        self.unencodable = true;
    }
    fn encode_syntax_context(&mut self, _: SyntaxContext) {
        self.unencodable = true;
    }
    fn encode_crate_num(&mut self, cnum: CrateNum) {
        self.mentions_local |= cnum == LOCAL_CRATE;
        self.tcx.stable_crate_id(cnum).encode(self);
    }
    fn encode_def_index(&mut self, _: DefIndex) {
        self.unencodable = true;
    }
    fn encode_def_id(&mut self, def_id: DefId) {
        self.mentions_local |= def_id.is_local();
        self.tcx.def_path_hash(def_id).encode(self);
    }
}

impl<'tcx> TyEncoder<'tcx> for KeyEncoder<'tcx> {
    const CLEAR_CROSS_CRATE: bool = true;
    fn position(&self) -> usize {
        self.buf.len()
    }
    fn type_shorthands(&mut self) -> &mut FxHashMap<ty::Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }
    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }
    fn encode_alloc_id(&mut self, alloc_id: &AllocId) {
        self.mentions_alloc = true;
        let alloc = self.tcx.global_alloc(*alloc_id);
        if let GlobalAlloc::Memory(mem) = alloc
            && mem.inner().mutability.is_mut()
        {
            // We can't tell whether another item refers to the same mutable memory.
            self.unencodable = true;
        }
        alloc.encode(self);
    }
}

/// Decodes what [`KeyEncoder`] encoded, in the current session.
struct KeyDecoder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: MemDecoder<'a>,
}

rustc_middle::implement_ty_decoder!(KeyDecoder<'a, 'tcx>);

impl<'tcx> TyDecoder<'tcx> for KeyDecoder<'_, 'tcx> {
    const CLEAR_CROSS_CRATE: bool = true;
    fn cached_ty_for_shorthand<F>(&mut self, _shorthand: usize, or_insert_with: F) -> ty::Ty<'tcx>
    where
        F: FnOnce(&mut Self) -> ty::Ty<'tcx>,
    {
        or_insert_with(self)
    }
    fn with_position<F, R>(&mut self, pos: usize, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let new_opaque = self.opaque.split_at(pos);
        let old_opaque = std::mem::replace(&mut self.opaque, new_opaque);
        let r = f(self);
        self.opaque = old_opaque;
        r
    }
    fn decode_alloc_id(&mut self) -> AllocId {
        let tcx = self.tcx;
        match GlobalAlloc::decode(self) {
            // A new allocation, as its view may differ from that of an existing one.
            GlobalAlloc::Memory(mem) => tcx.reserve_and_set_memory_alloc(mem),
            GlobalAlloc::Function { instance } => tcx.reserve_and_set_fn_alloc(instance, 0),
            GlobalAlloc::VTable(ty, preds) => tcx.reserve_and_set_vtable_alloc(ty, preds, 0),
            GlobalAlloc::TypeId { ty } => tcx.reserve_and_set_type_id_alloc(ty),
            GlobalAlloc::Static(def_id) => tcx.reserve_and_set_static_alloc(def_id),
        }
    }
}

impl<'tcx> rustc_type_ir::InternerDecoder for KeyDecoder<'_, 'tcx> {
    type Interner = TyCtxt<'tcx>;
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl SpanDecoder for KeyDecoder<'_, '_> {
    fn decode_span(&mut self) -> Span {
        DUMMY_SP
    }
    fn decode_expn_id(&mut self) -> ExpnId {
        unreachable!("expansion ids are not encoded")
    }
    fn decode_syntax_context(&mut self) -> SyntaxContext {
        unreachable!("syntax contexts are not encoded")
    }
    fn decode_crate_num(&mut self) -> CrateNum {
        let id = StableCrateId::decode(self);
        self.tcx.stable_crate_id_to_crate_num(id)
    }
    fn decode_def_id(&mut self) -> DefId {
        let hash = DefPathHash::decode(self);
        self.tcx
            .def_path_hash_to_def_id(hash)
            .expect("cached item refers to an unknown item")
    }
    fn decode_attr_id(&mut self) -> AttrId {
        unreachable!("attribute ids are not encoded")
    }
}

impl BlobDecoder for KeyDecoder<'_, '_> {
    fn decode_symbol(&mut self) -> Symbol {
        Symbol::intern(self.read_str())
    }
    fn decode_byte_symbol(&mut self) -> ByteSymbol {
        ByteSymbol::intern(self.read_byte_str())
    }
    fn decode_def_index(&mut self) -> DefIndex {
        unreachable!("def indices are not encoded")
    }
}

fn encode_kind(e: &mut KeyEncoder<'_>, kind: TransItemSourceKind) {
    let bytes = postcard::to_allocvec(&kind).unwrap();
    e.emit_usize(bytes.len());
    e.emit_raw_bytes(&bytes);
}

fn decode_kind(d: &mut KeyDecoder<'_, '_>) -> TransItemSourceKind {
    let len = d.read_usize();
    postcard::from_bytes(d.read_raw_bytes(len)).unwrap()
}

fn encode_def_id<'tcx>(
    e: &mut KeyEncoder<'tcx>,
    s: &hax::StateWithBase<'tcx>,
    def_id: &hax::DefId,
) {
    match def_id.base {
        DefIdBase::Real(did) => {
            e.emit_u8(0);
            did.encode(e);
        }
        DefIdBase::Promoted(did, promoted) => {
            e.emit_u8(1);
            did.encode(e);
            e.emit_u32(promoted.as_u32());
        }
        DefIdBase::ImplAssocItem(item) => {
            e.emit_u8(2);
            item.trait_impl_id.encode(e);
            item.item_decl_id.encode(e);
            item.item_impl_id.encode(e);
        }
        DefIdBase::Synthetic(synth) => {
            e.emit_u8(3);
            match synth {
                SyntheticItem::Array => e.emit_u8(0),
                SyntheticItem::Slice => e.emit_u8(1),
                SyntheticItem::Str => e.emit_u8(2),
                SyntheticItem::Tuple(n) => {
                    e.emit_u8(3);
                    e.emit_usize(n);
                }
                SyntheticItem::FnPtr(shape) => {
                    e.emit_u8(4);
                    shape.sig(s).encode(e);
                }
            }
        }
        DefIdBase::Alloc(alloc_id) => {
            // The translation of the allocation depends on the type we view it at, which is
            // decided when we first read it. We can't encode it until then.
            match s.global_cache().alloc_types.decided_view(alloc_id) {
                Some(view) => {
                    e.emit_u8(4);
                    alloc_id.encode(e);
                    view.encode(e);
                }
                None => e.unencodable = true,
            }
        }
    }
}

/// With `!number_allocs`, the decoded allocations are not numbered for naming: we use this to
/// check keys without changing the names of the allocations of the session.
fn decode_def_id<'tcx>(
    d: &mut KeyDecoder<'_, 'tcx>,
    s: &hax::StateWithBase<'tcx>,
    number_allocs: bool,
) -> hax::DefId {
    match d.read_u8() {
        0 => DefId::decode(d).sinto(s),
        1 => {
            let parent: hax::DefId = DefId::decode(d).sinto(s);
            let promoted = rustc_middle::mir::Promoted::from_u32(d.read_u32());
            parent.make_promoted_child(s, promoted)
        }
        2 => {
            let trait_impl_id = DefId::decode(d);
            let item_decl_id = DefId::decode(d);
            let item_impl_id = DefId::decode(d);
            hax::DefId::make_assoc_item_impl(
                s,
                hax::VirtualImplAssocItem {
                    trait_impl_id,
                    item_decl_id,
                    item_impl_id,
                },
            )
        }
        3 => {
            let synth = match d.read_u8() {
                0 => SyntheticItem::Array,
                1 => SyntheticItem::Slice,
                2 => SyntheticItem::Str,
                3 => SyntheticItem::Tuple(d.read_usize()),
                4 => SyntheticItem::FnPtr(hax::FnPtrShape::erase(ty::PolyFnSig::decode(d))),
                _ => unreachable!(),
            };
            hax::DefId::make_synthetic(s, synth)
        }
        4 => {
            let alloc_id = AllocId::decode(d);
            let view = Option::<ty::Ty<'tcx>>::decode(d);
            s.global_cache().alloc_types.decide_view(alloc_id, view);
            if number_allocs {
                hax::DefId::make_anon_alloc(s, alloc_id)
            } else {
                hax::DefId::make_anon_alloc_unnumbered(s, alloc_id)
            }
        }
        _ => unreachable!(),
    }
}

const RESOLUTIONS: [AssocItemResolution; 3] = [
    AssocItemResolution::ImplItem,
    AssocItemResolution::None,
    AssocItemResolution::TraitProof,
];

fn decode_src<'tcx>(
    tcx: TyCtxt<'tcx>,
    s: &hax::StateWithBase<'tcx>,
    bytes: &[u8],
    number_allocs: bool,
) -> TransItemSource<'tcx> {
    let mut d = KeyDecoder {
        tcx,
        opaque: MemDecoder::new(bytes, 0).unwrap(),
    };
    let kind = decode_kind(&mut d);
    let item = match d.read_u8() {
        0 => RustcItem::Poly(decode_def_id(&mut d, s, number_allocs)),
        1 => {
            let def_id = decode_def_id(&mut d, s, number_allocs);
            let args = ty::GenericArgsRef::decode(&mut d);
            let resolution = RESOLUTIONS[d.read_u8() as usize];
            let s = s.clone().with_hax_owner(&def_id);
            RustcItem::Mono(hax::ItemRef::translate_from_hax_def_id_maybe_resolve(
                &s, def_id, args, resolution,
            ))
        }
        2 => RustcItem::MonoTrait(decode_def_id(&mut d, s, number_allocs)),
        _ => unreachable!(),
    };
    TransItemSource { item, kind }
}

/// The session-independent identity of an item.
pub(crate) struct ItemKey {
    hash: u128,
    /// Encoding of the `TransItemSource`, decoded by `decode_src`.
    encoded: Vec<u8>,
}

impl<'tcx> KeyEncoder<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        KeyEncoder {
            tcx,
            buf: Vec::new(),
            unencodable: false,
            mentions_local: false,
            mentions_alloc: false,
            type_shorthands: Default::default(),
            predicate_shorthands: Default::default(),
        }
    }
}

/// A hash of the contents of an immutable allocation (with those of the allocations it points to)
/// and of the type we view it at: equal hashes mean equal translations. `None` if the allocation
/// is mutable.
pub(crate) fn anon_alloc_contents<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc_id: AllocId,
    view: Option<ty::Ty<'tcx>>,
) -> Option<Fingerprint> {
    let mut e = KeyEncoder::new(tcx);
    alloc_id.encode(&mut e);
    view.encode(&mut e);
    let mut hasher = StableHasher::new();
    std::hash::Hasher::write(&mut hasher, &e.buf);
    (!e.unencodable).then(|| hasher.finish())
}

/// Encode the source without the choice of resolution. Returns `None` if that's not possible.
fn encode_src<'tcx>(
    tcx: TyCtxt<'tcx>,
    s: &hax::StateWithBase<'tcx>,
    src: &TransItemSource<'tcx>,
) -> Option<KeyEncoder<'tcx>> {
    let mut e = KeyEncoder::new(tcx);
    encode_kind(&mut e, src.kind);
    match &src.item {
        RustcItem::Poly(def_id) => {
            e.emit_u8(0);
            encode_def_id(&mut e, s, def_id);
        }
        RustcItem::Mono(item) => {
            e.emit_u8(1);
            encode_def_id(&mut e, s, &item.def_id);
            item.rustc_args(s).encode(&mut e);
        }
        RustcItem::MonoTrait(def_id) => {
            e.emit_u8(2);
            encode_def_id(&mut e, s, def_id);
        }
    }
    (!e.unencodable && !e.mentions_local).then_some(e)
}

/// Compute the key of this source, if it has one, i.e. if it doesn't mention the local crate and
/// its encoding round-trips.
fn compute_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    s: &hax::StateWithBase<'tcx>,
    src: &TransItemSource<'tcx>,
) -> Option<ItemKey> {
    let e = encode_src(tcx, s, src)?;
    let base = e.buf;
    // Find an encoding that decodes back to the same source. Decoding allocations creates new
    // ones, so for those we compare encodings instead.
    let decodes_back = |encoded: &[u8]| {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let decoded = decode_src(tcx, s, encoded, false);
            if e.mentions_alloc {
                encode_src(tcx, s, &decoded).is_some_and(|e| e.buf == base)
            } else {
                decoded == *src
            }
        }))
        .unwrap_or(false)
    };
    let resolution_choices = match src.item {
        RustcItem::Mono(_) => 0..RESOLUTIONS.len() as u8,
        _ => 0..1,
    };
    let encoded = resolution_choices
        .map(|i| {
            let mut encoded = base.clone();
            if matches!(src.item, RustcItem::Mono(_)) {
                encoded.push(i);
            }
            // `MemDecoder` expects this suffix.
            encoded.extend_from_slice(MAGIC_END_BYTES);
            encoded
        })
        .find(|encoded| decodes_back(encoded))?;
    let mut hasher = StableHasher::new();
    std::hash::Hasher::write(&mut hasher, &encoded);
    let (hi, lo) = hasher.finish::<Fingerprint>().split();
    Some(ItemKey {
        hash: (u128::from(hi.as_u64()) << 64) | u128::from(lo.as_u64()),
        encoded,
    })
}

/// What the translation of an item, or the computation of the name of a new item, did apart from
/// producing its result.
pub(crate) struct Recorder {
    /// The items it registered, and whether it enqueued them.
    refs: indexmap::IndexMap<ItemId, bool>,
    /// Its effects on method usage tracking.
    effects: Vec<Effect>,
    /// Why the translation can't be replayed from the cache, if it can't.
    tainted: Option<&'static str>,
    errors_before: usize,
    /// Whether this records a computation memoized across items.
    memo: bool,
}

/// A computation memoized across items.
#[derive(PartialEq, Eq, Hash)]
pub(crate) enum MemoKey<'tcx> {
    /// See `cached_names`.
    Name(RustcItem<'tcx>),
    /// See `mono_type_cache`.
    Ty(hax::Ty<'tcx>),
    /// See `cached_item_metas`.
    ItemMeta(TransItemSource<'tcx>),
    /// See `cached_attr_infos`.
    AttrInfo(hax::DefId),
}

impl Recorder {
    fn merge(&mut self, other: &Recorder) {
        for (&id, &enqueue) in &other.refs {
            *self.refs.entry(id).or_default() |= enqueue;
        }
        for effect in &other.effects {
            if !self.effects.contains(effect) {
                self.effects.push(effect.clone());
            }
        }
        if self.tainted.is_none() {
            self.tainted = other.tainted;
        }
    }
}

/// An effect of a translation on the translation context, besides registering items.
#[derive(Clone, PartialEq, SerializeState, DeserializeState)]
pub(crate) enum Effect {
    /// `register_assoc_items` of this trait.
    RegisterAssocItems(TraitDeclId),
    /// `mark_method_as_used` of this method.
    MarkMethodUsed(TraitDeclId, TraitMethodId),
    /// This vtable of this impl was translated, see `settle_vtables`.
    TranslatedVTable(TraitImplId, GlobalDeclRef),
}

/// An item that a stored computation registered, and whether it enqueued it.
type StoredRef = (ItemId, bool);

/// Where a value is in the snapshot: offset and length.
type Loc = (u64, u64);

/// A stored item.
#[derive(Clone, Serialize, Deserialize)]
struct IndexEntry {
    hash: [u8; 16],
    id: ItemId,
    /// The encoding of its source, see `ItemKey`.
    key: Loc,
    /// The registrations computing its name did, and its name: `(Vec<StoredRef>, &[u8])`.
    name: Option<Loc>,
    /// The registrations translating it did, its effects (`Vec<Effect>`) and the item without its
    /// name (`CachedItem`): `(Vec<StoredRef>, &[u8], &[u8])`. AST values are serialized with a
    /// `DedupSerializer` each.
    body: Option<Loc>,
}

#[derive(SerializeState, DeserializeState)]
enum CachedItem {
    Type(TypeDecl),
    Fun(FunDecl),
    Global(GlobalDecl),
    TraitDecl(TraitDecl),
    TraitImpl(TraitImpl),
}

/// Numbers of ids: of types, functions, globals, trait decls and trait impls, then of files.
type Counts = [u32; 6];

fn counts_of(krate: &TranslatedCrate) -> Counts {
    [
        krate.type_decls.slot_count() as u32,
        krate.fun_decls.slot_count() as u32,
        krate.global_decls.slot_count() as u32,
        krate.trait_decls.slot_count() as u32,
        krate.trait_impls.slot_count() as u32,
        krate.files.len() as u32,
    ]
}

/// The position of the kind of this id in `Counts`, and its index.
fn kind_and_index(id: ItemId) -> (usize, usize) {
    match id {
        ItemId::Type(id) => (0, id.index()),
        ItemId::Fun(id) => (1, id.index()),
        ItemId::Global(id) => (2, id.index()),
        ItemId::TraitDecl(id) => (3, id.index()),
        ItemId::TraitImpl(id) => (4, id.index()),
    }
}

fn make_item_id(kind: usize, index: usize) -> ItemId {
    match kind {
        0 => ItemId::Type(TypeDeclId::from_usize(index)),
        1 => ItemId::Fun(FunDeclId::from_usize(index)),
        2 => ItemId::Global(GlobalDeclId::from_usize(index)),
        3 => ItemId::TraitDecl(TraitDeclId::from_usize(index)),
        _ => ItemId::TraitImpl(TraitImplId::from_usize(index)),
    }
}

/// A snapshot is the values of its items, this header, the length of the header as a `u64`, and
/// `SNAPSHOT_MAGIC`.
#[derive(Default, Serialize, Deserialize)]
struct Header {
    /// The ids sessions give out before they load the snapshot.
    prefix: Counts,
    /// The ids of the items and files of the snapshot are below these.
    counts: Counts,
    /// The files of the snapshot, which come after those of the prefix.
    files: Vec<File>,
    /// The stored items.
    index: Vec<IndexEntry>,
}

const SNAPSHOT_MAGIC: &[u8; 8] = b"CHRNSNP1";

/// Read the header of a snapshot, and the end of its values.
fn read_header(bytes: &[u8]) -> Option<(Header, usize)> {
    let footer_start = bytes.len().checked_sub(16)?;
    if &bytes[footer_start + 8..] != SNAPSHOT_MAGIC {
        return None;
    }
    let len = u64::from_le_bytes(bytes[footer_start..footer_start + 8].try_into().ok()?) as usize;
    let start = footer_start.checked_sub(len)?;
    Some((postcard::from_bytes(&bytes[start..footer_start]).ok()?, start))
}

#[derive(Default, Debug)]
pub(crate) struct CacheStats {
    unbound: usize,
    hits: usize,
    misses: usize,
    stored: usize,
    tainted: HashMap<&'static str, usize>,
}

type Range = std::ops::Range<usize>;

pub(crate) struct TranslationCache<'tcx> {
    dir: PathBuf,
    /// The snapshot we loaded, its header, where its values end, and its length and modification
    /// time when we loaded it.
    snapshot: Option<Mmap>,
    header: Header,
    values_end: usize,
    stamp: Option<(u64, std::time::SystemTime)>,
    /// Whether we loaded the snapshot (or found none), after which new items get ids above it.
    loaded: bool,
    /// The position in `header.index` of each item of the snapshot.
    entries: HashMap<ItemId, usize>,
    /// The ids of the items that have a key: those of the snapshot and the new ones.
    by_hash: HashMap<u128, ItemId>,
    /// The keys of the items registered by this session that have one, and the reverse map.
    keys: HashMap<ItemId, Rc<ItemKey>>,
    /// The key of the item we are registering, if we already know it.
    known_key: Option<(TransItemSource<'tcx>, Rc<ItemKey>)>,
    /// The items of the snapshot registered without their source (see `cache_register_ref`).
    unbound: HashSet<ItemId>,
    /// The ids in the next snapshot of the items and files of this session above the snapshot that
    /// we can store, the reverse map for items, the new files in order, and the next free ids.
    store_ids: HashMap<ItemId, ItemId>,
    from_store_ids: HashMap<ItemId, ItemId>,
    store_files: HashMap<FileId, FileId>,
    new_files: Vec<FileId>,
    next: Counts,
    /// The translations this session stored, serialized as `IndexEntry::body`, by id in the next
    /// snapshot.
    bodies: HashMap<ItemId, Vec<u8>>,
    /// One recorder per `translate_item` or name computation in progress.
    recorders: Vec<Recorder>,
    /// What computing the names of the items we registered did.
    name_records: HashMap<ItemId, Recorder>,
    /// What the computations memoized across items did.
    memos: HashMap<MemoKey<'tcx>, Recorder>,
    /// Unbound items that we must translate, and those we tried to translate.
    unbound_queue: std::collections::VecDeque<ItemId>,
    processed_unbound: HashSet<ItemId>,
    /// The files of the local crate.
    pub(crate) local_files: HashSet<FileId>,
    /// The loaded items we haven't decoded yet (the range of the item and its name), and those whose
    /// decoding failed.
    pending: HashMap<ItemId, (Range, Name)>,
    failed: HashSet<ItemId>,
    stats: CacheStats,
}

/// Decode a value stored in the cache.
fn decode_value<T: for<'de> DeserializeState<'de, DedupSerializer>>(bytes: &[u8]) -> Option<T> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let state = DedupSerializer::default();
        T::deserialize_state(&state, &mut postcard::Deserializer::from_bytes(bytes)).ok()
    }))
    .ok()
    .flatten()
}

fn encode_value<T: SerializeState<DedupSerializer>>(value: &T) -> Option<Vec<u8>> {
    let state = DedupSerializer::default();
    postcard::to_allocvec(&serde_state::WithState::new(value, &state)).ok()
}

impl<'tcx> TranslationCache<'tcx> {
    /// Set up the cache if `CHARON_TRANSLATION_CACHE` is set.
    pub(crate) fn new(tcx: TyCtxt<'tcx>, options: &CliOpts) -> Option<Self> {
        let root = std::env::var_os("CHARON_TRANSLATION_CACHE")?;
        let mut hasher = StableHasher::new();
        let mut hash_str = |s: &str| std::hash::Hasher::write(&mut hasher, s.as_bytes());
        // The charon binary.
        let exe = std::env::current_exe().ok()?;
        let meta = std::fs::metadata(&exe).ok()?;
        hash_str(&format!(
            "{} {} {:?}",
            exe.display(),
            meta.len(),
            meta.modified().ok()
        ));
        hash_str(charon_lib::VERSION);
        // The options, except those that only affect outputs or the choice of items.
        let mut opts = serde_json::to_value(options).ok()?;
        let obj = opts.as_object_mut()?;
        obj.retain(|k, _| {
            !(k.starts_with("print_")
                || k.starts_with("start_from")
                || matches!(
                    k.as_str(),
                    "dest_dir"
                        | "dest_file"
                        | "format"
                        | "no_serialize"
                        | "abort_on_error"
                        | "error_on_warnings"
                        | "run_with_minirust"
                ))
        });
        hash_str(&opts.to_string());
        // The target and the upstream crates.
        hash_str(tcx.sess.opts.target_triple.tuple());
        for &cnum in tcx.crates(()) {
            hash_str(&format!(
                "{} {:?} {:?}",
                tcx.crate_name(cnum),
                tcx.stable_crate_id(cnum),
                tcx.crate_hash(cnum)
            ));
        }
        let env: Fingerprint = hasher.finish();
        let dir = PathBuf::from(root).join(env.to_hex());
        std::fs::create_dir_all(&dir).ok()?;
        Some(Self {
            dir,
            snapshot: None,
            header: Default::default(),
            values_end: 0,
            stamp: None,
            loaded: false,
            entries: Default::default(),
            by_hash: Default::default(),
            keys: Default::default(),
            known_key: None,
            unbound: Default::default(),
            store_ids: Default::default(),
            from_store_ids: Default::default(),
            store_files: Default::default(),
            new_files: Default::default(),
            next: Default::default(),
            bodies: Default::default(),
            recorders: Default::default(),
            name_records: Default::default(),
            memos: Default::default(),
            unbound_queue: Default::default(),
            processed_unbound: Default::default(),
            local_files: Default::default(),
            pending: Default::default(),
            failed: Default::default(),
            stats: Default::default(),
        })
    }

    fn snapshot_path(&self) -> PathBuf {
        self.dir.join("snapshot")
    }

    fn entry(&self, id: ItemId) -> Option<&IndexEntry> {
        Some(&self.header.index[*self.entries.get(&id)?])
    }

    fn bytes(&self, (offset, len): Loc) -> &[u8] {
        &self.snapshot.as_ref().unwrap()[offset as usize..(offset + len) as usize]
    }

    fn slice(&self, range: Range) -> &[u8] {
        &self.snapshot.as_ref().unwrap()[range]
    }

    /// The range of this part of the snapshot.
    fn range_of(&self, bytes: &[u8]) -> Range {
        let start = bytes.as_ptr() as usize - self.snapshot.as_ref().unwrap().as_ptr() as usize;
        start..start + bytes.len()
    }

    /// The stored name of this item of the snapshot, and the registrations computing it did.
    fn stored_name(&self, id: ItemId) -> Option<(Vec<StoredRef>, Range)> {
        let (refs, name): (Vec<StoredRef>, &[u8]) =
            postcard::from_bytes(self.bytes(self.entry(id)?.name?)).ok()?;
        Some((refs, self.range_of(name)))
    }

    /// The stored translation of this item of the snapshot: registrations, effects and item.
    fn stored_body(&self, id: ItemId) -> Option<(Vec<StoredRef>, Range, Range)> {
        let (refs, effects, item): (Vec<StoredRef>, &[u8], &[u8]) =
            postcard::from_bytes(self.bytes(self.entry(id)?.body?)).ok()?;
        Some((refs, self.range_of(effects), self.range_of(item)))
    }

    /// The id in the next snapshot of this item, if it has one. The items of the snapshot and of the
    /// prefix keep theirs.
    fn store_id(&self, id: ItemId) -> Option<ItemId> {
        let (kind, index) = kind_and_index(id);
        if index < self.header.counts[kind] as usize {
            Some(id)
        } else {
            self.store_ids.get(&id).copied()
        }
    }

    /// The id in the next snapshot of this file, if it has one.
    fn store_file(&self, id: FileId) -> Option<FileId> {
        if id.index() < self.header.counts[5] as usize {
            Some(id)
        } else {
            self.store_files.get(&id).copied()
        }
    }

    /// Whether we can store this item: it has a key.
    fn has_key(&self, id: ItemId) -> bool {
        self.keys.contains_key(&id) || self.entries.contains_key(&id)
    }

    /// Record the key of a new item, and give it an id in the next snapshot.
    fn add_key(&mut self, id: ItemId, key: Rc<ItemKey>) {
        let first = *self.by_hash.entry(key.hash).or_insert(id);
        self.keys.insert(id, key);
        let (kind, index) = kind_and_index(id);
        if !self.loaded || index < self.header.counts[kind] as usize {
            return;
        }
        let store_id = match self.store_id(first) {
            // Allocations with the same contents and view have the same key: they share an item.
            Some(store_id) if first != id => store_id,
            _ => {
                let store_id = make_item_id(kind, self.next[kind] as usize);
                self.next[kind] += 1;
                self.from_store_ids.insert(store_id, id);
                store_id
            }
        };
        self.store_ids.insert(id, store_id);
    }

    pub(crate) fn pop_unbound(&mut self) -> Option<ItemId> {
        self.unbound_queue.pop_front()
    }

    /// Record a new file of the session.
    pub(crate) fn register_file(&mut self, id: FileId, is_local: bool) {
        if is_local {
            self.local_files.insert(id);
        } else if self.loaded {
            self.store_files
                .insert(id, FileId::from_usize(self.next[5] as usize));
            self.next[5] += 1;
            self.new_files.push(id);
        }
    }
}

/// Renumbers a value of the session to store it in the next snapshot.
#[derive(derive_generic_visitor::Visitor)]
struct ToStored<'a, 'tcx> {
    cache: &'a TranslationCache<'tcx>,
    /// Whether every id has an id in the next snapshot.
    ok: bool,
}

impl ToStored<'_, '_> {
    fn item<I: Into<ItemId> + TryFrom<ItemId> + Copy>(&mut self, id: I) -> I {
        match self.cache.store_id(id.into()) {
            Some(id) => id.try_into().ok().unwrap(),
            None => {
                self.ok = false;
                id
            }
        }
    }

    /// The files of the snapshot keep their ids. The prefix's only file is the local crate root,
    /// the file of the placeholder spans (`Span::dummy()` and `rustc_span::DUMMY_SP`) that e.g.
    /// builtin types and anonymous allocations get: we store these spans as they are.
    fn check_span_data(&mut self, data: &SpanData) {
        if data.file_id.index() < self.cache.header.prefix[5] as usize {
            let placeholder = matches!(
                (data.beg.line, data.beg.col, data.end.line, data.end.col),
                (0, 0, 0, 0) | (1, 0, 1, 0)
            );
            self.ok &= data.file_id == FileId::ZERO
                && placeholder
                && self.cache.local_files.contains(&FileId::ZERO);
        } else {
            self.ok &= self.cache.store_file(data.file_id).is_some();
        }
    }
}

impl VisitAstMut for ToStored<'_, '_> {
    fn enter_type_decl_id(&mut self, id: &mut TypeDeclId) {
        *id = self.item(*id);
    }
    fn enter_fun_decl_id(&mut self, id: &mut FunDeclId) {
        *id = self.item(*id);
    }
    fn enter_global_decl_id(&mut self, id: &mut GlobalDeclId) {
        *id = self.item(*id);
    }
    fn enter_trait_decl_id(&mut self, id: &mut TraitDeclId) {
        *id = self.item(*id);
    }
    fn enter_trait_impl_id(&mut self, id: &mut TraitImplId) {
        *id = self.item(*id);
    }
    // Visitors don't explore spans.
    fn enter_span(&mut self, span: &mut charon_lib::ast::Span) {
        let unpacked = span.unpack();
        self.check_span_data(&unpacked.data);
        if let Some(data) = &unpacked.generated_from_span {
            self.check_span_data(data);
        }
        let cache = self.cache;
        span.map_file_ids(|id| cache.store_file(id).unwrap_or(id));
    }
}

#[derive(derive_generic_visitor::Visitor)]
struct CollectIds {
    items: HashSet<ItemId>,
}

impl VisitAst for CollectIds {
    fn enter_type_decl_id(&mut self, id: &TypeDeclId) {
        self.items.insert((*id).into());
    }
    fn enter_fun_decl_id(&mut self, id: &FunDeclId) {
        self.items.insert((*id).into());
    }
    fn enter_global_decl_id(&mut self, id: &GlobalDeclId) {
        self.items.insert((*id).into());
    }
    fn enter_trait_decl_id(&mut self, id: &TraitDeclId) {
        self.items.insert((*id).into());
    }
    fn enter_trait_impl_id(&mut self, id: &TraitImplId) {
        self.items.insert((*id).into());
    }
}

impl<'tcx> TranslateCtx<'tcx> {
    /// Load the snapshot of the cache. Called once the items every session registers first are
    /// registered.
    pub(crate) fn cache_load_snapshot(&mut self) {
        // Matching an impl pattern needs the impl, so whether an item matches depends on the order
        // we translate items in (except for those of `hide_traits`, see `opacity_for_name`).
        if self.options.item_opacities.iter().any(|(pat, _)| {
            !self.options.hides_trait_impls(pat)
                && pat
                    .elems
                    .iter()
                    .any(|elem| matches!(elem, charon_lib::name_matcher::PatElem::Impl(_)))
        }) {
            self.cache = None;
        }
        let Some(cache) = &mut self.cache else {
            return;
        };
        let _guard = charon_lib::timing::scope("cache-open");
        let prefix = counts_of(&self.translated);
        cache.loaded = true;
        cache.header.prefix = prefix;
        cache.header.counts = prefix;
        cache.next = prefix;
        let loaded = (|| {
            let file = std::fs::File::open(cache.snapshot_path()).ok()?;
            let meta = file.metadata().ok()?;
            // SAFETY: snapshots are never modified once written (we write then rename).
            let snapshot = unsafe { Mmap::map(file) }.ok()?;
            let (header, values_end) = read_header(&snapshot)?;
            (header.prefix == prefix).then_some(())?;
            Some((snapshot, header, values_end, (meta.len(), meta.modified().ok()?)))
        })();
        let Some((snapshot, header, values_end, stamp)) = loaded else {
            return;
        };
        let krate = &mut self.translated;
        let reserve = |kind: usize| (header.counts[kind] - prefix[kind]) as usize;
        krate.type_decls.reserve_slots(reserve(0));
        krate.fun_decls.reserve_slots(reserve(1));
        krate.global_decls.reserve_slots(reserve(2));
        krate.trait_decls.reserve_slots(reserve(3));
        krate.trait_impls.reserve_slots(reserve(4));
        for file in &header.files {
            let id = krate.files.push_with(|id| File { id, ..file.clone() });
            self.file_to_id.insert(file.name.clone(), id);
        }
        cache.entries.reserve(header.index.len());
        cache.by_hash.reserve(header.index.len());
        for (i, entry) in header.index.iter().enumerate() {
            cache.by_hash.insert(u128::from_le_bytes(entry.hash), entry.id);
            cache.entries.insert(entry.id, i);
        }
        cache.next = header.counts;
        cache.header = header;
        cache.values_end = values_end;
        cache.snapshot = Some(snapshot);
        cache.stamp = Some(stamp);
    }

    /// If this source is the source of an item of the snapshot, bind it to that item.
    pub(crate) fn cache_find_unbound(&mut self, src: &TransItemSource<'tcx>) -> Option<ItemId> {
        let cache = self.cache.as_mut()?;
        let key = match cache.known_key.take_if(|(known, _)| known == src) {
            Some((_, key)) => key,
            None => {
                let _guard = charon_lib::timing::scope("cache-key");
                Rc::new(compute_key(self.tcx, &self.hax_state, src)?)
            }
        };
        let hash = key.hash;
        cache.known_key = Some((src.clone(), key));
        let id = *cache.by_hash.get(&hash)?;
        if self.reverse_id_map.contains_key(&id) {
            return None;
        }
        let registered = cache.unbound.remove(&id);
        self.bind_source(id, src.clone());
        if !registered {
            self.cache_register_name(id);
        }
        Some(id)
    }

    fn bind_source(&mut self, id: ItemId, src: TransItemSource<'tcx>) {
        if self.cache.as_ref().unwrap().processed_unbound.contains(&id) {
            self.processed.insert(src.clone());
        }
        self.id_map.insert(src.clone(), id);
        self.reverse_id_map.insert(id, src);
    }

    /// The source of this item, decoding it if it was registered from the cache without it.
    pub(crate) fn source_of(&mut self, id: ItemId) -> TransItemSource<'tcx> {
        if let Some(par) = &self.par {
            return par.reverse_ids.get(&id).unwrap();
        }
        if let Some(src) = self.reverse_id_map.get(&id) {
            return src.clone();
        }
        let cache = self.cache.as_ref().unwrap();
        let key = cache.entry(id).unwrap().key;
        let src = decode_src(self.tcx, &self.hax_state, cache.bytes(key), true);
        self.bind_source(id, src.clone());
        src
    }

    /// Enqueue an item registered without its source.
    pub(crate) fn cache_enqueue_unbound(&mut self, id: ItemId) {
        self.cache.as_mut().unwrap().unbound_queue.push_back(id);
    }

    /// Translate an item that was registered without its source.
    pub(crate) fn cache_translate_unbound(&mut self, id: ItemId) {
        if let Some(src) = self.reverse_id_map.get(&id) {
            let src = src.clone();
            if self.processed.insert(src.clone()) {
                self.translate_item(&src);
            }
            return;
        }
        if !self.cache.as_mut().unwrap().processed_unbound.insert(id) {
            return;
        }
        self.translate_stack.push(ItemOrModuleId::Item(id));
        let loaded = self.cache_load(id);
        self.translate_stack.pop();
        if !loaded {
            let src = self.source_of(id);
            self.translate_item(&src);
        }
    }

    /// Record a registration of `id`, computing its key if it is new.
    pub(crate) fn cache_record_registration(
        &mut self,
        id: ItemId,
        src: &TransItemSource<'tcx>,
        is_new: bool,
        enqueue: bool,
    ) {
        let Some(cache) = &mut self.cache else {
            return;
        };
        if is_new {
            let key = match cache.known_key.take_if(|(known, _)| known == src) {
                Some((_, key)) => Some(key),
                None => {
                    let _guard = charon_lib::timing::scope("cache-key");
                    compute_key(self.tcx, &self.hax_state, src).map(Rc::new)
                }
            };
            if let Some(key) = key {
                cache.add_key(id, key);
            }
        }
        if let Some(recorder) = cache.recorders.last_mut() {
            *recorder.refs.entry(id).or_default() |= enqueue;
        }
    }

    /// Record that the translation in progress needs `id` to be translated.
    pub(crate) fn cache_record_use(&mut self, id: ItemId) {
        if let Some(cache) = &mut self.cache
            && let Some(recorder) = cache.recorders.last_mut()
        {
            *recorder.refs.entry(id).or_default() = true;
        }
    }

    /// Record an effect of the translation in progress.
    pub(crate) fn cache_record_effect(&mut self, effect: impl FnOnce() -> Effect) {
        if let Some(cache) = &mut self.cache
            && let Some(recorder) = cache.recorders.last_mut()
        {
            let effect = effect();
            if !recorder.effects.contains(&effect) {
                recorder.effects.push(effect);
            }
        }
    }

    /// Record that the translation in progress did something we can't replay.
    pub(crate) fn cache_taint(&mut self, why: &'static str) {
        if let Some(cache) = &mut self.cache
            && let Some(recorder) = cache.recorders.last_mut()
        {
            recorder.tainted.get_or_insert(why);
        }
    }

    /// Replay a registration of a stored computation. Returns `false` if the item is unknown.
    fn cache_register_ref(&mut self, dep_src: &Option<DepSource>, (id, enqueue): StoredRef) -> bool {
        let cache = self.cache.as_mut().unwrap();
        if !self.reverse_id_map.contains_key(&id) && !cache.unbound.contains(&id) {
            if !cache.entries.contains_key(&id) {
                return false;
            }
            // Register the item without decoding its source.
            cache.unbound.insert(id);
            cache.stats.unbound += 1;
            self.cache_register_name(id);
        }
        if enqueue {
            match self.reverse_id_map.get(&id) {
                Some(src) => self.items_to_translate.push_back(src.clone()),
                None => self.cache_enqueue_unbound(id),
            }
        }
        self.errors
            .borrow_mut()
            .register_dep_source(dep_src, id, false);
        true
    }

    /// Give its name to an item of the snapshot we're registering.
    fn cache_register_name(&mut self, id: ItemId) {
        let cache = self.cache.as_ref().unwrap();
        if let Some((refs, name)) = cache.stored_name(id)
            && refs.into_iter().all(|r| self.cache_register_ref(&None, r))
            && let Some(name) = decode_value::<Name>(self.cache.as_ref().unwrap().slice(name))
        {
            self.translated.item_names.insert(id, name);
            return;
        }
        // Compute the name normally.
        let src = self.source_of(id);
        self.cache_start_recording();
        if let Ok(name) = self.translate_name(&src) {
            self.translated.item_names.insert(id, name);
        }
        self.cache_finish_naming(id);
    }

    /// Whether this item is translated, or loaded from the cache and waiting to be decoded.
    pub(crate) fn is_translated(&self, id: ItemId) -> bool {
        self.translated.get_item(id).is_some()
            || self
                .cache
                .as_ref()
                .is_some_and(|cache| cache.pending.contains_key(&id))
    }

    /// Try to get the translation of this item from the cache. Returns whether it succeeded. The
    /// item itself is decoded later.
    pub(crate) fn cache_load(&mut self, id: ItemId) -> bool {
        let Some(cache) = &mut self.cache else {
            return false;
        };
        if cache.failed.contains(&id) || !cache.entries.contains_key(&id) {
            return false;
        }
        // The name was computed when we registered the item.
        let Some(name) = self.translated.item_names.get(&id).cloned() else {
            return false;
        };
        // Stored placeholder spans refer to the local crate root as `FileId::ZERO`.
        if !cache.local_files.contains(&FileId::ZERO) {
            return false;
        }
        let Some((refs, effects, item)) = cache.stored_body(id) else {
            cache.stats.misses += 1;
            return false;
        };
        let _guard = charon_lib::timing::scope("cache-load");
        // Replay the registrations. These are not part of the translation in progress, if any.
        self.cache_start_recording();
        let dep_src = Some(DepSource {
            src_id: id,
            span: None,
        });
        let effects = refs
            .into_iter()
            .all(|r| self.cache_register_ref(&dep_src, r))
            .then(|| decode_value::<Vec<Effect>>(self.cache.as_ref().unwrap().slice(effects)))
            .flatten();
        let decoded = match &effects {
            // Effects update trait impls and names mention them: we decode them now.
            Some(_) if id.is_trait_impl() => {
                let item = decode_value(self.cache.as_ref().unwrap().slice(item.clone()));
                let ok = item.is_some();
                self.cache_finish_pending(id, name, item);
                ok
            }
            Some(_) => {
                self.cache.as_mut().unwrap().pending.insert(id, (item, name));
                true
            }
            None => false,
        };
        if !decoded {
            self.cache.as_mut().unwrap().recorders.pop();
            self.cache.as_mut().unwrap().stats.misses += 1;
            return false;
        }
        for effect in effects.unwrap() {
            match effect {
                Effect::RegisterAssocItems(trait_id) | Effect::MarkMethodUsed(trait_id, _) => {
                    // The source of the trait is only needed if its items aren't registered yet.
                    if self.method_status.get(trait_id).is_none() {
                        let trait_def_id = self.source_of(trait_id.into()).def_id().clone();
                        let _ = self.register_assoc_items(&trait_def_id, trait_id);
                    }
                    if let Effect::MarkMethodUsed(_, method_id) = effect {
                        self.mark_method_as_used(trait_id, method_id);
                    }
                }
                Effect::TranslatedVTable(impl_id, vtable) => {
                    self.translated_vtables.push((impl_id, vtable));
                }
            }
        }
        self.cache.as_mut().unwrap().recorders.pop();
        self.cache.as_mut().unwrap().stats.hits += 1;
        true
    }

    /// Put a decoded item in the translated crate, or mark it as failed if it couldn't be decoded.
    fn cache_finish_pending(&mut self, id: ItemId, name: Name, item: Option<CachedItem>) {
        let Some(item) = item else {
            self.cache.as_mut().unwrap().failed.insert(id);
            return;
        };
        macro_rules! finish {
            ($decl:expr, $slots:ident) => {{
                let mut decl = $decl;
                decl.item_meta.name = name;
                self.translated
                    .$slots
                    .set_slot(id.try_into().ok().unwrap(), decl);
            }};
        }
        match item {
            CachedItem::Type(decl) => finish!(decl, type_decls),
            CachedItem::Fun(decl) => finish!(decl, fun_decls),
            CachedItem::Global(decl) => finish!(decl, global_decls),
            CachedItem::TraitDecl(decl) => finish!(decl, trait_decls),
            CachedItem::TraitImpl(decl) => finish!(decl, trait_impls),
        }
    }

    /// Decode this item now if it is pending. If that fails, the item is left untranslated.
    pub(crate) fn cache_decode_now(&mut self, id: ItemId) {
        if let Some(cache) = &mut self.cache
            && let Some((range, name)) = cache.pending.remove(&id)
        {
            let item = decode_value(cache.slice(range));
            self.cache_finish_pending(id, name, item);
        }
    }

    /// Decode all the pending items, in parallel. The items that fail to decode get translated.
    /// Returns whether there were pending items.
    pub(crate) fn cache_decode_pending(&mut self) -> bool {
        let Some(cache) = &mut self.cache else {
            return false;
        };
        if cache.pending.is_empty() {
            return false;
        }
        let _guard = charon_lib::timing::scope("cache-decode");
        let mut pending: Vec<_> = cache.pending.drain().collect();
        pending.sort_unstable_by_key(|(id, _)| *id);
        let snapshot: &[u8] = cache.snapshot.as_ref().unwrap();
        let items: Vec<Option<CachedItem>> = pending
            .par_iter()
            .map(|(_, (range, _))| decode_value(&snapshot[range.clone()]))
            .collect();
        let mut failed = vec![];
        for ((id, (_, name)), item) in pending.into_iter().zip(items) {
            if item.is_none() {
                failed.push(id);
            }
            self.cache_finish_pending(id, name, item);
        }
        for id in failed {
            self.cache.as_mut().unwrap().stats.misses += 1;
            let src = self.source_of(id);
            self.translate_item(&src);
        }
        true
    }

    /// Start recording the translation of an item, or the computation of a name.
    pub(crate) fn cache_start_recording(&mut self) {
        self.cache_push_recorder(false);
    }

    /// Start recording a computation memoized across items.
    pub(crate) fn cache_start_memo(&mut self) {
        self.cache_push_recorder(true);
    }

    fn cache_push_recorder(&mut self, memo: bool) {
        let errors_before = self.errors.borrow().error_count;
        if let Some(cache) = &mut self.cache {
            cache.recorders.push(Recorder {
                refs: Default::default(),
                effects: Default::default(),
                tainted: None,
                errors_before,
                memo,
            });
        }
    }

    /// Whether we're recording a computation memoized across items. Such a recording doesn't see
    /// what reusing a value from a cache of the current item skips, so it shouldn't reuse them.
    pub(crate) fn cache_recording_memo(&self) -> bool {
        self.cache
            .as_ref()
            .and_then(|cache| cache.recorders.last())
            .is_some_and(|recorder| recorder.memo)
    }

    /// Record that we reuse the translation of `hax_ty` from the cache of the current binder. The
    /// item recorded what the translation did, but a memoized computation in progress didn't.
    pub(crate) fn cache_reuse_binder_ty(&mut self, hax_ty: &hax::Ty<'tcx>) {
        if let Some(cache) = &mut self.cache
            && let Some(recorder) = cache.recorders.last_mut()
            && recorder.memo
        {
            match cache.memos.get(&MemoKey::Ty(hax_ty.clone())) {
                Some(memo) => recorder.merge(memo),
                None => {
                    recorder.tainted.get_or_insert("type reused in a memo");
                }
            }
        }
    }

    /// Finish recording a computation whose result is memoized for `item`: we record what it did
    /// again when we reuse its result.
    pub(crate) fn cache_finish_memo(&mut self, key: impl Fn() -> MemoKey<'tcx>) {
        self.cache_finish_memo_if(true, key)
    }

    /// Like `cache_finish_memo`, for a computation whose result is only memoized if `memoized`.
    pub(crate) fn cache_finish_memo_if(&mut self, memoized: bool, key: impl Fn() -> MemoKey<'tcx>) {
        if let Some(cache) = &mut self.cache {
            let recorder = cache.recorders.pop().unwrap();
            if let Some(parent) = cache.recorders.last_mut() {
                parent.merge(&recorder);
            }
            if memoized {
                cache.memos.insert(key(), recorder);
            }
        }
    }

    /// Record what the memoized computation for `key` did, as we reuse its result.
    pub(crate) fn cache_replay_memo(&mut self, key: impl Fn() -> MemoKey<'tcx>) {
        if let Some(cache) = &mut self.cache
            && let Some(memo) = cache.memos.get(&key())
            && let Some(recorder) = cache.recorders.last_mut()
        {
            recorder.merge(memo);
        }
    }

    /// Finish recording the computation of the name of `id`.
    pub(crate) fn cache_finish_naming(&mut self, id: ItemId) {
        let error_count = self.errors.borrow().error_count;
        if let Some(cache) = &mut self.cache {
            let recorder = cache.recorders.pop().unwrap();
            if recorder.tainted.is_none()
                && recorder.effects.is_empty()
                && recorder.errors_before == error_count
            {
                cache.name_records.insert(id, recorder);
            }
        }
    }

    /// The registrations of a recorded computation, with the ids of the next snapshot.
    fn cache_stored_refs(&mut self, recorder: &Recorder, except: ItemId) -> Option<Vec<StoredRef>> {
        let mut refs = Vec::with_capacity(recorder.refs.len());
        for (&id, &enqueue) in &recorder.refs {
            if id == except {
                continue;
            }
            let cache = self.cache.as_mut().unwrap();
            // The key of an allocation is only known once its view is decided.
            if cache.store_id(id).is_none()
                && !cache.keys.contains_key(&id)
                && let Some(key) = compute_key(self.tcx, &self.hax_state, &self.reverse_id_map[&id])
            {
                cache.add_key(id, Rc::new(key));
            }
            refs.push((cache.store_id(id)?, enqueue));
        }
        Some(refs)
    }

    /// Finish recording the translation of `id` and store it if possible.
    pub(crate) fn cache_finish_recording(&mut self, id: ItemOrModuleId) {
        let error_count = self.errors.borrow().error_count;
        let Some(cache) = &mut self.cache else {
            return;
        };
        let _guard = charon_lib::timing::scope("cache-store");
        let mut recorder = cache.recorders.pop().unwrap();
        let Some(id) = id.as_item() else {
            return;
        };
        if !cache.has_key(id) {
            return;
        }
        if error_count != recorder.errors_before {
            recorder.tainted.get_or_insert("errors");
        }
        if let Some(why) = recorder.tainted {
            *cache.stats.tainted.entry(why).or_default() += 1;
            return;
        }
        let stored = (|| {
            let refs = self.cache_stored_refs(&recorder, id).ok_or("ref without id")?;
            let cache = self.cache.as_ref().unwrap();
            let store_id = cache.store_id(id).ok_or("no id")?;
            let item = self.translated.get_item(id).ok_or("no item")?;
            // Check that we recorded all the items it mentions.
            // Check that we recorded all the items it mentions, except in its name, which we store
            // separately.
            let mut collect = CollectIds {
                items: Default::default(),
            };
            macro_rules! without_name {
                ($variant:ident, $d:expr) => {{
                    let mut d = $d.clone();
                    d.item_meta.name = Name::default();
                    let _ = d.drive(&mut collect);
                    CachedItem::$variant(d)
                }};
            }
            let mut item = match item {
                ItemRef::Type(d) => without_name!(Type, d),
                ItemRef::Fun(d) => without_name!(Fun, d),
                ItemRef::Global(d) => without_name!(Global, d),
                ItemRef::TraitDecl(d) => without_name!(TraitDecl, d),
                ItemRef::TraitImpl(d) => without_name!(TraitImpl, d),
            };
            for effect in &recorder.effects {
                match effect {
                    Effect::RegisterAssocItems(t) | Effect::MarkMethodUsed(t, _) => {
                        collect.items.insert((*t).into());
                    }
                    Effect::TranslatedVTable(i, vtable) => {
                        collect.items.insert((*i).into());
                        let _ = vtable.drive(&mut collect);
                    }
                }
            }
            // Every session registers the items of the prefix (e.g. `TypeDeclId::UNIT`, which items
            // mention without registering it).
            let is_known = |i: &ItemId| {
                let (kind, index) = kind_and_index(*i);
                *i == id || index < cache.header.prefix[kind] as usize || recorder.refs.contains_key(i)
            };
            if !collect.items.iter().all(is_known) {
                return Err("unrecorded id");
            }
            let mut to_stored = ToStored { cache, ok: true };
            let _ = match &mut item {
                CachedItem::Type(d) => d.drive_mut(&mut to_stored),
                CachedItem::Fun(d) => d.drive_mut(&mut to_stored),
                CachedItem::Global(d) => d.drive_mut(&mut to_stored),
                CachedItem::TraitDecl(d) => d.drive_mut(&mut to_stored),
                CachedItem::TraitImpl(d) => d.drive_mut(&mut to_stored),
            };
            let effects: Vec<Effect> = recorder
                .effects
                .iter()
                .map(|effect| match effect.clone() {
                    Effect::RegisterAssocItems(t) => Effect::RegisterAssocItems(to_stored.item(t)),
                    Effect::MarkMethodUsed(t, m) => Effect::MarkMethodUsed(to_stored.item(t), m),
                    Effect::TranslatedVTable(i, mut vtable) => {
                        let _ = vtable.drive_mut(&mut to_stored);
                        Effect::TranslatedVTable(to_stored.item(i), vtable)
                    }
                })
                .collect();
            if !to_stored.ok {
                return Err("unstorable id or file");
            }
            let (effects, item) = (encode_value(&effects).unwrap(), encode_value(&item).unwrap());
            let body = postcard::to_allocvec(&(refs, effects.as_slice(), item.as_slice())).unwrap();
            Ok((store_id, body))
        })();
        let cache = self.cache.as_mut().unwrap();
        match stored {
            Ok((store_id, body)) => {
                cache.stats.stored += 1;
                cache.bodies.insert(store_id, body);
            }
            Err(why) => *cache.stats.tainted.entry(why).or_default() += 1,
        }
    }

    /// The name of `id` and the registrations computing it did, with the ids of the next
    /// snapshot and serialized as `IndexEntry::name`, if we can store them.
    fn cache_stored_name(&mut self, id: ItemId) -> Option<Vec<u8>> {
        // The names of allocations depend on the order we encounter them in.
        if matches!(self.reverse_id_map.get(&id)?.def_id().base, DefIdBase::Alloc(_)) {
            return None;
        }
        let recorder = self.cache.as_mut().unwrap().name_records.remove(&id)?;
        let refs = self.cache_stored_refs(&recorder, id)?;
        let mut name = self.translated.item_names.get(&id)?.clone();
        let cache = self.cache.as_ref().unwrap();
        let mut collect = CollectIds {
            items: Default::default(),
        };
        let _ = name.drive(&mut collect);
        let is_known = |i: &ItemId| {
            let (kind, index) = kind_and_index(*i);
            *i == id || index < cache.header.prefix[kind] as usize || recorder.refs.contains_key(i)
        };
        collect.items.iter().all(is_known).then_some(())?;
        let mut to_stored = ToStored {
            cache: self.cache.as_ref().unwrap(),
            ok: true,
        };
        let _ = name.drive_mut(&mut to_stored);
        to_stored.ok.then_some(())?;
        postcard::to_allocvec(&(refs, encode_value(&name)?.as_slice())).ok()
    }

    /// Write the snapshot plus what this session stored, unless another session replaced the
    /// snapshot meanwhile.
    pub(crate) fn cache_finish(&mut self) {
        let Some(cache) = &mut self.cache else {
            return;
        };
        if std::env::var_os("CHARON_CACHE_STATS").is_some() {
            eprintln!("charon cache: {:?}", cache.stats);
        }
        let _guard = charon_lib::timing::scope("cache-write");
        let mut out = match &cache.snapshot {
            Some(snapshot) => snapshot[..cache.values_end].to_vec(),
            None => vec![],
        };
        let mut index = cache.header.index.clone();
        let mut push = |bytes: &[u8]| {
            let loc = (out.len() as u64, bytes.len() as u64);
            out.extend_from_slice(bytes);
            loc
        };
        // The items of this session with a key that the snapshot doesn't have, by id in the next
        // snapshot.
        let mut new: Vec<(ItemId, ItemId)> = cache
            .keys
            .keys()
            .filter_map(|&id| Some((cache.store_id(id)?, id)))
            .filter(|(store_id, _)| !cache.entries.contains_key(store_id))
            .collect();
        new.sort_unstable();
        new.dedup_by_key(|(store_id, _)| *store_id);
        let mut changed = !new.is_empty();
        for (store_id, id) in new {
            let cache = self.cache.as_ref().unwrap();
            let id = cache.from_store_ids.get(&store_id).copied().unwrap_or(id);
            let key = &cache.keys[&id];
            let hash = key.hash.to_le_bytes();
            let key = push(&key.encoded);
            let name = self.cache_stored_name(id).map(|name| push(&name));
            let body = self.cache.as_mut().unwrap().bodies.remove(&store_id);
            index.push(IndexEntry {
                hash,
                id: store_id,
                key,
                name,
                body: body.map(|body| push(&body)),
            });
        }
        // The items of the snapshot that this session translated for the first time.
        let cache = self.cache.as_ref().unwrap();
        for (&store_id, body) in &cache.bodies {
            if let Some(&i) = cache.entries.get(&store_id)
                && index[i].body.is_none()
            {
                index[i].body = Some(push(body));
                changed = true;
            }
        }
        if !changed {
            return;
        }
        let mut files = cache.header.files.clone();
        for &id in &cache.new_files {
            let file = &self.translated.files[id];
            files.push(File {
                id: cache.store_files[&id],
                ..file.clone()
            });
        }
        let header = Header {
            prefix: cache.header.prefix,
            counts: cache.next,
            files,
            index,
        };
        let Ok(header) = postcard::to_allocvec(&header) else {
            return;
        };
        out.extend_from_slice(&header);
        out.extend_from_slice(&(header.len() as u64).to_le_bytes());
        out.extend_from_slice(SNAPSHOT_MAGIC);
        // Another session may have replaced the snapshot since we loaded it: keep theirs.
        let path = cache.snapshot_path();
        let current = std::fs::metadata(&path)
            .ok()
            .and_then(|meta| Some((meta.len(), meta.modified().ok()?)));
        if current != cache.stamp {
            return;
        }
        // Write atomically, as other charon processes may be reading the cache.
        let tmp = cache.dir.join(format!("snapshot.{}.tmp", std::process::id()));
        if std::fs::write(&tmp, out).is_ok() {
            let _ = std::fs::rename(&tmp, &path);
        }
    }
}
