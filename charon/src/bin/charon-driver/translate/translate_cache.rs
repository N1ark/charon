//! An opt-in persistent cache of translated items, shared across charon invocations. Set
//! `CHARON_TRANSLATION_CACHE` to enable it.
//!
//! The unit of caching is the translation of one item (`translate_item`). An item can be cached if
//! its `TransItemSource` mentions no item of the local crate and has a session-independent
//! encoding (`DefPathHash`es instead of `DefId`s, see [`KeyEncoder`]). The hash of that encoding
//! is the item's key.
//!
//! Besides producing the item, translating it registers (and maybe enqueues) the items it refers
//! to. We record these registrations and store them with the item, as encoded sources. Loading an
//! item replays them, which gives the ids that replace the ones stored in the item. We don't store
//! items whose translation has any other effect on the translation context (errors, method usage
//! tracking, ...).
//!
//! Registering an item computes its name, which we also store. This lets us register the items
//! that a cached item refers to without decoding their sources ("unbound" items): decoding is
//! costly, as it resolves trait references. We decode the source of an unbound item only when we
//! need it, e.g. to translate the item if its translation isn't cached.
//!
//! Translation rarely reads translated items, so loading an item only replays its registrations
//! and effects: we decode most items at the end of the translation, in parallel (see
//! [`PendingItem`]).
//!
//! Entries live in `$CHARON_TRANSLATION_CACHE/<env>/`, where `<env>` hashes everything else the
//! translation depends on: the charon binary, the options and the upstream crates.
use std::borrow::Cow;
use std::cell::Cell;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;

use rayon::prelude::*;
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::memmap::Mmap;
use rustc_data_structures::stable_hash::StableHasher;
use rustc_hash::FxHashMap as HashMap;
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

use super::translate_crate::{RustcItem, VirtualImplKind};
use super::translate_ctx::*;
use crate::hax;
use crate::hax::{AssocItemResolution, BaseState, DefIdBase, SInto, SyntheticItem};
use charon_lib::ast::id_remap::{IdRemap, with_id_remap};
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
    use TransItemSourceKind::*;
    fn virtual_kind(e: &mut KeyEncoder<'_>, kind: VirtualImplKind) {
        match kind {
            VirtualImplKind::Destruct => e.emit_u8(0),
            VirtualImplKind::Callable(k) => e.emit_u8(1 + k as u8),
        }
    }
    fn impl_kind(e: &mut KeyEncoder<'_>, kind: TransImplSource) {
        match kind {
            TransImplSource::Normal => e.emit_u8(0),
            TransImplSource::TraitAlias => e.emit_u8(1),
            TransImplSource::Marker => e.emit_u8(2),
            TransImplSource::Virtual(k) => {
                e.emit_u8(3);
                virtual_kind(e, k)
            }
        }
    }
    match kind {
        Global => e.emit_u8(0),
        TraitDecl => e.emit_u8(1),
        TraitImpl(k) => {
            e.emit_u8(2);
            impl_kind(e, k)
        }
        Fun => e.emit_u8(3),
        Type => e.emit_u8(4),
        InherentImpl => e.emit_u8(5),
        Module => e.emit_u8(6),
        ClosureAsFnCast => e.emit_u8(7),
        VirtualMethod(k) => {
            e.emit_u8(8);
            virtual_kind(e, k)
        }
        VTable => e.emit_u8(9),
        VTableInstance(k) => {
            e.emit_u8(10);
            impl_kind(e, k)
        }
        VTableMethod(k) => {
            e.emit_u8(11);
            impl_kind(e, k)
        }
        VTableDropShim(k) => {
            e.emit_u8(12);
            impl_kind(e, k)
        }
        IntrinsicFallback => e.emit_u8(13),
    }
}

fn decode_kind(d: &mut KeyDecoder<'_, '_>) -> TransItemSourceKind {
    use TransItemSourceKind::*;
    fn virtual_kind(d: &mut KeyDecoder<'_, '_>) -> VirtualImplKind {
        match d.read_u8() {
            0 => VirtualImplKind::Destruct,
            1 => VirtualImplKind::Callable(ClosureKind::Fn),
            2 => VirtualImplKind::Callable(ClosureKind::FnMut),
            3 => VirtualImplKind::Callable(ClosureKind::FnOnce),
            _ => unreachable!(),
        }
    }
    fn impl_kind(d: &mut KeyDecoder<'_, '_>) -> TransImplSource {
        match d.read_u8() {
            0 => TransImplSource::Normal,
            1 => TransImplSource::TraitAlias,
            2 => TransImplSource::Marker,
            3 => TransImplSource::Virtual(virtual_kind(d)),
            _ => unreachable!(),
        }
    }
    match d.read_u8() {
        0 => Global,
        1 => TraitDecl,
        2 => TraitImpl(impl_kind(d)),
        3 => Fun,
        4 => Type,
        5 => InherentImpl,
        6 => Module,
        7 => ClosureAsFnCast,
        8 => VirtualMethod(virtual_kind(d)),
        9 => VTable,
        10 => VTableInstance(impl_kind(d)),
        11 => VTableMethod(impl_kind(d)),
        12 => VTableDropShim(impl_kind(d)),
        13 => IntrinsicFallback,
        _ => unreachable!(),
    }
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
            match s.with_global_cache(|cache| cache.alloc_types.decided_view(alloc_id)) {
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
            s.with_global_cache(|cache| cache.alloc_types.decide_view(alloc_id, view));
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

/// Encode the source without the choice of resolution. Returns `None` if that's not possible.
fn encode_src<'tcx>(
    tcx: TyCtxt<'tcx>,
    s: &hax::StateWithBase<'tcx>,
    src: &TransItemSource<'tcx>,
) -> Option<KeyEncoder<'tcx>> {
    let mut e = KeyEncoder {
        tcx,
        buf: Vec::new(),
        unencodable: false,
        mentions_local: false,
        mentions_alloc: false,
        type_shorthands: Default::default(),
        predicate_shorthands: Default::default(),
    };
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
    /// This trait impl has this vtable, which may not be translated yet (the impl's `vtable`
    /// depends on that).
    ImplVTable(TraitImplId, GlobalDeclRef),
    /// This vtable was translated, which fills the `vtable` of its impl if it was lazy.
    FillLazyVTable(TraitImplId, GlobalDeclRef),
}

#[derive(Clone, Serialize, Deserialize)]
struct CachedRef<'a> {
    old_id: ItemId,
    enqueue: bool,
    hash: u128,
    #[serde(borrow)]
    encoded: Cow<'a, [u8]>,
}

/// An entry is: this head, the length of the serialized name and the name if `name_refs` is
/// `Some`, and if `has_body`, the references of the item (`Vec<CachedRef>`), the length of its
/// serialized effects (`Vec<Effect>`), its effects and the item (`CachedItem`).
#[derive(Serialize, Deserialize)]
struct EntryHead<'a> {
    /// The id of the item itself in the session that stored it.
    self_id: ItemId,
    has_body: bool,
    /// The files of the entry, as indices in the file table of its pack.
    files: Vec<u32>,
    /// The registrations made to compute the name of the item, if we stored its name.
    #[serde(borrow)]
    name_refs: Option<Vec<CachedRef<'a>>>,
}

#[derive(SerializeState, DeserializeState)]
enum CachedItem {
    Type(TypeDecl),
    Fun(FunDecl),
    Global(GlobalDecl),
    TraitDecl(TraitDecl),
    TraitImpl(TraitImpl),
}

#[derive(Default, Debug)]
pub(crate) struct CacheStats {
    unbound: usize,
    decoded: usize,
    hits: usize,
    misses: usize,
    stored: usize,
    tainted: HashMap<&'static str, usize>,
}

/// The bytes of an entry, in the pack that holds them.
struct EntryBytes {
    pack: Arc<Mmap>,
    pack_index: usize,
    range: std::ops::Range<usize>,
}

impl std::ops::Deref for EntryBytes {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.pack[self.range.clone()]
    }
}

/// Where an entry lives: pack index, offset and length.
type EntryLoc = (usize, usize, usize);

/// An entry in the index of a pack: hash, offset, length, whether the entry has a body.
type PackIndexEntry = (u128, u64, u64, bool);

/// A pack is its entries, its file table (`Vec<File>`), its index, the lengths of the file table
/// and the index as `u64`s, and this.
const PACK_MAGIC: &[u8; 8] = b"CHRNPAK2";

pub(crate) struct TranslationCache<'tcx> {
    dir: PathBuf,
    /// The pack files of the cache, and the entries they contain.
    packs: Vec<Arc<Mmap>>,
    /// The file table of each pack, and the ids of these files in this session, once registered.
    pack_files: Vec<Vec<File>>,
    pack_file_ids: Vec<Vec<Option<FileId>>>,
    index: HashMap<u128, EntryLoc>,
    /// The entries stored by this session, written to a new pack at the end, and the files they
    /// mention.
    new_pack: Vec<u8>,
    new_index: Vec<PackIndexEntry>,
    new_files: indexmap::IndexSet<FileId>,
    /// The keys of the registered items that have one, and the reverse map.
    keys: HashMap<ItemId, Rc<ItemKey>>,
    by_hash: HashMap<u128, ItemId>,
    /// The key of the item we are registering, if we already know it.
    known_key: Option<(TransItemSource<'tcx>, Rc<ItemKey>)>,
    /// One recorder per `translate_item` or name computation in progress.
    recorders: Vec<Recorder>,
    /// What computing the names of the items we registered did.
    name_records: HashMap<ItemId, Recorder>,
    /// What the computations memoized across items did.
    memos: HashMap<MemoKey<'tcx>, Recorder>,
    /// Items registered without their source (see `cache_register_unbound`) that we must translate,
    /// and those we tried to translate.
    unbound_queue: std::collections::VecDeque<ItemId>,
    processed_unbound: rustc_hash::FxHashSet<ItemId>,
    /// The entries we stored in this session.
    stored: rustc_hash::FxHashSet<u128>,
    /// The files of the local crate.
    pub(crate) local_files: rustc_hash::FxHashSet<FileId>,
    /// The loaded items we haven't decoded yet, and those whose decoding failed.
    pending: HashMap<ItemId, PendingItem>,
    failed: rustc_hash::FxHashSet<ItemId>,
    stats: CacheStats,
}

/// An item loaded from the cache whose registrations and effects we replayed, and that we decode
/// later. Trait impls are never pending: the effects of other items update them, and the names of
/// items mention them.
struct PendingItem {
    bytes: EntryBytes,
    /// Where the serialized `CachedItem` starts in `bytes`.
    item_start: usize,
    id_map: HashMap<ItemId, ItemId>,
    files: Vec<FileId>,
    name: Name,
}

impl PendingItem {
    fn decode(&self) -> Option<CachedItem> {
        decode_entry_value(&self.bytes[self.item_start..], &self.id_map, &self.files)
    }
}

/// Read the file table and the index of a pack.
fn read_pack_index(pack: &[u8]) -> Option<(Vec<File>, Vec<PackIndexEntry>)> {
    let footer_start = pack.len().checked_sub(24)?;
    let footer = &pack[footer_start..];
    if &footer[16..] != PACK_MAGIC {
        return None;
    }
    let files_len = u64::from_le_bytes(footer[..8].try_into().ok()?) as usize;
    let index_len = u64::from_le_bytes(footer[8..16].try_into().ok()?) as usize;
    let index_start = footer_start.checked_sub(index_len)?;
    let files_start = index_start.checked_sub(files_len)?;
    let files = postcard::from_bytes(&pack[files_start..index_start]).ok()?;
    let index = postcard::from_bytes(&pack[index_start..footer_start]).ok()?;
    Some((files, index))
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

        let mut packs = Vec::new();
        let mut pack_files = Vec::new();
        let mut index = HashMap::default();
        let mut with_body = rustc_hash::FxHashSet::default();
        for entry in std::fs::read_dir(&dir).ok()?.flatten() {
            if entry.path().extension().is_some_and(|ext| ext == "pack")
                && let Ok(file) = std::fs::File::open(entry.path())
                // SAFETY: packs are never modified once written (we write then rename).
                && let Ok(pack) = unsafe { Mmap::map(file) }
                && let Some((files, pack_index)) = read_pack_index(&pack)
            {
                for (hash, offset, len, has_body) in pack_index {
                    // Prefer entries with a body.
                    let loc = (packs.len(), offset as usize, len as usize);
                    if has_body {
                        with_body.insert(hash);
                        index.insert(hash, loc);
                    } else if !with_body.contains(&hash) {
                        index.insert(hash, loc);
                    }
                }
                packs.push(Arc::new(pack));
                pack_files.push(files);
            }
        }
        let pack_file_ids = pack_files
            .iter()
            .map(|files| vec![None; files.len()])
            .collect();
        Some(Self {
            dir,
            packs,
            pack_files,
            pack_file_ids,
            index,
            new_pack: Default::default(),
            new_index: Default::default(),
            new_files: Default::default(),
            keys: Default::default(),
            by_hash: Default::default(),
            known_key: None,
            recorders: Default::default(),
            name_records: Default::default(),
            memos: Default::default(),
            unbound_queue: Default::default(),
            processed_unbound: Default::default(),
            stored: Default::default(),
            local_files: Default::default(),
            pending: Default::default(),
            failed: Default::default(),
            stats: Default::default(),
        })
    }

    /// Whether this value, renumbered with `StoreFileIds`, only mentions files of its entry. The
    /// exception is `FileId::ZERO`: in every session that's the local crate root, the file of the
    /// placeholder spans (`Span::dummy()` and `rustc_span::DUMMY_SP`) that e.g. builtin types and
    /// anonymous allocations get. We store these spans as is. Hash-consing can also give us values
    /// of the session with other spans than the ones we renumbered.
    fn only_stored_files<T: AstVisitable>(&self, value: &T) -> bool {
        let mut check = CheckStoredFiles {
            zero_is_local: self.local_files.contains(&FileId::ZERO),
            ok: true,
        };
        let _ = value.drive(&mut check);
        check.ok
    }

    fn store(&mut self, hash: u128, bytes: &[u8], has_body: bool) {
        let start = self.new_pack.len() as u64;
        self.new_pack.extend_from_slice(bytes);
        self.new_index
            .push((hash, start, bytes.len() as u64, has_body));
        self.stored.insert(hash);
        self.stats.stored += 1;
    }

    fn entry(&self, hash: u128) -> Option<EntryBytes> {
        let &(pack, offset, len) = self.index.get(&hash)?;
        Some(EntryBytes {
            pack: self.packs[pack].clone(),
            pack_index: pack,
            range: offset..offset + len,
        })
    }

    pub(crate) fn pop_unbound(&mut self) -> Option<ItemId> {
        self.unbound_queue.pop_front()
    }

    /// The indices in the file table of the new pack of these files of the session.
    fn store_files(&mut self, files: &indexmap::IndexSet<FileId>) -> Vec<u32> {
        files
            .iter()
            .map(|fid| self.new_files.insert_full(*fid).0 as u32)
            .collect()
    }

    /// Write the entries stored during this session to a new pack.
    pub(crate) fn finish(&mut self, session_files: &IndexVec<FileId, File>) {
        if std::env::var_os("CHARON_CACHE_STATS").is_some() {
            eprintln!("charon cache: {:?}", self.stats);
        }
        if self.new_index.is_empty() {
            return;
        }
        let _guard = charon_lib::timing::scope("cache-write");
        let mut pack = std::mem::take(&mut self.new_pack);
        let files: Vec<&File> = self
            .new_files
            .iter()
            .map(|fid| &session_files[*fid])
            .collect();
        let files = postcard::to_allocvec(&files).unwrap();
        let index = postcard::to_allocvec(&self.new_index).unwrap();
        pack.extend_from_slice(&files);
        pack.extend_from_slice(&index);
        pack.extend_from_slice(&(files.len() as u64).to_le_bytes());
        pack.extend_from_slice(&(index.len() as u64).to_le_bytes());
        pack.extend_from_slice(PACK_MAGIC);
        // Write atomically, as other charon processes may be reading the cache.
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let name = format!("{}-{nanos}", std::process::id());
        let tmp = self.dir.join(format!("{name}.tmp"));
        if std::fs::write(&tmp, pack).is_ok() {
            let _ = std::fs::rename(&tmp, self.dir.join(format!("{name}.pack")));
        }
    }
}

impl<'tcx> TranslateCtx<'tcx> {
    /// If this source was registered from the cache without its source, bind it to that item.
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
        self.bind_source(id, src.clone());
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
        if let Some(src) = self.reverse_id_map.get(&id) {
            return src.clone();
        }
        let key = self.cache.as_ref().unwrap().keys[&id].clone();
        let src = decode_src(self.tcx, &self.hax_state, &key.encoded, true);
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
                cache.by_hash.entry(key.hash).or_insert(id);
                cache.keys.insert(id, key);
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

    /// Register a reference of a cached item. Returns `None` if that failed.
    fn cache_register_ref(
        &mut self,
        dep_src: &Option<DepSource>,
        r: &CachedRef<'_>,
    ) -> Option<ItemId> {
        let cache = self.cache.as_mut().unwrap();
        let id = match cache.by_hash.get(&r.hash) {
            Some(&id) => {
                if r.enqueue {
                    match self.reverse_id_map.get(&id) {
                        Some(src) => self.items_to_translate.push_back(src.clone()),
                        None => self.cache_enqueue_unbound(id),
                    }
                }
                id
            }
            None => match self.cache_register_unbound(r) {
                Some(id) => {
                    if r.enqueue {
                        self.cache_enqueue_unbound(id);
                    }
                    id
                }
                None => {
                    self.cache.as_mut().unwrap().stats.decoded += 1;
                    let src = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        decode_src(self.tcx, &self.hax_state, &r.encoded, true)
                    }))
                    .ok()?;
                    let key = Rc::new(ItemKey {
                        hash: r.hash,
                        encoded: r.encoded.to_vec(),
                    });
                    self.cache.as_mut().unwrap().known_key = Some((src.clone(), key));
                    let id = if r.enqueue {
                        self.register_and_enqueue(dep_src, src)
                    } else {
                        self.register_no_enqueue(dep_src, &src)
                    };
                    return id.as_item();
                }
            },
        };
        self.errors
            .borrow_mut()
            .register_dep_source(dep_src, id, false);
        Some(id)
    }

    /// Register an item without decoding its source, using the name stored in its entry.
    fn cache_register_unbound(&mut self, r: &CachedRef<'_>) -> Option<ItemId> {
        let cache = self.cache.as_ref().unwrap();
        // Stored placeholder spans refer to the local crate root as `FileId::ZERO`.
        if !cache.local_files.contains(&FileId::ZERO) {
            return None;
        }
        let bytes = cache.entry(r.hash)?;
        let (head, rest) = postcard::take_from_bytes::<EntryHead>(&bytes).ok()?;
        let name_refs = head.name_refs?;
        let name_len = u32::from_le_bytes(rest.get(..4)?.try_into().ok()?) as usize;
        let name_bytes = rest.get(4..4 + name_len)?;
        let kind = decode_kind(&mut KeyDecoder {
            tcx: self.tcx,
            opaque: MemDecoder::new(&r.encoded, 0).ok()?,
        });
        let id = self.reserve_item_id(kind)?;
        let cache = self.cache.as_mut().unwrap();
        cache.stats.unbound += 1;
        cache.by_hash.insert(r.hash, id);
        let key = Rc::new(ItemKey {
            hash: r.hash,
            encoded: r.encoded.to_vec(),
        });
        cache.keys.insert(id, key);

        let mut id_map: HashMap<ItemId, ItemId> =
            HashMap::with_capacity_and_hasher(name_refs.len() + 2, Default::default());
        id_map.insert(head.self_id, id);
        id_map.insert(TypeDeclId::UNIT.into(), TypeDeclId::UNIT.into());
        let name = 'name: {
            for name_ref in &name_refs {
                let Some(new_id) = self.cache_register_ref(&None, name_ref) else {
                    break 'name None;
                };
                id_map.insert(name_ref.old_id, new_id);
            }
            let Some(files) = self.cache_register_files(bytes.pack_index, &head.files) else {
                break 'name None;
            };
            decode_entry_value::<Name>(name_bytes, &id_map, &files)
        };
        let name = match name {
            Some(name) => name,
            // Compute the name normally.
            None => {
                let src = self.source_of(id);
                let Ok(name) = self.translate_name(&src) else {
                    return Some(id);
                };
                name
            }
        };
        self.translated.item_names.insert(id, name);
        Some(id)
    }

    /// Register the files of an entry of this pack. Returns `None` if the entry is invalid.
    fn cache_register_files(&mut self, pack: usize, files: &[u32]) -> Option<Vec<FileId>> {
        let mut ids = Vec::with_capacity(files.len());
        for &index in files {
            let index = index as usize;
            let cache = self.cache.as_mut().unwrap();
            let id = match *cache.pack_file_ids[pack].get(index)? {
                Some(id) => id,
                None => {
                    let file = &cache.pack_files[pack][index];
                    let id = match self.file_to_id.get(&file.name) {
                        Some(id) => *id,
                        None => {
                            let file = file.clone();
                            let name = file.name.clone();
                            let id = self.translated.files.push_with(|id| File { id, ..file });
                            self.file_to_id.insert(name, id);
                            id
                        }
                    };
                    self.cache.as_mut().unwrap().pack_file_ids[pack][index] = Some(id);
                    id
                }
            };
            ids.push(id);
        }
        Some(ids)
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
    /// item itself is decoded later, see [`PendingItem`].
    pub(crate) fn cache_load(&mut self, id: ItemId) -> bool {
        let Some(cache) = &mut self.cache else {
            return false;
        };
        let Some(key) = cache.keys.get(&id) else {
            return false;
        };
        if cache.failed.contains(&id) {
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
        let Some(bytes) = cache.entry(key.hash) else {
            cache.stats.misses += 1;
            return false;
        };
        let _guard = charon_lib::timing::scope("cache-load");
        let parsed = (|| {
            let (head, rest) = postcard::take_from_bytes::<EntryHead>(&bytes).ok()?;
            if !head.has_body {
                return None;
            }
            let name_len = u32::from_le_bytes(rest.get(..4)?.try_into().ok()?) as usize;
            let rest = rest.get(4 + name_len..)?;
            let (refs, rest) = postcard::take_from_bytes::<Vec<CachedRef>>(rest).ok()?;
            let effects_len = u32::from_le_bytes(rest.get(..4)?.try_into().ok()?) as usize;
            let effects = rest.get(4..4 + effects_len)?;
            let item_start = bytes.len() - (rest.len() - 4 - effects_len);
            Some((head, refs, effects, item_start))
        })();
        let Some((head, refs, effects, item_start)) = parsed else {
            cache.stats.misses += 1;
            return false;
        };

        // Replay the registrations. These are not part of the translation in progress, if any.
        self.cache_start_recording();
        let dep_src = Some(DepSource {
            src_id: id,
            span: None,
        });
        let mut id_map: HashMap<ItemId, ItemId> =
            HashMap::with_capacity_and_hasher(refs.len() + 2, Default::default());
        for r in &refs {
            let Some(new_id) = self.cache_register_ref(&dep_src, r) else {
                self.cache.as_mut().unwrap().recorders.pop();
                self.cache.as_mut().unwrap().stats.misses += 1;
                return false;
            };
            id_map.insert(r.old_id, new_id);
        }
        id_map.insert(head.self_id, id);
        id_map.insert(TypeDeclId::UNIT.into(), TypeDeclId::UNIT.into());
        let files = self.cache_register_files(bytes.pack_index, &head.files);
        let Some(files) = files else {
            self.cache.as_mut().unwrap().recorders.pop();
            self.cache.as_mut().unwrap().stats.misses += 1;
            return false;
        };
        let Some(effects) = decode_entry_value::<Vec<Effect>>(effects, &id_map, &files) else {
            self.cache.as_mut().unwrap().recorders.pop();
            self.cache.as_mut().unwrap().stats.misses += 1;
            return false;
        };
        let pending = PendingItem {
            item_start,
            bytes,
            id_map,
            files,
            name,
        };
        if id.is_trait_impl() {
            let item = pending.decode();
            if item.is_none() {
                self.cache.as_mut().unwrap().recorders.pop();
                self.cache.as_mut().unwrap().stats.misses += 1;
                return false;
            }
            self.cache_finish_pending(id, pending, item);
        } else {
            self.cache.as_mut().unwrap().pending.insert(id, pending);
        }

        for effect in effects {
            match effect {
                Effect::RegisterAssocItems(trait_id) => {
                    let trait_def_id = self.source_of(trait_id.into()).def_id().clone();
                    let _ = self.register_assoc_items(&trait_def_id, trait_id);
                }
                Effect::MarkMethodUsed(trait_id, method_id) => {
                    let trait_def_id = self.source_of(trait_id.into()).def_id().clone();
                    let _ = self.register_assoc_items(&trait_def_id, trait_id);
                    self.mark_method_as_used(trait_id, method_id);
                }
                Effect::ImplVTable(impl_id, vtable) => {
                    let translated = self.is_translated(vtable.id.into());
                    if let Some(timpl) = self.translated.trait_impls.get_mut(impl_id)
                        && matches!(timpl.vtable, VTableDecl::Lazy | VTableDecl::VTable(_))
                    {
                        timpl.vtable = if translated {
                            VTableDecl::VTable(vtable)
                        } else {
                            VTableDecl::Lazy
                        };
                    }
                }
                Effect::FillLazyVTable(impl_id, vtable) => {
                    if let Some(timpl) = self.translated.trait_impls.get_mut(impl_id)
                        && timpl.vtable.is_lazy()
                    {
                        timpl.vtable = VTableDecl::VTable(vtable);
                    }
                }
            }
        }
        self.cache.as_mut().unwrap().recorders.pop();
        self.cache.as_mut().unwrap().stats.hits += 1;
        true
    }

    /// Put a decoded pending item in the translated crate, or mark it as failed if it couldn't be
    /// decoded.
    fn cache_finish_pending(&mut self, id: ItemId, pending: PendingItem, item: Option<CachedItem>) {
        let cache = self.cache.as_mut().unwrap();
        let Some(item) = item else {
            cache.stats.hits -= 1;
            cache.stats.misses += 1;
            cache.failed.insert(id);
            return;
        };
        let name = pending.name;
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
        if let Some(pending) = self.cache.as_mut().and_then(|c| c.pending.remove(&id)) {
            let item = pending.decode();
            self.cache_finish_pending(id, pending, item);
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
        let items: Vec<_> = pending.par_iter().map(|(_, p)| p.decode()).collect();
        let mut failed = vec![];
        for ((id, pending), item) in pending.into_iter().zip(items) {
            if item.is_none() {
                failed.push(id);
            }
            self.cache_finish_pending(id, pending, item);
        }
        for id in failed {
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
    pub(crate) fn cache_finish_memo(&mut self, key: impl FnOnce() -> MemoKey<'tcx>) {
        self.cache_finish_memo_if(true, key)
    }

    /// Like `cache_finish_memo`, for a computation whose result is only memoized if `memoized`.
    pub(crate) fn cache_finish_memo_if(
        &mut self,
        memoized: bool,
        key: impl FnOnce() -> MemoKey<'tcx>,
    ) {
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
    pub(crate) fn cache_replay_memo(&mut self, key: impl FnOnce() -> MemoKey<'tcx>) {
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

    /// Serialize the name of `id` and the registrations needed to compute it, if possible.
    fn cache_name_section(
        &self,
        id: ItemId,
        files: &mut indexmap::IndexSet<FileId>,
    ) -> Option<(Vec<CachedRef<'static>>, Vec<u8>)> {
        let cache = self.cache.as_ref().unwrap();
        // The names of allocations depend on the order we encounter them in.
        if matches!(self.reverse_id_map[&id].def_id().base, DefIdBase::Alloc(_)) {
            return None;
        }
        let recorder = cache.name_records.get(&id)?;
        let mut refs = Vec::with_capacity(recorder.refs.len());
        for (&ref_id, &enqueue) in &recorder.refs {
            let ref_key = cache.keys.get(&ref_id)?;
            refs.push(CachedRef {
                old_id: ref_id,
                enqueue,
                hash: ref_key.hash,
                encoded: Cow::Owned(ref_key.encoded.clone()),
            });
        }
        let mut name = self.translated.item_names.get(&id)?.clone();
        let mut collect = CollectIds {
            items: Default::default(),
            files: std::mem::take(files),
        };
        let _ = name.drive(&mut collect);
        *files = collect.files;
        files.shift_remove(&FileId::ZERO);
        let is_known = |i: &ItemId| {
            *i == id || *i == ItemId::Type(TypeDeclId::UNIT) || recorder.refs.contains_key(i)
        };
        if !collect.items.iter().all(is_known) {
            return None;
        }
        let _ = name.drive_mut(&mut StoreFileIds { files });
        if !cache.only_stored_files(&name) {
            return None;
        }
        let state = DedupSerializer::default();
        let bytes = postcard::to_allocvec(&serde_state::WithState::new(&name, &state)).ok()?;
        Some((refs, bytes))
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
        let Some(key) = cache.keys.get(&id).cloned() else {
            return;
        };
        if error_count != recorder.errors_before {
            recorder.tainted.get_or_insert("errors");
        }
        if let Some(why) = recorder.tainted {
            *cache.stats.tainted.entry(why).or_default() += 1;
            return;
        }
        // The item refers to itself under its own id.
        recorder.refs.shift_remove(&id);
        let mut refs = Vec::with_capacity(recorder.refs.len());
        for (&ref_id, &enqueue) in &recorder.refs {
            // The key of an allocation is only known once its view is decided.
            if !cache.keys.contains_key(&ref_id)
                && let Some(key) =
                    compute_key(self.tcx, &self.hax_state, &self.reverse_id_map[&ref_id])
            {
                cache.by_hash.entry(key.hash).or_insert(ref_id);
                cache.keys.insert(ref_id, Rc::new(key));
            }
            let Some(ref_key) = cache.keys.get(&ref_id) else {
                *cache.stats.tainted.entry("ref without key").or_default() += 1;
                return;
            };
            refs.push(CachedRef {
                old_id: ref_id,
                enqueue,
                hash: ref_key.hash,
                encoded: Cow::Owned(ref_key.encoded.clone()),
            });
        }
        let Some(mut item) = self.translated.get_item_mut(id) else {
            // E.g. invisible items.
            return;
        };
        // Serialize without the name: it is recomputed when the item is registered.
        let name = std::mem::replace(&mut item.item_meta().name, Name::default());
        let item = self.translated.get_item(id).unwrap();
        // Check that we recorded all the ids the item mentions.
        let mut collect = CollectIds {
            items: Default::default(),
            files: Default::default(),
        };
        match item {
            ItemRef::Type(d) => d.drive(&mut collect),
            ItemRef::Fun(d) => d.drive(&mut collect),
            ItemRef::Global(d) => d.drive(&mut collect),
            ItemRef::TraitDecl(d) => d.drive(&mut collect),
            ItemRef::TraitImpl(d) => d.drive(&mut collect),
        };
        for effect in &recorder.effects {
            match effect {
                Effect::RegisterAssocItems(t) | Effect::MarkMethodUsed(t, _) => {
                    collect.items.insert((*t).into());
                }
                Effect::ImplVTable(i, vtable) | Effect::FillLazyVTable(i, vtable) => {
                    collect.items.insert((*i).into());
                    let _ = vtable.drive(&mut collect);
                }
            }
        }
        let is_known = |i: ItemId| {
            i == id || i == ItemId::Type(TypeDeclId::UNIT) || recorder.refs.contains_key(&i)
        };
        let all_recorded = collect.items.iter().all(|i| is_known(*i));
        let mut files = collect.files;
        files.shift_remove(&FileId::ZERO);
        let serialized = all_recorded
            .then(|| {
                let mut store_files = StoreFileIds { files: &files };
                macro_rules! renumber {
                    ($variant:ident, $d:expr) => {{
                        let mut d = $d.clone();
                        let _ = d.drive_mut(&mut store_files);
                        CachedItem::$variant(d)
                    }};
                }
                let item = match item {
                    ItemRef::Type(d) => renumber!(Type, d),
                    ItemRef::Fun(d) => renumber!(Fun, d),
                    ItemRef::Global(d) => renumber!(Global, d),
                    ItemRef::TraitDecl(d) => renumber!(TraitDecl, d),
                    ItemRef::TraitImpl(d) => renumber!(TraitImpl, d),
                };
                let only_stored_files = match &item {
                    CachedItem::Type(d) => cache.only_stored_files(d),
                    CachedItem::Fun(d) => cache.only_stored_files(d),
                    CachedItem::Global(d) => cache.only_stored_files(d),
                    CachedItem::TraitDecl(d) => cache.only_stored_files(d),
                    CachedItem::TraitImpl(d) => cache.only_stored_files(d),
                };
                // Effects only mention vtable refs, which have no spans.
                only_stored_files.then_some(item)
            })
            .flatten();
        self.translated.get_item_mut(id).unwrap().item_meta().name = name;
        let bytes = serialized.and_then(|item| {
            // The name section may add files.
            let name_section = self.cache_name_section(id, &mut files);
            let head = EntryHead {
                self_id: id,
                has_body: true,
                files: self.cache.as_mut().unwrap().store_files(&files),
                name_refs: name_section.as_ref().map(|(refs, _)| refs.clone()),
            };
            let mut bytes = postcard::to_allocvec(&head).ok()?;
            let name_bytes = name_section.map(|(_, bytes)| bytes).unwrap_or_default();
            bytes.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
            bytes.extend_from_slice(&name_bytes);
            bytes = postcard::to_extend(&refs, bytes).ok()?;
            let state = DedupSerializer::default();
            let effects =
                postcard::to_allocvec(&serde_state::WithState::new(&recorder.effects, &state))
                    .ok()?;
            bytes.extend_from_slice(&(effects.len() as u32).to_le_bytes());
            bytes.extend_from_slice(&effects);
            let state = DedupSerializer::default();
            postcard::to_extend(&serde_state::WithState::new(&item, &state), bytes).ok()
        });
        let cache = self.cache.as_mut().unwrap();
        match bytes {
            Some(bytes) => cache.store(key.hash, &bytes, true),
            None => {
                *cache
                    .stats
                    .tainted
                    .entry("unrecorded id or local file")
                    .or_default() += 1
            }
        }
    }

    /// Store the names of the items we registered but whose translation we didn't store, so that
    /// later sessions can register them without their source.
    pub(crate) fn cache_store_names(&mut self) {
        let Some(cache) = &self.cache else {
            return;
        };
        let mut ids: Vec<ItemId> = cache
            .name_records
            .keys()
            .copied()
            .filter(|id| {
                cache.keys.get(id).is_some_and(|key| {
                    !cache.stored.contains(&key.hash) && !cache.index.contains_key(&key.hash)
                })
            })
            .collect();
        ids.sort();
        for id in ids {
            let mut files = Default::default();
            let Some((name_refs, name_bytes)) = self.cache_name_section(id, &mut files) else {
                continue;
            };
            let head = EntryHead {
                self_id: id,
                has_body: false,
                files: self.cache.as_mut().unwrap().store_files(&files),
                name_refs: Some(name_refs),
            };
            let Ok(mut bytes) = postcard::to_allocvec(&head) else {
                continue;
            };
            bytes.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
            bytes.extend_from_slice(&name_bytes);
            let cache = self.cache.as_mut().unwrap();
            let hash = cache.keys[&id].hash;
            cache.store(hash, &bytes, false);
        }
    }
}

/// Decode a value of an entry, with the ids of this session: `items` maps the item ids of the entry
/// to ours, and its k-th file is `files[k]`.
fn decode_entry_value<T: for<'de> DeserializeState<'de, DedupSerializer>>(
    bytes: &[u8],
    items: &HashMap<ItemId, ItemId>,
    files: &[FileId],
) -> Option<T> {
    struct EntryIdRemap<'a> {
        items: &'a HashMap<ItemId, ItemId>,
        files: &'a [FileId],
        /// Whether we met an id that the entry doesn't know of.
        unknown: Cell<bool>,
    }
    impl IdRemap for EntryIdRemap<'_> {
        fn item_id(&self, id: ItemId) -> ItemId {
            let new = self.items.get(&id).copied();
            self.unknown.set(self.unknown.get() || new.is_none());
            new.unwrap_or(id)
        }
        fn file_id(&self, id: FileId) -> FileId {
            // Placeholder spans in the local crate root, see `CheckStoredFiles`.
            if id == FileId::ZERO {
                return id;
            }
            let new = (id.index().checked_sub(STORED_FILE_IDS_START))
                .and_then(|k| self.files.get(k).copied());
            self.unknown.set(self.unknown.get() || new.is_none());
            new.unwrap_or(id)
        }
    }
    let remap = EntryIdRemap {
        items,
        files,
        unknown: Cell::new(false),
    };
    let value = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        with_id_remap(&remap, || {
            let state = DedupSerializer::default();
            T::deserialize_state(&state, &mut postcard::Deserializer::from_bytes(bytes)).ok()
        })
    }));
    match value {
        Ok(Some(value)) if !remap.unknown.get() => Some(value),
        _ => None,
    }
}

/// In stored items, the k-th file of the entry is `FileId::from(STORED_FILE_IDS_START + k)`. This
/// distinguishes them from the ids of the session: hash-consing may give us values of the session
/// when we load ours, because the equality of `TraitParam`s ignores their spans.
const STORED_FILE_IDS_START: usize = 0xC000;

/// Renumber the files of an item to be stored.
#[derive(derive_generic_visitor::Visitor)]
struct StoreFileIds<'a> {
    files: &'a indexmap::IndexSet<FileId>,
}

impl StoreFileIds<'_> {
    fn store(&self, id: FileId) -> FileId {
        match self.files.get_index_of(&id) {
            Some(index) => FileId::from(STORED_FILE_IDS_START + index),
            None => id,
        }
    }
}

impl VisitAstMut for StoreFileIds<'_> {
    fn enter_file_id(&mut self, id: &mut FileId) {
        *id = self.store(*id);
    }
    // Visitors don't explore spans.
    fn enter_span(&mut self, span: &mut charon_lib::ast::Span) {
        span.map_file_ids(|id| self.store(id));
    }
}

/// See `TranslationCache::only_stored_files`.
#[derive(derive_generic_visitor::Visitor)]
struct CheckStoredFiles {
    zero_is_local: bool,
    ok: bool,
}

impl VisitAst for CheckStoredFiles {
    fn enter_span(&mut self, span: &charon_lib::ast::Span) {
        let span = span.unpack();
        for data in [Some(span.data), span.generated_from_span]
            .into_iter()
            .flatten()
        {
            if data.file_id.index() < STORED_FILE_IDS_START {
                let placeholder = matches!(
                    (data.beg.line, data.beg.col, data.end.line, data.end.col),
                    (0, 0, 0, 0) | (1, 0, 1, 0)
                );
                self.ok &= self.zero_is_local && data.file_id == FileId::ZERO && placeholder;
            }
        }
    }
}

#[derive(derive_generic_visitor::Visitor)]
struct CollectIds {
    items: rustc_hash::FxHashSet<ItemId>,
    files: indexmap::IndexSet<FileId>,
}

impl VisitAst for CollectIds {
    fn enter_file_id(&mut self, id: &FileId) {
        self.files.insert(*id);
    }
    // Visitors don't explore spans.
    fn enter_span(&mut self, span: &charon_lib::ast::Span) {
        self.files.extend(span.file_ids());
    }
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
