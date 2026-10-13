//@ revisions=values,bytes
//@[values] charon-args=--consts=values
//@[bytes] charon-args=--consts=bytes
//@ ignore-warnings
// Constant pointers that are hard to express.
#![allow(unused)]
use std::any::TypeId;
use std::fmt::Debug;
use std::mem::transmute;

struct Sync<T>(T);
unsafe impl<T> core::marker::Sync for Sync<T> {}

fn foo() {}
trait Tr {}
impl Tr for () {}
impl Tr for u8 {}
static X: u8 = 0;

// Pointers into a function.
static FN_PTR: Sync<*const ()> = Sync(foo as fn() as *const ());
static FN_OFFSET: Sync<*const u8> = Sync((foo as fn() as *const u8).wrapping_add(1));
static FN_SLICE: Sync<*const [u8]> =
    Sync(core::ptr::slice_from_raw_parts(foo as fn() as *const u8, 3));
static FN_DYN: Sync<*const dyn Tr> = Sync(foo as fn() as *const u8 as *const dyn Tr);
static FN_REF: &() = unsafe { transmute::<fn(), &()>(foo) };

// Pointers into vtables and `TypeId`s.
const DYN: &dyn Debug = &0u8;
static VTABLE: Sync<*const u8> = Sync(unsafe { transmute::<&dyn Debug, [*const u8; 2]>(DYN)[1] });
static VTABLE_OFFSET: Sync<*const u8> =
    Sync(unsafe { transmute::<&dyn Debug, [*const u8; 2]>(DYN)[1].wrapping_add(1000) });
static TYPE_ID_PTR: Sync<*const u8> =
    Sync(unsafe { transmute::<TypeId, [*const u8; 2]>(TypeId::of::<u8>())[0] });

// `TypeId`s that weren't made by `TypeId::of`.
const fn type_id_ptrs(id: TypeId) -> [*const u8; 2] {
    unsafe { transmute(id) }
}
const fn mk_type_id(ptrs: [*const u8; 2]) -> TypeId {
    unsafe { transmute(ptrs) }
}
static TYPE_ID_DATA: TypeId = mk_type_id([&X as *const u8; 2]);
static TYPE_ID_MIXED: TypeId = {
    let (a, b) = (type_id_ptrs(TypeId::of::<u8>()), type_id_ptrs(TypeId::of::<u16>()));
    mk_type_id([a[0], b[1]])
};
// In bytes mode, we can't tell which pointer of a `TypeId` a pointer is, so this one looks like the
// `TypeId` of `u8`.
static TYPE_ID_SWAPPED: TypeId = {
    let a = type_id_ptrs(TypeId::of::<u8>());
    mk_type_id([a[1], a[0]])
};
static TYPE_ID_OFFSET: TypeId = {
    let a = type_id_ptrs(TypeId::of::<u8>());
    mk_type_id([a[0].wrapping_add(1), a[1]])
};

// A marker-only vtable in raw memory.
union U {
    p: *const (dyn Send + core::marker::Sync),
    r: *const u8,
}
static MARKER_VTABLE: Sync<U> = Sync(U { p: &1u8 as *const u8 as *const (dyn Send + core::marker::Sync) });

// A raw pointer to a stateless closure.
static CLOSURE_RAW: Sync<*const ()> = Sync((|| 1u8) as fn() -> u8 as *const ());

// A pointer into an array of ZSTs, and to a field after ZSTs.
static ZARR: ((), [(); 4], u8) = ((), [(); 4], 1);
static ZPTR: &() = &ZARR.1[2];
static ZFIELD: &u8 = &ZARR.2;

// A pointer into a union field that isn't at offset 0.
union Bytes {
    a: (u8, u8, u8, u8),
    b: u32,
}
static UNION: Bytes = Bytes { b: 0 };
static UNION_A1: &u8 = unsafe { &UNION.a.1 };

// A pointer split across two union fields.
#[derive(Clone, Copy)]
union Half {
    a: u32,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct Two(Half, Half);
static SPLIT: Sync<Two> = Sync(unsafe { transmute::<*const u8, Two>(&X) });

// Pointers into extern statics.
enum E {
    A(u8),
    B(u32),
}
unsafe extern "C" {
    static EXT: [u32; 4];
    static EXT_E: E;
}
static EXT_PTR: &u32 = unsafe { &EXT[1] };
static EXT_E_PTR: Sync<*const u32> = Sync(unsafe { (&raw const EXT_E).cast::<u32>().add(1) });

fn main() {}
