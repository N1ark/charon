//@ revisions=values,bytes,initializers
//@[values] charon-args=--consts=values
//@[bytes] charon-args=--consts=bytes
// Allocations reachable from constants and statics.
#![allow(unused)]
struct Sync<T>(T);
unsafe impl<T> core::marker::Sync for Sync<T> {}

// Pointers stored in raw memory keep their offset into their target.
static ARR: [u8; 4] = [1, 2, 3, 4];
const INTERIOR: &&u8 = &&ARR[2];

// Vtable pointers stored in raw memory.
trait Tr {
    fn m(&self) -> u8;
}
impl Tr for u8 {
    fn m(&self) -> u8 {
        *self
    }
}
const DYNS: &[&dyn Tr] = &[&1u8];

// `TypeId`s.
const TID: core::any::TypeId = core::any::TypeId::of::<u8>();

// A raw pointer to a function.
fn foo() {}
const FN_RAW: *const () = foo as *const ();

// A pointer to a union field.
union U {
    a: (u8, u8, u8, u8),
    b: u32,
}
static UNION: U = U { b: 0 };
static UNION_B: &u32 = unsafe { &UNION.b };

// A `*mut` pointer to an immutable static.
static MUT_PTR: Sync<*mut u8> = Sync(&ARR as *const [u8; 4] as *mut u8);

// A nested static.
static mut NESTED: &mut [u8] = &mut [1, 2];

// Unsized pointees that aren't slices.
struct W<T: ?Sized>(u8, T);
static WS: W<[u8; 2]> = W(0, [1, 2]);
const W_SLICE: &W<[u8]> = &WS;
const W_DYN: &W<dyn Tr> = &W(0, 1u8);
const CSTR: &core::ffi::CStr = c"hi";

// A `str` pointing into a static, or into part of a literal.
static BYTES: [u8; 3] = *b"abc";
const STR: &str = unsafe { core::str::from_utf8_unchecked(&BYTES) };
const STR_SUFFIX: &str = "abc".split_at(1).1;

// A promoted in a generic function.
fn generic<T>() -> &'static [u8] {
    &[1, 2, 3]
}

// A byte string in a function body.
fn byte_str() -> &'static [u8; 2] {
    b"ab"
}

fn main() {}
