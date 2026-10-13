//@ charon-args=--consts=values
// Pointers to generic structs with an unsized tail and other unsized type parameters.
pub struct S<T: ?Sized + 'static, U: ?Sized> {
    pub p: &'static T,
    pub tail: U,
}
pub static S1: S<[u16], [u8; 2]> = S { p: &[1, 2, 3], tail: [4, 5] };
pub static R1: &S<[u16], [u8]> = &S1;
const C0: S<[u16], [u8; 2]> = S { p: &[1, 2, 3], tail: [4, 5] };
pub const C1: &S<[u16], [u8]> = &C0;
pub trait Tr: Sync {}
impl Tr for u8 {}
pub static S2: S<dyn Tr, [u8; 2]> = S { p: &1u8, tail: [4, 5] };
pub static R2: &S<dyn Tr, [u8]> = &S2;
pub static S3: S<[u8], u8> = S { p: &[1], tail: 7u8 };
pub static R3: &S<[u8], dyn Tr> = &S3;
const C2: S<dyn Tr, [u8; 2]> = S { p: &1u8, tail: [4, 5] };
pub fn body() -> (&'static S<[u16], [u8]>, &'static S<dyn Tr, [u8]>) {
    let a: &'static S<[u16], [u8]> = const { &C0 };
    let b: &'static S<dyn Tr, [u8]> = const { &C2 };
    (a, b)
}
