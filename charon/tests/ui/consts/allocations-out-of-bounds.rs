//@ revisions=values,bytes
//@[values] charon-args=--consts=values
//@[bytes] charon-args=--consts=bytes
// Pointers outside of their allocation.
#![allow(unused)]
struct Sync<T>(T);
unsafe impl<T> core::marker::Sync for Sync<T> {}

static ARR: [u8; 4] = [1, 2, 3, 4];
static BEFORE: Sync<*const u8> = Sync(ARR.as_ptr().wrapping_sub(1));
static AFTER: Sync<*const u8> = Sync(ARR.as_ptr().wrapping_add(8));
static END: Sync<*const u8> = Sync(ARR.as_ptr().wrapping_add(4));

fn main() {}
