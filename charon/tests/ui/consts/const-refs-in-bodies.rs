//@ revisions=default,mono
//@[mono] charon-args=--monomorphize
// References in constants used in bodies must stay valid after the function returns.
#![feature(adt_const_params, unsized_const_params)]
#![allow(incomplete_features)]
static ARR: [u32; 3] = [10, 20, 30];

// Points to the static.
fn get() -> &'static [u32; 3] {
    const { &ARR }
}

// An anonymous allocation.
fn anon() -> &'static [u32; 2] {
    const { &[1, 2] }
}

// A const generic reference, which has no allocation.
fn by_generic<const X: &'static &'static u8>() -> &'static &'static u8 {
    X
}

fn main() {
    let _ = get();
    let _ = anon();
    let _ = by_generic::<{ &&4 }>();
}
