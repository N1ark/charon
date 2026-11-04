//@ revisions=poly,mono
//@ charon-args=--print-layouts --hide-marker-traits
//@[poly] charon-args=--monomorphic-layouts
//@[poly] rustc-args=--cfg poly
//@[mono] charon-args=--monomorphize
//! `--monomorphic-layouts` gives each type declaration the layouts of its closed instances, which
//! are those that `--monomorphize` gives the monomorphized type declarations.
struct Tail<T: ?Sized> {
    a: u8,
    t: T,
}

enum Either<A, B> {
    Left(A),
    Right(B),
}

// The layout of `List<u8>` mentions `Option<Box<List<u8>>>`, whose layout mentions
// `Box<List<u8>>`.
struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

// Pointers aren't followed: we don't record `Grow<(u8, u8)>`. (Monomorphizing `Grow<u8>` doesn't
// terminate.)
#[cfg(poly)]
struct Grow<T>(T, Option<Box<Grow<(T, T)>>>);
#[cfg(poly)]
fn grow(_: &Grow<u8>) {}

fn instances(x: u32, list: List<u8>) -> Option<(u8, u32, u16)> {
    let _ = [1u8, 2];
    let _: Option<bool> = None;
    let _: Option<&u8> = None;
    let _: Either<u8, char> = Either::Left(0);
    let tail = Tail { a: 1u8, t: 7u32 };
    let _ = move || tail.t + x;
    let _ = (list, 0u8);
    None
}

// Not closed: no layout.
fn generic<T>(x: T) -> Option<T> {
    Some(x)
}
