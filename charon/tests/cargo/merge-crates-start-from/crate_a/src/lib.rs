#[derive(Clone, PartialEq)]
pub struct Pair(pub u32, pub u32);

/// Only `crate_b` uses it: it is reached from `crate_b::entry` only.
pub fn swap(p: &Pair) -> Pair {
    let Pair(a, b) = p.clone();
    Pair(b, a)
}

/// Not reachable from `crate_b::entry`.
pub fn unused() -> u32 {
    0
}

pub trait Describe {
    fn describe(&self) -> u32;
}
