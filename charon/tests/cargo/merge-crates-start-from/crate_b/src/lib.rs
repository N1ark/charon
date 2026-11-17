pub fn entry(p: crate_a::Pair) -> u32 {
    crate_a::swap(&p).0
}

/// Not reachable from `crate_b::entry`.
pub fn not_started_from() -> u32 {
    crate_a::unused()
}
