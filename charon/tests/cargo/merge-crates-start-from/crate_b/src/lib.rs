pub fn entry(p: crate_a::Pair) -> u32 {
    crate_a::swap(&p).0
}

/// Not reachable from `crate_b::entry`.
pub fn not_started_from() -> u32 {
    crate_a::unused()
}

pub struct Thing;

/// Started from by a pattern whose implemented type is in `crate_b`.
impl crate_a::Describe for Thing {
    fn describe(&self) -> u32 {
        1
    }
}
