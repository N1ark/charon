//@ charon-args=--consts=values --monomorphize
// A constant used by several items with different environments.
trait HasLen {
    const LEN: usize;
}
impl<T, const N: usize> HasLen for [T; N] {
    const LEN: usize = N;
}

fn generic<T>(_x: T) -> usize {
    <[u8; 4] as HasLen>::LEN
}

pub fn use_generic() -> usize {
    generic(0u8) + generic(0u32) + <[u8; 4] as HasLen>::LEN
}
