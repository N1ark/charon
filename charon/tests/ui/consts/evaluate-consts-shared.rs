//@ charon-args=--consts=values --monomorphize
// A constant pointing to an allocation, evaluated in items with different typing environments.
const TABLE: &[u8; 3] = &[1, 2, 3];

fn generic<T>(_x: T) -> &'static [u8; 3] {
    const { TABLE }
}

pub fn use_generic() -> (&'static [u8; 3], &'static [u8; 3], &'static [u8; 3]) {
    (generic(0u8), generic(0u32), TABLE)
}
