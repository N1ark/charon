//@ charon-args=--monomorphize
// Ensures monomorphization handles globals with generics

fn mul<const LEN: usize>(v: usize) -> usize {
    v * LEN
}

fn foo() {
    let _ = mul::<10>(5);
    let _ = mul::<5>(10);
}
