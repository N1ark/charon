//@ output=run-with-minirust
//@ known-failure
// MiniRust relocations can't point before the start of their target.
unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
}
struct Sync<T>(T);
unsafe impl<T> core::marker::Sync for Sync<T> {}

static ARR: [u32; 3] = [10, 20, 30];
static BEFORE: Sync<*const u32> = Sync((&raw const ARR).cast::<u32>().wrapping_sub(1));

fn main() {
    minirust_print(unsafe { *BEFORE.0.wrapping_add(1) });
}
