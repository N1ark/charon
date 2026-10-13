//@ output=run-with-minirust
//@ known-failure
// MiniRust globals can't contain pointers to vtables.
unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
}
trait Tr: Sync {
    fn m(&self) -> u32;
}
impl Tr for u8 {
    fn m(&self) -> u32 {
        *self as u32 + 100
    }
}
static DYN: &dyn Tr = &5u8;

fn main() {
    minirust_print(DYN.m());
}
