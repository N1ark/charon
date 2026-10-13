//@ output=run-with-minirust
// MiniRust doesn't support subslice projections.
unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
}

static ARR: [u32; 3] = [10, 20, 30];

fn main() {
    let tail: &[u32] = const { ARR.split_at(1).1 };
    minirust_print(tail[0]);
}
