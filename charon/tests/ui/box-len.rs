//@ charon-args=--extract-opaque-bodies

// Use .len() explicitly
fn explicit() {
    let mut vec: Vec<u8> = Vec::new();
    let x: Box<[u8]> = vec.into_boxed_slice();
    let l = x.len();
}

// The vec! macro also uses it
fn implicit() {
    let mut vec = vec![1, 2];
}
