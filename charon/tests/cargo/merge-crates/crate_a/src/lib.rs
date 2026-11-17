pub struct Wrapper {
    pub v: Vec<u32>,
}

pub fn make() -> Wrapper {
    Wrapper { v: vec![1, 2, 3] }
}

/// `w` is only moved out on one branch, so drop elaboration introduces a drop flag.
pub fn maybe_consume(w: Wrapper, b: bool) {
    if b {
        let _w = w;
    }
}

/// Moving out of a box is lowered to raw pointer operations.
pub fn unbox(b: Box<Wrapper>) -> Wrapper {
    *b
}

/// Match guards introduce fake borrows and reads, which are removed in runtime MIR.
pub fn classify(o: Option<u32>) -> u32 {
    match o {
        Some(x) if x > 10 => x,
        Some(_) => 1,
        None => 0,
    }
}

/// The message of the assertion is an allocation, local to every crate that translates the body.
pub fn check(n: u32) -> u32 {
    assert!(n > 0, "n is zero");
    n
}
