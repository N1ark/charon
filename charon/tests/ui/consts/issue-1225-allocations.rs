//@ revisions=values,unsized_strings
//@[values] charon-args=--consts=values
//@[unsized_strings] charon-args=--consts=values --unsized-strings
// With `--consts=values`, every allocation reachable from a constant gets its own global.
const C: &&u32 = &&1;
const STR: &str = "hello";
const STRS: &[&str] = &["a", "bc"];
const STR_SUFFIX: &str = STR.split_at(1).1;

static BOTH: (&u32, &u32) = (*C, *C);

fn promoted() -> &'static &'static u32 {
    &&2
}

fn use_consts() {
    let _ = C;
    let _ = STR;
    let _ = STRS;
    let _ = STR_SUFFIX;
    let _ = "world";
}

fn main() {}
