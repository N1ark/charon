pub fn use_a(b: bool) -> u32 {
    let w = crate_a::unbox(Box::new(crate_a::make()));
    crate_a::maybe_consume(w, b);
    crate_a::check(crate_a::classify(Some(1)))
}
