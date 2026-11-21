//! In `if a || b { x? }`, the branches of the switch on `a` don't merge at `x`, which the false
//! branch of `b` bypasses, but after it. Picking `x` as the exit of that switch would translate the
//! rest of the function in both of its branches, exponentially so in a sequence of such `if`s.
pub fn sequence(
    first: bool,
    state: &mut [Option<u32>; 3],
    parse: fn(usize) -> Result<u32, ()>,
) -> Result<u32, ()> {
    if first || state[0].is_none() {
        state[0] = Some(parse(0)?);
    }
    if first || state[1].is_none() {
        state[1] = Some(parse(1)?);
    }
    if first || state[2].is_none() {
        state[2] = Some(parse(2)?);
    }
    Ok(0)
}
