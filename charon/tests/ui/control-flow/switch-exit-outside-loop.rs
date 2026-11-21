//! The branches of the `p == 0` switch can both break out of the loop through the same block
//! (where the condition's temporary dies), after the loop. Taking that block as the exit of the
//! switch makes it an exit that every switch below can reach through its own `break`, so none of
//! them can use its own exit, and each duplicates the rest of the loop body in both of its
//! branches: the output is exponential in the number of such switches.
pub fn scan(mut p: u32, f: fn(u32) -> bool) -> u32 {
    let current_block: u32;
    loop {
        if f(0) {
            current_block = 1;
            break;
        } else if p == 0 {
            current_block = 1;
            break;
        } else {
            if f(1) {
                if f(11) {
                    current_block = 1;
                    break;
                }
                p += 1;
            } else {
                p += 2;
            }
            if f(2) {
                if f(12) {
                    current_block = 1;
                    break;
                }
                p += 1;
            } else {
                p += 2;
            }
            if f(3) {
                if f(13) {
                    current_block = 1;
                    break;
                }
                p += 1;
            } else {
                p += 2;
            }
            if f(4) {
                current_block = 2;
                break;
            }
        }
    }
    if current_block != 1 {
        return p;
    }
    0
}
