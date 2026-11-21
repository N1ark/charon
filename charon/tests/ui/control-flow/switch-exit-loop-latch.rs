//! The block that all the `continue`s go to must not be picked as the exit of the `if`s: that
//! would duplicate the rest of the loop body in both branches of every `if`, which is exponential.
pub fn permutation(parse: fn(u32, u32) -> Result<u32, u32>, mut input: u32) -> Result<u32, u32> {
    let mut done_a = false;
    let mut done_b = false;
    let mut done_c = false;
    let mut done_d = false;
    let mut done_e = false;
    let mut done_f = false;
    loop {
        let mut err = None;
        if !done_a {
            match parse(0, input) {
                Ok(i) => {
                    input = i;
                    done_a = true;
                    continue;
                }
                Err(e) => err = Some(e),
            }
        }
        if !done_b {
            match parse(1, input) {
                Ok(i) => {
                    input = i;
                    done_b = true;
                    continue;
                }
                Err(e) => err = Some(e),
            }
        }
        if !done_c {
            match parse(2, input) {
                Ok(i) => {
                    input = i;
                    done_c = true;
                    continue;
                }
                Err(e) => err = Some(e),
            }
        }
        if !done_d {
            match parse(3, input) {
                Ok(i) => {
                    input = i;
                    done_d = true;
                    continue;
                }
                Err(e) => err = Some(e),
            }
        }
        if !done_e {
            match parse(4, input) {
                Ok(i) => {
                    input = i;
                    done_e = true;
                    continue;
                }
                Err(e) => err = Some(e),
            }
        }
        if !done_f {
            match parse(5, input) {
                Ok(i) => {
                    input = i;
                    done_f = true;
                    continue;
                }
                Err(e) => err = Some(e),
            }
        }
        return match err {
            Some(e) => Err(e),
            None => Ok(input),
        };
    }
}
