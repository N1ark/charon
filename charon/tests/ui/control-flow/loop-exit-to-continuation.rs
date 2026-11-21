//! The loop is left either for the code after it (on `None` and on `break`) or for the straight-line
//! code that drops `default_port` and returns (on each `return Err`). The exit of the loop is the
//! code after it.
pub fn parse_port<P: Fn() -> Option<u16>>(
    mut input: &[u8],
    setter: bool,
    default_port: P,
) -> Result<(Option<u16>, usize), ()> {
    let mut port: u32 = 0;
    let mut has_any_digit = false;
    while let Some((&c, remaining)) = input.split_first() {
        if let Some(digit) = (c as char).to_digit(10) {
            port = port * 10 + digit;
            if port > u16::MAX as u32 {
                return Err(());
            }
            has_any_digit = true;
        } else if !setter && !matches!(c, b'/' | b'?') {
            return Err(());
        } else {
            break;
        }
        input = remaining;
    }
    if !has_any_digit && setter && !input.is_empty() {
        return Err(());
    }
    let mut opt_port = Some(port as u16);
    if !has_any_digit || opt_port == default_port() {
        opt_port = None;
    }
    Ok((opt_port, input.len()))
}
