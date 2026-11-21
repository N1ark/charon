//! A chain of range tests that all jump to the same `true` block. That block being the exit of a
//! switch must not prevent the following switches from getting an exit, otherwise the rest of the
//! chain gets duplicated in both branches of every test.
pub fn is_code_point(c: char) -> bool {
    matches!(c,
        'a'..='z' | 'A'..='Z' | '0'..='9' | '!' | '$' | '&' |
        '('..='+' | '-'..='/' | ':'..=';' | '<'..='>' | '['..=']')
}
