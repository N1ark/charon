//@ revisions=default,unsized_strings
//@[unsized_strings] charon-args=--unsized-strings
// Const generic arguments, which are read from valtrees.
#![feature(adt_const_params, unsized_const_params)]
#![allow(incomplete_features)]
use std::marker::ConstParamTy;

#[derive(PartialEq, Eq, ConstParamTy)]
pub struct P {
    a: u8,
    b: &'static str,
}

pub fn s<const S: &'static str>() -> &'static str {
    S
}
pub fn r<const R: &'static u8>() -> u8 {
    *R
}
pub fn sl<const SL: &'static [u16]>() -> usize {
    SL.len()
}
pub fn t<const T: (u8, [u16; 2])>() {}
pub fn p<const X: P>() {}
pub fn arr_of_str<const A: [&'static str; 2]>() {}
pub fn b<const B: &'static [u8; 3]>() {}

pub fn main() {
    s::<"hé">();
    r::<{ &7 }>();
    sl::<{ &[1, 2] }>();
    t::<{ (1, [2, 3]) }>();
    p::<{ P { a: 1, b: "x" } }>();
    arr_of_str::<{ ["a", "bc"] }>();
    b::<b"abc">();
}
