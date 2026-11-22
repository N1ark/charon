//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
//@[mono] known-failure
//! Concrete where-clauses that an impl also proves: the impl takes precedence.
#![feature(trivial_bounds)]
#![allow(trivial_bounds)]
pub struct Env;
pub trait Unix {
    fn name() -> u32;
}
impl Unix for Env {
    fn name() -> u32 {
        1
    }
}
pub struct W<'a>(pub &'a u32);
pub trait Lt {
    fn lt() -> u32;
}
impl<'a> Lt for W<'a> {
    fn lt() -> u32 {
        2
    }
}
pub fn foo() -> u32
where
    Env: Unix,
{
    <Env as Unix>::name()
}
pub fn bar() -> u32
where
    Env: Unix,
{
    foo() + <Env as Unix>::name()
}
pub fn lt_user<'a>(x: W<'a>) -> u32
where
    W<'a>: Lt,
{
    let _ = x;
    <W<'a> as Lt>::lt() + foo()
}
pub fn plain() -> u32 {
    foo() + <Env as Unix>::name()
}
pub fn generic<T: Clone>(t: T) -> u32
where
    Env: Unix,
{
    let _ = t.clone();
    foo()
}
pub fn main_like() -> u32 {
    bar() + plain() + generic(3u8) + lt_user(W(&0))
}
