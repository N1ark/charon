//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
//@[mono] known-failure
//! Concrete where-clauses on an inherent impl, on a trait, and on the parent of a closure.
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
pub fn foo() -> u32
where
    Env: Unix,
{
    <Env as Unix>::name()
}
pub struct S;
impl S
where
    Env: Unix,
{
    pub fn m(&self) -> u32 {
        foo() + <Env as Unix>::name()
    }
}
pub trait Tr
where
    Env: Unix,
{
    fn d(&self) -> u32 {
        foo() + <Env as Unix>::name()
    }
}
impl Tr for S {}
pub fn closure_user() -> u32
where
    Env: Unix,
{
    let f = || foo() + <Env as Unix>::name();
    f()
}
pub fn user() -> u32 {
    S.m() + S.d() + closure_user()
}
