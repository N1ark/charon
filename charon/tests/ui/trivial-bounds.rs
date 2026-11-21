//@ revisions=poly,mono,mono-old
//@[mono] charon-args=--monomorphize
//@[mono] known-failure
//@[mono-old] charon-args=--monomorphize --old-trait-solver
//@[mono-old] known-failure
//! A call to an item with a trivially-false where-clause must use the caller's where-clause: there
//! is no impl to resolve to.
#![feature(trivial_bounds)]
#![allow(trivial_bounds)]
pub struct Env;
pub trait Unix {
    fn name() -> u32;
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
    foo()
}
pub fn baz() -> u32
where
    Env: Unix,
{
    bar() + foo()
}
