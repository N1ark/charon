//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
//! Concrete where-clauses that the environment only gets through elaboration (supertraits) or
//! normalization (associated type bindings).
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
pub trait Sub: Unix {}
impl Sub for Env {}
pub fn foo() -> u32
where
    Env: Unix,
{
    <Env as Unix>::name()
}
// `Env: Unix` comes from elaborating `Env: Sub`.
pub fn via_supertrait() -> u32
where
    Env: Sub,
{
    foo() + <Env as Unix>::name()
}
// `Env: Unix` comes from normalizing `T::Item: Unix` to `Env: Unix`.
pub fn via_projection<T: Iterator<Item = Env>>() -> u32
where
    T::Item: Unix,
{
    foo() + <Env as Unix>::name()
}
pub fn user() -> u32 {
    via_supertrait() + via_projection::<std::iter::Empty<Env>>()
}
