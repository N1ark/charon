//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
//! The associated type binding of a where-clause that mentions no generic parameters constrains
//! that where-clause, even though an impl proves its trait ref.
use std::ops::Add;
pub trait FloatConst {
    fn tau() -> Self
    where
        Self: Sized + Add<Self, Output = Self>;
}
impl FloatConst for f32 {
    fn tau() -> f32 {
        6.28
    }
}
pub fn double() -> f32
where
    f32: Add<f32, Output = f32>,
{
    f32::tau() + f32::tau()
}
