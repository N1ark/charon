//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
//! A where-clause that mentions no generic parameters only proves a trait ref that no impl proves:
//! `id::<u32>` and `<Nil as List>::LEN` use the impls in every item.
pub trait CastInto<T>: Copy {
    fn cast(self) -> T;
}
impl CastInto<u64> for u32 {
    fn cast(self) -> u64 {
        self as u64
    }
}
fn id<T: Copy>(x: T) -> T {
    x
}
/// The environment has `u32: Copy` as the parent clause of `u32: CastInto<T>`.
pub fn generic<T>(x: u32) -> T
where
    u32: CastInto<T>,
{
    id(x).cast()
}
pub fn plain(x: u32) -> u32 {
    id(x)
}

pub struct Nil;
pub trait List {
    const LEN: usize;
}
impl List for Nil {
    const LEN: usize = 0;
}
impl Nil {
    pub fn len(&self) -> usize
    where
        Self: List,
    {
        <Self as List>::LEN
    }
}

pub fn main() -> u64 {
    let _ = plain(1) + Nil.len() as u32;
    generic::<u64>(2)
}
