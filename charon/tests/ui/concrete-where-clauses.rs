//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
//! A where-clause on a parameter-free trait reference wins over the impl when it mentions a lifetime
//! (`ref_with_clause`), not otherwise (`with_clause`). So the same trait reference resolves to the
//! where-clause in one item and to the impl in the others. Charon caches the translation of
//! parameter-free values across items, which must not mix these up.
pub trait Tr {
    fn method(&self);
}
impl Tr for u32 {
    fn method(&self) {}
}
impl<'a> Tr for &'a u8 {
    fn method(&self) {}
}

pub struct Wrap<T: Tr>(T);

pub fn before(x: Wrap<u32>) {
    x.0.method()
}
pub fn with_clause(x: Wrap<u32>)
where
    u32: Tr,
{
    x.0.method()
}
pub fn after(x: Wrap<u32>) {
    x.0.method()
}

pub fn ref_before<'a>(x: &'a u8) {
    x.method()
}
pub fn ref_with_clause<'a>(x: &'a u8)
where
    &'a u8: Tr,
{
    x.method()
}
pub fn ref_after<'a>(x: &'a u8) {
    x.method()
}
