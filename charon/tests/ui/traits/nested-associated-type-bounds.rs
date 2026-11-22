//! A bound on an associated type of an associated type: `T::A`'s bounds say that `<T::A as
//! Iterator>::Item: Clone`, also when a where-clause proves `T::A: Iterator`.
pub trait Tr {
    type A: Iterator<Item: Clone>;
}
fn needs_clone<X: Clone>(_: &X) {}

pub fn direct<T: Tr>(x: <T::A as Iterator>::Item) {
    needs_clone(&x)
}
pub fn with_clause<T: Tr>(x: <T::A as Iterator>::Item)
where
    T::A: Iterator,
{
    needs_clone(&x)
}
// Same, after resolving a trait ref about `T::A` itself.
pub fn with_clause_after<T: Tr>(x: <T::A as Iterator>::Item)
where
    T::A: Iterator,
{
    let _ = size_of::<T::A>();
    needs_clone(&x)
}
