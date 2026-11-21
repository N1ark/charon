//@ charon-args=--lift-associated-types=*
// The `Self` type of a `dyn Trait` proof can be an associated type we haven't normalized yet, here
// `<Box<dyn Future<..>> as Deref>::Target`.
use std::future::Future;
use std::pin::Pin;

pub fn assert_future<T, F>(future: F) -> F
where
    F: Future<Output = T>,
{
    future
}

pub trait FutureExt: Future {
    fn boxed<'a>(self) -> Pin<Box<dyn Future<Output = Self::Output> + Send + 'a>>
    where
        Self: Sized + Send + 'a,
    {
        assert_future::<Self::Output, _>(Box::pin(self))
    }
}
