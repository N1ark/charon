//@ known-failure
//@ charon-args=--lift-associated-types=*
// Reduced from futures-util's `FutureExt::boxed`: the `Self` type of the `dyn Future` proof is
// `<Box<dyn Future<..>> as Deref>::Target`, which we haven't normalized yet when we use the proof.
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
