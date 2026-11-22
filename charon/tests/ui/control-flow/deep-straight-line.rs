//@ no-check-output
// A straight-line body with more blocks (1024 calls) than our recursion limit.
macro_rules! twice {
    ($($t:tt)*) => { $($t)* $($t)* };
}

fn f() {}

pub fn long() {
    twice! { twice! { twice! { twice! { twice! { twice! { twice! { twice! { twice! { twice! {
        f();
    } } } } } } } } } }
}
