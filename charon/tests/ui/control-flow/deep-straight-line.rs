//! A straight-line body with more blocks than the reconstruction may recurse on.
macro_rules! twice {
    ($($t:tt)*) => { $($t)* $($t)* };
}

fn f() {}

pub fn long() {
    twice! { twice! { twice! { twice! { twice! { twice! { twice! { twice! { twice! { twice! {
        f();
    } } } } } } } } } }
    twice! { twice! { twice! { f(); } } }

}
