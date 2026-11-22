#![feature(pattern_type_macro, pattern_types, generic_pattern_types)]
#![allow(incomplete_features, internal_features)]
use std::pat::pattern_type;

pub trait Trait<T> {}

pub fn foo<const N: u32, T: Trait<pattern_type!(u32 is N..)>>() {}

pub fn bar<const N: u32, T: Trait<pattern_type!(u32 is N..)>>() {
    foo::<N, T>()
}

pub fn baz<U, T: Trait<U>>() {}

pub fn qux<const N: u32, T: Trait<pattern_type!(u32 is N..)>>() {
    baz::<pattern_type!(u32 is N..), T>()
}
