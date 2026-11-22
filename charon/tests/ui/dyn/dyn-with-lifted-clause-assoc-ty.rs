//@ known-panic
//@ charon-args=--lift-associated-types=*
//! Lifting the associated types of the where-clauses of a trait adds types to the binder of a
//! `dyn` of that trait.
pub trait Input {
    type Span;
}

pub trait Parser<I: Input> {
    fn parse(&self, input: I);
}

pub fn use_dyn<I: Input>(p: &dyn Parser<I>, input: I) {
    p.parse(input)
}
