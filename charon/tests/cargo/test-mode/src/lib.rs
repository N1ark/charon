//! `charon cargo --test --start-from-attribute=test -- --lib` translates the unit tests, which keep
//! their `#[test]` attribute.

fn answer() -> u32 {
    42
}

mod helpers {
    pub mod tests {
        /// Not a test, though its path ends with the path of one.
        pub fn plain() -> u32 {
            super::super::answer()
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn plain() {
        assert_eq!(crate::helpers::tests::plain(), 42);
    }

    #[test]
    #[should_panic]
    fn panics() {
        panic!()
    }

    #[test]
    #[ignore]
    fn ignored() {}
}
