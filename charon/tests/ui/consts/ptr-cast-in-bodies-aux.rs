//@ ignore
#![allow(invalid_from_utf8_unchecked)]
pub struct Sync<T>(pub T);
unsafe impl<T> std::marker::Sync for Sync<T> {}

pub static ARR: [u32; 3] = [1, 2, 3];
// One past the end: an offset followed by a cast.
pub static END: Sync<*const u32> = Sync(unsafe { (&raw const ARR).cast::<u32>().add(3) });
// A misaligned offset: a byte offset followed by a cast.
pub static BYTE: Sync<*const u16> = Sync(unsafe { (&raw const ARR).cast::<u8>().add(3).cast() });

#[repr(C, align(2))]
pub struct Aligned(pub [u8; 4]);
pub static BYTES: Aligned = Aligned([1, 2, 3, 4]);
// Reinterpreting the bytes as a slice: a cast followed by an unsizing cast.
pub static WORDS: &[u16] =
    unsafe { std::slice::from_raw_parts((&raw const BYTES).cast::<u16>(), 2) };

pub trait Tr: std::marker::Sync {
    fn m(&self) -> u8;
}
impl Tr for u8 {
    fn m(&self) -> u8 {
        *self
    }
}
pub struct W<T: ?Sized>(pub u8, pub T);
pub struct DynTail {
    pub x: u8,
    pub t: dyn Tr,
}
pub struct SliceTail {
    pub x: u8,
    pub t: [u16],
}

// A raw slice pointer to a whole static (raw borrow with unsizing metadata).
pub static RAW_SLICE: Sync<*const [u32]> = Sync(&raw const ARR as *const [u32]);
// A function pointer and a closure as function pointer.
pub fn foo() -> u8 {
    1
}
pub static FN: fn() -> u8 = foo;
pub static CLOSURE: fn() -> u8 = || 2;
pub static CLOSURE_RAW: Sync<*const ()> = Sync((|| 3u8) as fn() -> u8 as *const ());
// Non-generic DSTs, pointing into anonymous allocations.
pub static DYN_TAIL: &DynTail =
    unsafe { &*(&W(1u8, 2u8) as &W<dyn Tr> as *const W<dyn Tr> as *const DynTail) };
pub static SLICE_TAIL: &SliceTail =
    unsafe { &*(&W(1u8, [2u16, 3]) as &W<[u16]> as *const W<[u16]> as *const SliceTail) };
// A `str` tail.
pub static STR_TAIL: &W<str> =
    unsafe { &*(&W(0u8, [104u8, 105]) as &W<[u8]> as *const W<[u8]> as *const W<str>) };
// A non-UTF-8 `str`.
pub static BAD_STR: &str = unsafe { core::str::from_utf8_unchecked(&[0xff, 0x61]) };
// A wrapping out-of-bounds pointer.
pub static OOB: Sync<*const u32> = Sync((&raw const ARR).cast::<u32>().wrapping_sub(1));
// A `&dyn` to an anonymous allocation.
pub static DYN: &dyn Tr = &5u8;
