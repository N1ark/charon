//@ ignore
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
