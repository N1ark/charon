//@ charon-args=--consts=values
// References to zero-sized values without provenance.
use core::ptr::NonNull;
pub const Z: &() = unsafe { &*NonNull::<()>::dangling().as_ptr() };
pub const E: &[u8; 0] = unsafe { &*NonNull::<[u8; 0]>::dangling().as_ptr() };
pub const EM: &mut [u8; 0] = unsafe { &mut *NonNull::<[u8; 0]>::dangling().as_ptr() };
pub static ZS: &() = unsafe { &*NonNull::<()>::dangling().as_ptr() };
pub fn body() -> (&'static (), &'static [u8; 0], &'static mut [u8; 0]) {
    let a = const { unsafe { &*NonNull::<()>::dangling().as_ptr() } };
    let b = const { unsafe { &*NonNull::<[u8; 0]>::dangling().as_ptr() } };
    (a, b, EM)
}
