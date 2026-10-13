//@ known-failure
//@ charon-args=--consts=values
// Wide pointers without provenance.
#![allow(unused)]
struct Sync<T>(T);
unsafe impl<T> core::marker::Sync for Sync<T> {}

const RAW_SLICE: *const [u8] = core::ptr::slice_from_raw_parts(1 as *const u8, 0);
const EMPTY: &[u8] = unsafe { &*core::ptr::slice_from_raw_parts(1 as *const u8, 0) };
static RAW_SLICE_STATIC: Sync<*const [u8]> = Sync(core::ptr::slice_from_raw_parts(1 as *const u8, 0));
// Unsized types that aren't unsized from a sized type.
static STR: Sync<*const str> = Sync(core::ptr::slice_from_raw_parts(1 as *const u8, 3) as *const str);
static CSTR: Sync<*const core::ffi::CStr> =
    Sync(core::ptr::slice_from_raw_parts(1 as *const u8, 3) as *const core::ffi::CStr);
struct Dst {
    x: u8,
    tail: [u8],
}
static DST: Sync<*const Dst> = Sync(core::ptr::slice_from_raw_parts(2 as *const u8, 4) as *const Dst);

fn main() {}
