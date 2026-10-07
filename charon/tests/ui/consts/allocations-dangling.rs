//@ charon-args=--consts=values
// Wide pointers without provenance.
#![allow(unused)]
const RAW_SLICE: *const [u8] = core::ptr::slice_from_raw_parts(1 as *const u8, 0);
const EMPTY: &[u8] = unsafe { &*core::ptr::slice_from_raw_parts(1 as *const u8, 0) };

fn main() {}
