//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
//@ charon-args=--include core::ops::function::FnPtr::addr
#![feature(fn_static)]
use std::ops::FnPtr;

pub fn addr(f: fn()) -> usize {
    f.addr()
}
