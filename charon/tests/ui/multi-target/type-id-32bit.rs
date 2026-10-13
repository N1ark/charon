//@ charon-args=--targets=i686-unknown-linux-gnu,x86_64-unknown-linux-gnu --consts=bytes
// The pointers of a `TypeId` in raw memory, on 32-bit and 64-bit targets.
#![no_std]
use core::any::TypeId;
pub static TID: TypeId = TypeId::of::<u8>();
pub static ARR: [u32; 2] = [1, 2];
pub static P: &u32 = &ARR[1];
