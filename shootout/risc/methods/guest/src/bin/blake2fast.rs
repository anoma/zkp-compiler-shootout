#![no_main]
#![no_std]
#![feature(slice_flatten)]

extern crate alloc;

use blake2::{Blake2b512, Digest};
use digest::generic_array::GenericArray;
use risc0_zkvm::guest::env;
use alloc::string::String;
use typenum::bit::{B0, B1};
use typenum::uint::{UInt, UTerm};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let s: String = env::read();
    let answer = hash(s);
    env::commit(&answer.as_slice());
}

pub fn hash(
    str: String,
) -> GenericArray<u8, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>> {
    let mut hasher = Blake2b512::new();
    hasher.update(str);
    hasher.finalize()
}
