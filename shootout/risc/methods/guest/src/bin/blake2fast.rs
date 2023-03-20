#![no_main]
#![feature(slice_flatten)]

use blake2::{Blake2b512, Digest};
use digest::generic_array::GenericArray;
use risc0_zkvm::guest::env;
use std::string::String;
use typenum::bit::{B0, B1};
use typenum::uint::{UInt, UTerm};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let str: String = env::read();
    let answer = hash(str);
    // // let s = str::from_utf8(&answer[..]).unwrap();
    env::commit(&vec!(&answer[..]));
    // env::commit(&vec!("T".to_string()))
}

pub fn hash(
    str: String,
) -> GenericArray<u8, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>> {
    let mut hasher = Blake2b512::new();
    hasher.update(str);
    hasher.finalize()
}
