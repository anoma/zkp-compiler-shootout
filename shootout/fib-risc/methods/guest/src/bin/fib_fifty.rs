#![no_std]
#![no_main]
#![feature(slice_flatten)]

use risc0_zkvm_guest::{env, sha};
risc0_zkvm_guest::entry!(main);

pub fn main() {
    let starting_value_1 : u32 = env::read();
    let starting_value_2 : u32 = env::read();
    let answer = compute(starting_value_1, starting_value_2);
    env::commit(&answer);
}

pub fn compute(start1 : u32, start2 : u32) -> u64 {
    let mut a = start1 as u64;
    let mut b = start2 as u64;
    for _ in 0..51 {
        let c = a;
        a  = b;
        b += c;
    };
    a
}
