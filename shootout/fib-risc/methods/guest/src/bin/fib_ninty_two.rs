#![no_std]
#![no_main]
#![feature(slice_flatten)]

use risc0_zkvm_guest::{env, sha};
risc0_zkvm_guest::entry!(main);

pub fn main() {
    let starting_value_1 : u64 = env::read();
    let starting_value_2 : u64 = env::read();
    let answer = compute(starting_value_1, starting_value_2);
    env::commit(&answer);
}

pub fn compute(start1 : u64, start2 : u64) -> u64 {
    let mut a = start1;
    let mut b = start2;
    for _ in 0..92 {
        let c = a;
        a  = b;
        b += c;
    };
    a
}
