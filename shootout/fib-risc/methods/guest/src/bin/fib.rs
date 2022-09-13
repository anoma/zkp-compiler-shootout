#![no_std]
#![no_main]
#![feature(slice_flatten)]

use risc0_zkvm_guest::{env, sha};
risc0_zkvm_guest::entry!(main);

pub fn main() {
    let number_to_compute : u64 = env::read();
    let answer = compute(number_to_compute);
    env::commit(&answer);
}

// Rust lacks TCO, so no good functional solution for you!
// Note the non fixed version is not similar to the masm program.
// One has to look at the fib fixed version also included in this project.
pub fn compute(iteration : u64) -> u64 {
    let mut a = 0;
    let mut b = 1;
    for _ in 0..iteration {
        let c = a;
        a  = b;
        b += c;
    };
    a
}
