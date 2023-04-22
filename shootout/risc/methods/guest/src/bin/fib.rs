#![no_std]
#![no_main]
#![feature(slice_flatten)]

risc0_zkvm::guest::entry!(main);
use risc0_zkvm::guest::env;

pub fn main() {
    let number_to_compute: u32 = env::read();
    let answer = compute(number_to_compute);
    env::commit(&answer);
}

// Rust lacks TCO, so no good functional solution for you!
// Note the non fixed version is not similar to the masm program.
// One has to look at the fib fixed version also included in this project.
pub fn compute(iteration: u32) -> u64 {
    let mut a = 0;
    let mut b = 1;
    for _ in 0..iteration {
        let c = a;
        a = b;
        b += c;
    }
    a
}
