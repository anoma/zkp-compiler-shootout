use criterion::{criterion_group, criterion_main, Criterion};
mod bench;
mod halo;
mod miden;
mod plonk;
mod risc;
mod vampir_p;
use ::risc::{FIB_FIFTY_ID, FIB_FIFTY_PATH, FIB_NINTY_TWO_ID, FIB_NINTY_TWO_PATH};
use bench::*;
////////////////////////////////////////
// Hello, you can place your benchmarks
// in each `bench_*` to_bench's vector,
// and it'll be included in the results!
////////////////////////////////////////

pub fn bench_sudoku(c: &mut Criterion) {
    let to_bench = vec![
        ZKP::Miden(miden::sudoku()),
        ZKP::Plonk(plonk::sudoku()),
        ZKP::Risc0(risc::sudoku()),
        ZKP::Halo2(halo::sudoku()),
        ZKP::VampIR_Plonk(vampir_p::sudoku()),
    ];
    bench_zkp(c, String::from("Sudoku"), to_bench)
}

pub fn bench_fib(c: &mut Criterion) {
    let to_bench = vec![
        ZKP::Miden(miden::fib_iter(93)),
        ZKP::Miden(miden::fib_fixed("92")),
        ZKP::Miden(miden::fib_fixed("50")),
        ZKP::Risc0(risc::fib(93)),
        ZKP::Risc0(risc::fib(50)),
        ZKP::Risc0(risc::fib_fixed(
            String::from("50"),
            FIB_FIFTY_ID,
            FIB_FIFTY_PATH,
        )),
        ZKP::Risc0(risc::fib_fixed(
            String::from("92"),
            FIB_NINTY_TWO_ID,
            FIB_NINTY_TWO_PATH,
        )),
    ];
    let to_bench_large = vec![
        ZKP::Miden(miden::fib_iter(1000)),
        ZKP::Risc0(risc::fib(1000)),
    ];
    bench_zkp(c, String::from("fibonacci"), to_bench);
    bench_zkp(c, String::from("fibonacci large"), to_bench_large);
}

pub fn bench_blake(c: &mut Criterion) {
    let to_bench_blake2 = vec![
        ZKP::Risc0(risc::blake2b(String::from(
        "abc", ))),
        ZKP::Risc0(risc::blake2b(String::from("abc"))),
        ZKP::VampIR_Plonk(vampir_p::blake2s()),
    ];
    let to_bench_blake3 = vec![ZKP::Miden(miden::blake3BrownFox())];
    bench_zkp(c, String::from("Blake"), to_bench_blake2);
    bench_zkp(c, String::from("Blake3"), to_bench_blake3);
}

pub fn benchmark(c: &mut Criterion) {
    // the receipt is of a minimal amount of time, so it doesn't
    // matter for testing. The code has problems if we don't include
    // it!
    bench_sudoku(c);
    bench_fib(c);
    bench_blake(c);
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
