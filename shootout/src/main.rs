use criterion::{criterion_group, criterion_main, Criterion};
mod bench;
#[cfg(feature = "halo2")]
mod halo;
#[cfg(feature = "miden")]
mod miden;
#[cfg(feature = "plonk")]
mod plonk;
#[cfg(feature = "risc")]
mod risc;
#[cfg(feature = "triton")]
mod triton;
#[cfg(feature = "vampir_p")]
mod vampir_p;
#[cfg(feature = "vampir_halo2")]
mod vampir_halo2;
#[cfg(feature = "cairo_giza")]
mod cairo_gz;

#[cfg(feature = "risc")]
use ::risc::{FIB_FIFTY_ID, FIB_FIFTY_ELF, FIB_NINTY_TWO_ID, FIB_NINTY_TWO_ELF};
use bench::*;
////////////////////////////////////////
// Hello, you can place your benchmarks
// in each `bench_*` to_bench's vector,
// and it'll be included in the results!
////////////////////////////////////////

#[cfg(feature = "sudoku")]
pub fn bench_sudoku(c: &mut Criterion) {
    let to_bench = vec![
        #[cfg(feature = "triton")]
        ZKP::Triton(triton::sudoku()),
        #[cfg(feature = "miden")]
        ZKP::Miden(miden::sudoku()),
        #[cfg(feature = "plonk")]
        ZKP::Plonk(plonk::sudoku()),
        #[cfg(feature = "risc")]
        ZKP::Risc0(risc::sudoku()),
        #[cfg(feature = "halo2")]
        ZKP::Halo2(halo::sudoku()),
        #[cfg(feature = "vampir_p")]
        ZKP::VampIR_Plonk(vampir_p::sudoku()),
        #[cfg(feature = "vampir_halo2")]
        ZKP::VampIR_Halo2(vampir_halo2::sudoku()),
    ];
    bench_zkp(c, String::from("Sudoku"), to_bench)
}

#[cfg(feature = "fib")]
pub fn bench_fib(c: &mut Criterion) {
    let to_bench = vec![
        #[cfg(feature = "triton")]
        ZKP::Triton(triton::fib(50)),
        #[cfg(feature = "triton")]
        ZKP::Triton(triton::fib(93)),
        #[cfg(feature = "miden")]
        ZKP::Miden(miden::fib_iter(93)),
        #[cfg(feature = "miden")]
        ZKP::Miden(miden::fib_fixed("92")),
        #[cfg(feature = "miden")]
        ZKP::Miden(miden::fib_fixed("50")),
        #[cfg(feature = "risc")]
        ZKP::Risc0(risc::fib(93)),
        #[cfg(feature = "risc")]
        ZKP::Risc0(risc::fib(50)),
        #[cfg(feature = "risc")]
        ZKP::Risc0(risc::fib_fixed(
            String::from("50"),
            FIB_FIFTY_ID,
            FIB_FIFTY_ELF,
        )),
        #[cfg(feature = "risc")]
        ZKP::Risc0(risc::fib_fixed(
            String::from("92"),
            FIB_NINTY_TWO_ID,
            FIB_NINTY_TWO_ELF,
        )),
    ];
    #[allow(unused_variables)]
    let fib_sequence_idx = 1000;
    let to_bench_large = vec![
        #[cfg(feature = "triton")]
        ZKP::Triton(triton::fib(fib_sequence_idx)),
        #[cfg(feature = "miden")]
        ZKP::Miden(miden::fib_iter(fib_sequence_idx)),
        #[cfg(feature = "risc")]
        ZKP::Risc0(risc::fib(fib_sequence_idx as u32)),
    ];
    bench_zkp(c, String::from("fibonacci"), to_bench);
    bench_zkp(c, String::from("fibonacci large"), to_bench_large);
}

#[cfg(feature = "blake")]
pub fn bench_blake(c: &mut Criterion) {
    let to_bench_blake2 = vec![
        #[cfg(feature = "risc")]
        ZKP::Risc0(risc::blake2b(String::from("abc"))),
        #[cfg(feature = "vampir_p")]
        ZKP::VampIR_Plonk(vampir_p::blake2s()),
        #[cfg(feature = "vampir_halo2")]
        ZKP::VampIR_Halo2(vampir_halo2::blake2s()),
        #[cfg(feature = "cairo_giza")]
        ZKP::CairoGiza(cairo_gz::blake2s())
    ];
    let to_bench_blake3 = vec![
        #[cfg(feature = "miden")]
        ZKP::Miden(miden::blake3BrownFox())
    ];
    bench_zkp(c, String::from("Blake"), to_bench_blake2);
    bench_zkp(c, String::from("Blake3"), to_bench_blake3);
}

pub fn benchmark(c: &mut Criterion) {
    // the receipt is of a minimal amount of time, so it doesn't
    // matter for testing. The code has problems if we don't include
    // it!
    #[cfg(feature = "sudoku")]
    bench_sudoku(c);
    #[cfg(feature = "fib")]
    bench_fib(c);
    #[cfg(feature = "blake")]
    bench_blake(c);
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
