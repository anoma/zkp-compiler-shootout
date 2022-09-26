use criterion::{criterion_group, criterion_main, Criterion};
mod miden;
mod plonk;
mod risc;
mod bench;
// TODO Put the plonk code by itself and make it runable standalone!

pub fn bench_fib(c: &mut Criterion) {
    // let ca = c;
    let group = &mut c.benchmark_group("fibonacci");
    miden::bench_fib(group, 93, None);
    miden::bench_fib(group, 1000, None);
    miden::bench_fib_fix(group, "92", None);
    miden::bench_fib_fix(group, "50", None);
    risc::bench_fib(group);
}

pub fn bench_sudoku(c: &mut Criterion) {
    let group = &mut c.benchmark_group("sudoku");
    miden::bench_sudoku(group);
    plonk::bench_sudoku(group);
    risc::bench_sudoku(group);
}

pub fn benchmark(c: &mut Criterion) {
    // the receipt is of a minimal amount of time, so it doesn't
    // matter for testing. The code has problems if we don't include
    // it!
    bench_fib(c);
    bench_sudoku(c);
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
