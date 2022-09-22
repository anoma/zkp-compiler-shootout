use criterion::{criterion_group, criterion_main, Criterion};
mod miden;
mod plonk;
mod risc;
// TODO Put the plonk code by itself and make it runable standalone!

pub fn bench_fib(c: &mut Criterion) {
    miden::bench_fib(c, 93, Some(&[12200160415121876738]));
    miden::bench_fib(c, 1000, None);
    miden::bench_fib_fix(c, "92", Some(&[12200160415121876738]));
    miden::bench_fib_fix(c, "50", Some(&[20365011074]));
    risc::bench_fib(c);
}

pub fn bench_sudoku(c: &mut Criterion) {
    plonk::bench_sudoku(c);
    risc::bench_sudoku(c);
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
