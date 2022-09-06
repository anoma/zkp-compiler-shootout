use criterion::{criterion_group, criterion_main, Criterion};
use starter::starter::*;

pub fn benchmark(c: &mut Criterion) {
    let receipt = prove(setup());
    // the receipt is of a minimal amount of time, so it doesn't
    // matter for testing. The code has problems if we don't include
    // it!
    c.bench_function("sudoku-prove" , |b| b.iter(|| prove(setup())));
    c.bench_function("sudoku-digest", |b| b.iter(|| digest(&receipt)));
    c.bench_function("sudoku-verify", |b| b.iter(|| verify(&receipt)));
    c.bench_function("sudoku"       , |b| b.iter(|| prove_and_verify()));
}
criterion_group!(benches, benchmark);
criterion_main!(benches);
