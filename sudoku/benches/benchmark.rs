use criterion::{criterion_group, criterion_main, Criterion};
use starter::starter::prove_and_verify;

pub fn benchmark(c: &mut Criterion) {
    c.bench_function("sudoku", |b| b.iter(|| prove_and_verify()));
}
criterion_group!(benches, benchmark);
criterion_main!(benches);
