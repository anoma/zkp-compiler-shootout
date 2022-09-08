use criterion::{criterion_group, criterion_main, Criterion};
use sudoku::*;

pub fn benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| sudoku::starter::main()));
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
