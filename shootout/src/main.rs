use criterion::{criterion_group, criterion_main, Criterion};

// TODO Put the halo code by itself and make it runable standalone!
pub fn bench_halo (c : &mut Criterion) {
    use sudoku_halo::*;
    // Halo code
    c.bench_function("HALO: sudoku-setup"  , |b| b.iter(|| setup()));
    c.bench_function("HALO: sudoku-key-gen",
                     |b| b.iter_batched(|| (circuit(), setup().unwrap()),
                                        |(circ, pp)| key_generation(&pp, circ),
                                        criterion::BatchSize::SmallInput));

    c.bench_function("HALO: sudoku-proof",
                     |b| b.iter_batched(
                         || {
                             let circ        = circuit();
                             let pp          = setup().unwrap();
                             let (pk_p, _vk) = key_generation(&pp, circ).unwrap();
                             (pp, pk_p)
                         },
                         |(pp, pk_p)|  proof(&pp, pk_p),
                         criterion::BatchSize::SmallInput));

    c.bench_function("HALO: sudoku-verify",
                     |b| b.iter_batched(
                         || {
                             let circ       = circuit();
                             let pp         = setup().unwrap();
                             let (pk_p, vk) = key_generation(&pp, circ).unwrap();
                             let (prof, pi) = proof(&pp, pk_p).unwrap();
                             (vk, pi, pp, prof)
                         },
                         |(vk, pi, pp, prof)|  verify(vk, pi, &pp, prof),
                         criterion::BatchSize::SmallInput));
    c.bench_function("HALO: sudoku", |b| b.iter(|| prove_and_verify()));
}

pub fn benchmark(c: &mut Criterion) {
    let receipt = prove(setup());
    // the receipt is of a minimal amount of time, so it doesn't
    // matter for testing. The code has problems if we don't include
    // it!
    use sudoku_risc::*;
    bench_halo(c);
    c.bench_function("RISC0: sudoku-setup" , |b| b.iter(|| setup()));
    c.bench_function("RISC0: sudoku-prove" , |b| b.iter(|| prove(setup())));
    c.bench_function("RISC0: sudoku-digest", |b| b.iter(|| digest(&receipt)));
    c.bench_function("RISC0: sudoku-verify", |b| b.iter(|| verify(&receipt)));
    c.bench_function("RISC0: sudoku"       , |b| b.iter(|| prove_and_verify()));

}
criterion_group!(benches, benchmark);
criterion_main!(benches);
