use criterion::{criterion_group, criterion_main, Criterion};
use fib_miden::trace;
use std::path::Path;

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
                         |(vk, pi, pp, prof)| verify(vk, pi, &pp, prof),
                         criterion::BatchSize::SmallInput));
    c.bench_function("HALO: sudoku", |b| b.iter(|| prove_and_verify()));
}

pub fn miden_fib(c : &mut Criterion, fib_number : &str, answer : &[u64]) {
    use fib_miden::*;
    let name = format!("fib{}", fib_number);
    let path_str = format!("../miden-assembler/miden/{}.masm", name);
    let path = Path::new(&path_str);
    let program = compile(path).unwrap();
    let input = inputs(&[0, 1]).unwrap();
    let (outputs, proof) = prove(&program, &input).unwrap();
    // might as well check the answer is what we expect in this case

    assert_eq!((answer), outputs);
    c.bench_function(&format!("Miden: {}-compile", name), |b| b.iter(|| compile(path)));
    c.bench_function(&format!("Miden: {}-trace", name)  , |b| b.iter(|| trace(&program, &input)));
    c.bench_function(&format!("Miden: {}-proof", name)  , |b| b.iter(|| prove(&program, &input)));
    c.bench_function(&format!("Miden: {}-verify", name) , |b| b.iter_batched(
        || {
            let program  = compile(path).unwrap();
            let input   = inputs(&[0, 1]).unwrap();
            let (outputs, proof) = prove(&program, &input).unwrap();
            (program, proof)
        },
        |(program, proof)| verify_from_start(&program, &[12200160415121876738], proof),
        criterion::BatchSize::SmallInput));
    c.bench_function(&format!("Miden: {}", name)  , |b| b.iter(|| prove_and_verify(path, answer)));
}

pub fn benchmark(c: &mut Criterion) {
    let receipt = prove(setup());
    // the receipt is of a minimal amount of time, so it doesn't
    // matter for testing. The code has problems if we don't include
    // it!
    use sudoku_risc::*;
    miden_fib(c, "92", &[12200160415121876738]);
    miden_fib(c, "50", &[20365011074]);
    bench_halo(c);
    c.bench_function("RISC0: sudoku-setup" , |b| b.iter(|| setup()));
    c.bench_function("RISC0: sudoku-prove" , |b| b.iter(|| prove(setup())));
    c.bench_function("RISC0: sudoku-digest", |b| b.iter(|| digest(&receipt)));
    c.bench_function("RISC0: sudoku-verify", |b| b.iter(|| verify(&receipt)));
    c.bench_function("RISC0: sudoku"       , |b| b.iter(|| prove_and_verify()));
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
