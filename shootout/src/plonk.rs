use criterion::measurement::WallTime;
use criterion::BenchmarkGroup;

pub fn bench_sudoku(c: &mut BenchmarkGroup<WallTime>) {
    use sudoku_plonk::*;
    // Halo code
    c.bench_function("PLONK: sudoku-setup", |b| b.iter(|| setup()));
    c.bench_function("PLONK: sudoku-key-gen", |b| {
        b.iter_batched(
            || (circuit(), setup().unwrap()),
            |(circ, pp)| key_generation(&pp, circ),
            criterion::BatchSize::SmallInput,
        )
    });

    c.bench_function("PLONK: sudoku-proof", |b| {
        b.iter_batched(
            || {
                let circ = circuit();
                let pp = setup().unwrap();
                let (pk_p, _vk) = key_generation(&pp, circ).unwrap();
                (pp, pk_p)
            },
            |(pp, pk_p)| proof(&pp, &pk_p),
            criterion::BatchSize::SmallInput,
        )
    });

    c.bench_function("PLONK: sudoku-verify", |b| {
        b.iter_batched(
            || {
                let circ = circuit();
                let pp = setup().unwrap();
                let (pk_p, vk) = key_generation(&pp, circ).unwrap();
                let (prof, pi) = proof(&pp, &pk_p).unwrap();
                (vk, pi, pp, prof)
            },
            |(vk, pi, pp, prof)| verify(&vk, pi, &pp, prof),
            criterion::BatchSize::SmallInput,
        )
    });
    c.bench_function("PLONK: sudoku", |b| b.iter(|| prove_and_verify()));
}
