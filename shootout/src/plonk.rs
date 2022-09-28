use criterion::measurement::WallTime;
use criterion::BenchmarkGroup;

pub fn sudoku() -> sudoku_plonk::JubSudoku {
    sudoku_plonk::make_circuit([
        [7, 6, 0, 5, 3, 8, 1, 2, 4],
        [2, 4, 3, 7, 1, 0, 6, 5, 8],
        [8, 5, 1, 4, 6, 2, 0, 7, 3],
        [4, 8, 6, 0, 7, 5, 3, 1, 2],
        [5, 3, 7, 6, 2, 1, 4, 8, 0],
        [1, 0, 2, 8, 4, 3, 7, 6, 5],
        [6, 1, 8, 3, 5, 4, 2, 0, 7],
        [0, 7, 4, 2, 8, 6, 5, 3, 1],
        [3, 2, 5, 1, 0, 7, 8, 4, 6],
    ])
}

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
