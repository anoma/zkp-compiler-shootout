use criterion::measurement::WallTime;
use criterion::BenchmarkGroup;
use miden_interface::Miden;
use std::path::Path;
use std::str::FromStr;

pub fn sudoku() -> Miden {
    Miden {
        path: String::from("../miden-assembler/miden/sudoku.masm"),
        name: String::from("Sudoku"),
        advice: vec![
            7, 6, 9, 0, 5, 3, 8, 0, 1, 2, 4, 0, 2, 4, 3, 0, 7, 1, 9, 0, 6, 5, 8, 0, 8, 5, 1, 0, 4,
            6, 2, 0, 9, 7, 3, 0, 4, 8, 6, 0, 9, 7, 5, 0, 3, 1, 2, 0, 5, 3, 7, 0, 6, 2, 1, 0, 4, 8,
            9, 0, 1, 9, 2, 0, 8, 4, 3, 0, 7, 6, 5, 0, 6, 1, 8, 0, 3, 5, 4, 0, 2, 9, 7, 0, 9, 7, 4,
            0, 2, 8, 6, 0, 5, 3, 1, 0, 3, 2, 5, 0, 1, 9, 7, 0, 8, 4, 6, 0,
        ],
        input: vec![],
    }
}

pub fn bench_fib_fix(c: &mut BenchmarkGroup<WallTime>, fib_number: &str, answer: Option<&[u64]>) {
    let name = format!("Miden: fixed-{}", fib_number);
    let path_str = format!("../miden-assembler/miden/{}.masm", name);
    bench_flexy(c, name, path_str, &[0, 1], &[], answer);
}

pub fn bench_fib(c: &mut BenchmarkGroup<WallTime>, fib_number: u64, answer: Option<&[u64]>) {
    let name = format!("Miden: iter-{}", fib_number);
    let path_str = String::from("../miden-assembler/miden/fib.masm");
    bench_flexy(c, name, path_str, &[fib_number], &[], answer);
}

pub fn bench_sudoku(c: &mut BenchmarkGroup<WallTime>) {
    let name = String::from("Miden");
    let path_str = String::from("../miden-assembler/miden/sudoku.masm");
    let advice = &[
        7, 6, 9, 0, 5, 3, 8, 0, 1, 2, 4, 0, 2, 4, 3, 0, 7, 1, 9, 0, 6, 5, 8, 0, 8, 5, 1, 0, 4, 6,
        2, 0, 9, 7, 3, 0, 4, 8, 6, 0, 9, 7, 5, 0, 3, 1, 2, 0, 5, 3, 7, 0, 6, 2, 1, 0, 4, 8, 9, 0,
        1, 9, 2, 0, 8, 4, 3, 0, 7, 6, 5, 0, 6, 1, 8, 0, 3, 5, 4, 0, 2, 9, 7, 0, 9, 7, 4, 0, 2, 8,
        6, 0, 5, 3, 1, 0, 3, 2, 5, 0, 1, 9, 7, 0, 8, 4, 6, 0,
    ];
    bench_flexy(c, name, path_str, &[], advice, None);
}

// for those who prefer a more dynamic fibonacci
pub fn bench_flexy(
    c: &mut BenchmarkGroup<WallTime>,
    name: String,
    path: String,
    input_vec: &[u64],
    advice_vec: &[u64],
    answer: Option<&[u64]>,
) {
    use miden_interface::*;
    let path = Path::new(&path);
    let program = compile(path).unwrap();
    let input = inputs(input_vec, advice_vec).unwrap();
    let (outputs, _proof) = prove(&program, &input).unwrap();

    match answer {
        Some(answer) => assert_eq!(answer, outputs.stack()),
        None => (),
    };

    c.bench_function(&format!("Miden: {}-compile", name), |b| {
        b.iter(|| compile(path))
    });
    c.bench_function(&format!("Miden: {}-trace", name), |b| {
        b.iter(|| trace(&program, &input))
    });
    c.bench_function(&format!("Miden: {}-proof", name), |b| {
        b.iter(|| prove(&program, &input))
    });
    c.bench_function(&format!("Miden: {}-verify", name), |b| {
        b.iter_batched(
            || {
                let program = compile(path).unwrap();
                let input = inputs(input_vec, advice_vec).unwrap();
                let (outputs, proof) = prove(&program, &input).unwrap();
                (program, proof, outputs)
            },
            |(program, proof, outputs)| verify_from_start(&program, &outputs, proof, input_vec),
            criterion::BatchSize::SmallInput,
        )
    });
    c.bench_function(&format!("Miden: {}", name), |b| {
        b.iter(|| prove_and_verify(path, answer, input_vec, advice_vec))
    });
}
