use criterion::measurement::WallTime;
use criterion::BenchmarkGroup;
use risc::Risc;
use std::path::Path;
use std::str::FromStr;

pub fn fib(input: u32) -> Risc {
    Risc {
        method_id: risc::FIB_ID,
        method_path: risc::FIB_PATH,
        input: vec![input],
        name: format!("fib{}", input),
    }
}

pub fn fib_fixed(name: String, method_id: &'static [u8], method_path: &'static str) -> Risc {
    Risc {
        method_id,
        method_path,
        input: vec![0, 1],
        name: format!("fib-fixed{}", name),
    }
}

// ([
//         [7, 6, 9, 5, 3, 8, 1, 2, 4],
//         [2, 4, 3, 7, 1, 9, 6, 5, 8],
//         [8, 5, 1, 4, 6, 2, 9, 7, 3],
//         [4, 8, 6, 9, 7, 5, 3, 1, 2],
//         [5, 3, 7, 6, 2, 1, 4, 8, 9],
//         [1, 9, 2, 8, 4, 3, 7, 6, 5],
//         [6, 1, 8, 3, 5, 4, 2, 9, 7],
//         [9, 7, 4, 2, 8, 6, 5, 3, 1],
//         [3, 2, 5, 1, 9, 7, 8, 4, 6],
//     ])

pub fn bench_sudoku(c: &mut BenchmarkGroup<WallTime>) {
    // use sudoku_risc::*;
    // let receipt = prove(setup());
    // c.bench_function("RISC0: sudoku-setup", |b| b.iter(|| setup()));
    // c.bench_function("RISC0: sudoku-prove", |b| b.iter(|| prove(setup())));
    // c.bench_function("RISC0: sudoku-digest", |b| b.iter(|| digest(&receipt)));
    // c.bench_function("RISC0: sudoku-verify", |b| b.iter(|| verify(&receipt)));
    // c.bench_function("RISC0: sudoku", |b| b.iter(|| prove_and_verify()));
}

pub fn bench_fib(c: &mut BenchmarkGroup<WallTime>) {
    use risc::*;
    let receipt = prove(setup(93));
    c.bench_function("RISC0: fib-setup", |b| b.iter(|| setup(93)));
    c.bench_function("RISC0: fib-prove", |b| b.iter(|| prove(setup(93))));
    c.bench_function("RISC0: fib-digest", |b| b.iter(|| digest(&receipt)));
    c.bench_function("RISC0: fib-verify", |b| b.iter(|| verify(FIB_ID, &receipt)));
    c.bench_function("RISC0: fib", |b| b.iter(|| prove_and_verify(93)));
    bench_fib_fixed(c, FIB_FIFTY_ID, &FIB_FIFTY_PATH, "50");
    bench_fib_fixed(c, FIB_NINTY_TWO_ID, &FIB_NINTY_TWO_PATH, "92");
}

pub fn bench_fib_fixed(
    c: &mut BenchmarkGroup<WallTime>,
    method_id: &[u8],
    method_path: &dyn AsRef<Path>,
    fib_number: &str,
) {
    use risc::*;
    let setup = || setup_fix(method_id, method_path);
    let receipt = prove(setup());
    let name = format!("fib{}", fib_number);
    c.bench_function(&format!("RISC0: {}-setup", name), |b| b.iter(|| setup()));
    c.bench_function(&format!("RISC0: {}-prove", name), |b| {
        b.iter(|| prove(setup()))
    });
    c.bench_function(&format!("RISC0: {}-digest", name), |b| {
        b.iter(|| digest(&receipt))
    });
    c.bench_function(&format!("RISC0: {}-verify", name), |b| {
        b.iter(|| verify(method_id, &receipt))
    });
    c.bench_function(&format!("RISC0: {}", name), |b| {
        b.iter(|| prove_and_verify_fix(method_id, method_path))
    });
}
