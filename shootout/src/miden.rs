use criterion::Criterion;
use std::path::Path;

pub fn bench_fib_fix(c: &mut Criterion, fib_number: &str, answer: Option<&[u64]>) {
    let name = format!("fib{}", fib_number);
    let path_str = format!("../miden-assembler/miden/{}.masm", name);
    bench_fib_flexy(c, name, path_str, &[0, 1], &[], answer);
}

pub fn bench_fib(c: &mut Criterion, fib_number: u64, answer: Option<&[u64]>) {
    let name = format!("fib-iter-{}", fib_number);
    let path_str = String::from("../miden-assembler/miden/fib.masm");
    bench_fib_flexy(c, name, path_str, &[fib_number], &[], answer);
}

// for those who prefer a more dynamic fibonacci
pub fn bench_fib_flexy(
    c: &mut Criterion,
    name: String,
    path: String,
    input_vec: &[u64],
    advice_vec: &[u64],
    answer: Option<&[u64]>,
) {
    use fib_miden::*;
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
