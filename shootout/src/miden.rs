use criterion::Criterion;
use std::path::Path;

pub fn bench_fib(c: &mut Criterion, fib_number: &str, answer: &[u64]) {
    use fib_miden::*;
    let name = format!("fib{}", fib_number);
    let path_str = format!("../miden-assembler/miden/{}.masm", name);
    let path = Path::new(&path_str);
    let program = compile(path).unwrap();
    let input = inputs(&[0, 1]).unwrap();
    let (outputs, proof) = prove(&program, &input).unwrap();
    // might as well check the answer is what we expect in this case

    assert_eq!((answer), outputs);
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
                let input = inputs(&[0, 1]).unwrap();
                let (outputs, proof) = prove(&program, &input).unwrap();
                (program, proof)
            },
            |(program, proof)| verify_from_start(&program, &[12200160415121876738], proof, &[0, 1]),
            criterion::BatchSize::SmallInput,
        )
    });
    c.bench_function(&format!("Miden: {}", name), |b| {
        b.iter(|| prove_and_verify(path, answer, &[0, 1]))
    });
}
