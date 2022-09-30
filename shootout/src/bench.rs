use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, Criterion};
use zero_knowledge::ZeroKnowledge;
// Rust lacks existential types, and it seems downcasting things is
// also a pain...
// _So we can't express the following_
//
// Vec<dyn ZeroKnowledge> or Vec<Box<impl ZeroKnowledge>>
//
// as it really wants the generics to be added, or for `impl` doesn't
// work for let values.

// Please remove this when a better way is found.
#[derive(Clone)]
pub enum ZKP {
    Miden(miden_interface::Miden),
    Risc0(risc::Risc),
    Plonk(sudoku_plonk::JubSudoku),
    Halo2(sudoku_halo2::sudoku::Circuit),
}

// Thus we offer this and much boilerplate instead.

pub fn bench_zkp(c: &mut Criterion, program_name: String, programs: Vec<ZKP>) {
    // we are doing it this way to avoid multiple mutable references at once
    let p = programs;
    let p = call_bench(c, format!("{}: compile", program_name), p, compile_zkp);
    let p = call_bench(c, format!("{}: prove", program_name), p, prove_zkp);
    let p = call_bench(c, format!("{}: verify", program_name), p, verify_zkp);
    call_bench(c, format!("{}:", program_name), p, prove_and_verify_zkp);
}

// return the value as it moves, serves as a forth style move
fn call_bench(c: &mut Criterion, nam: String, programs: Vec<ZKP>, f: ZKPFn) -> Vec<ZKP> {
    let g = &mut c.benchmark_group(nam);
    programs.iter().for_each(|x| f(g, x.clone(), name(x)));
    programs
}

////////////////////////////////////////////////////////////////////////////////
// Boilerplate ZKP Functions
////////////////////////////////////////////////////////////////////////////////

pub fn name(z: &ZKP) -> String {
    match z {
        ZKP::Miden(m) => m.name(),
        ZKP::Plonk(p) => p.name(),
        ZKP::Risc0(r) => r.name(),
        ZKP::Halo2(h) => h.name(),
    }
}

type ZKPFn = fn(c: &mut Group, z: ZKP, name: String) -> ();

pub fn compile_zkp(c: &mut Group, z: ZKP, name: String) {
    match z {
        ZKP::Miden(m) => compile(c, m, name),
        ZKP::Plonk(p) => compile(c, p, name),
        ZKP::Risc0(r) => compile(c, r, name),
        ZKP::Halo2(h) => compile(c, h, name),
    }
}

pub fn prove_zkp(c: &mut Group, z: ZKP, name: String) {
    match z {
        ZKP::Miden(m) => prove(c, m, name),
        ZKP::Plonk(p) => prove(c, p, name),
        ZKP::Risc0(r) => prove(c, r, name),
        ZKP::Halo2(h) => prove(c, h, name),
    }
}

pub fn verify_zkp(c: &mut Group, z: ZKP, name: String) {
    match z {
        ZKP::Miden(m) => verify(c, m, name),
        ZKP::Plonk(p) => verify(c, p, name),
        ZKP::Risc0(r) => verify(c, r, name),
        ZKP::Halo2(h) => verify(c, h, name),
    }
}

pub fn prove_and_verify_zkp(c: &mut Group, z: ZKP, name: String) {
    match z {
        ZKP::Miden(m) => prove_and_verify(c, m, name),
        ZKP::Plonk(p) => prove_and_verify(c, p, name),
        ZKP::Risc0(r) => prove_and_verify(c, r, name),
        ZKP::Halo2(h) => prove_and_verify(c, h, name),
    }
}

////////////////////////////////////////////////////////////////////////////////
// Calls over the interface into timing
////////////////////////////////////////////////////////////////////////////////

type Group<'a> = BenchmarkGroup<'a, WallTime>;

pub fn compile<Z: ZeroKnowledge>(c: &mut Group, v: Z, name: String) {
    c.bench_function(name, |b| b.iter(|| v.compile()));
}

pub fn prove<Z: ZeroKnowledge>(c: &mut Group, v: Z, name: String) {
    c.bench_function(name, |b| {
        b.iter_batched(
            || v.compile(),
            |c| v.prove(&c),
            criterion::BatchSize::SmallInput,
        );
    });
}

pub fn verify<Z: ZeroKnowledge>(c: &mut Group, v: Z, name: String) {
    c.bench_function(name, |b| {
        b.iter_batched(
            || {
                let circuit = v.compile();
                let receipt = v.prove(&circuit);
                (circuit, receipt)
            },
            |(c, p)| v.verify(p, &c),
            criterion::BatchSize::SmallInput,
        );
    });
}

pub fn prove_and_verify<Z: ZeroKnowledge>(c: &mut Group, v: Z, name: String) {
    c.bench_function(name, |b| b.iter(|| v.prove_and_verify()));
}
