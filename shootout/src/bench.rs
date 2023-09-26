use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, Criterion};
use zero_knowledge::ZeroKnowledge;

// Rust lacks existential types with associated types, and it seems
// downcasting things is also a pain...
//
// _So we can't express the following_
//
// Vec<Box<dyn ZeroKnowledge>>
//
// If we didn't have associated types this would work fine.
// as it really wants the associated types to be added, or for `impl`
// doesn't work for let values.

// Please remove this when a better way is found.
#[derive(Clone)]
pub enum ZKP {
    #[cfg(feature = "triton")]
    Triton(triton::Triton),
    #[cfg(feature = "miden")]
    Miden(miden_interface::Miden),
    #[cfg(feature = "risc")]
    Risc0(risc::Risc),
    #[cfg(feature = "plonk")]
    Plonk(sudoku_plonk::JubSudoku),
    #[cfg(feature = "halo2")]
    Halo2(sudoku_halo2::sudoku::Circuit),
    #[cfg(feature = "vampir_p")]
    VampIR_Plonk(vampir_plonk::VampIRCircuit),
    #[cfg(feature = "vampir_halo2")]
    VampIR_Halo2(vampir_halo2::VampIRCircuit),
}

// Thus we offer this and much boilerplate instead.

pub fn bench_zkp(c: &mut Criterion, program_name: String, programs: Vec<ZKP>) {
    // we are doing it this way to avoid multiple mutable references at once
    let p = programs;
    #[cfg(feature = "compile")]
    let p = call_bench(c, format!("{}: compile", program_name), p, compile_zkp);
    #[cfg(feature = "prove")]
    let p = call_bench(c, format!("{}: prove", program_name), p, prove_zkp);
    #[cfg(feature = "verify")]
    let p = call_bench(c, format!("{}: verify", program_name), p, verify_zkp);
    #[cfg(feature = "prove_and_verify")]
    call_bench(c, format!("{}:", program_name), p, prove_and_verify_zkp);
}

// return the value as it moves, serves as a forth style move
fn call_bench(c: &mut Criterion, nam: String, programs: Vec<ZKP>, f: ZKPFn) -> Vec<ZKP> {
    let g = &mut c.benchmark_group(nam);
    g.sample_size(10);
    programs.iter().for_each(|x| f(g, x.clone(), name(x)));
    programs
}

////////////////////////////////////////////////////////////////////////////////
// Boilerplate ZKP Functions
////////////////////////////////////////////////////////////////////////////////

pub fn name(z: &ZKP) -> String {
    match z {
        #[cfg(feature = "triton")]
        ZKP::Triton(t) => t.name(),
        #[cfg(feature = "miden")]
        ZKP::Miden(m) => m.name(),
        #[cfg(feature = "plonk")]
        ZKP::Plonk(p) => p.name(),
        #[cfg(feature = "risc")]
        ZKP::Risc0(r) => r.name(),
        #[cfg(feature = "halo2")]
        ZKP::Halo2(h) => h.name(),
        #[cfg(feature = "vampir_p")]
        ZKP::VampIR_Plonk(vp) => vp.name(),
        #[cfg(feature = "vampir_halo2")]
        ZKP::VampIR_Halo2(vp) => vp.name(),
        _ => "Error".to_string(),
    }
}

type ZKPFn = fn(c: &mut Group, z: ZKP, name: String) -> ();

pub fn compile_zkp(c: &mut Group, z: ZKP, name: String) {
    match z {
        #[cfg(feature = "triton")]
        ZKP::Triton(t) => compile(c, t, name),
        #[cfg(feature = "miden")]
        ZKP::Miden(m) => compile(c, m, name),
        #[cfg(feature = "plonk")]
        ZKP::Plonk(p) => compile(c, p, name),
        #[cfg(feature = "risc")]
        ZKP::Risc0(r) => compile(c, r, name),
        #[cfg(feature = "halo2")]
        ZKP::Halo2(h) => compile(c, h, name),
        #[cfg(feature = "vampir_p")]
        ZKP::VampIR_Plonk(vp) => compile(c, vp, name),
        #[cfg(feature = "vampir_halo2")]
        ZKP::VampIR_Halo2(vp) => compile(c, vp, name),
    }
}

pub fn prove_zkp(c: &mut Group, z: ZKP, name: String) {
    match z {
        #[cfg(feature = "triton")]
        ZKP::Triton(t) => prove(c, t, name),
        #[cfg(feature = "miden")]
        ZKP::Miden(m) => prove(c, m, name),
        #[cfg(feature = "plonk")]
        ZKP::Plonk(p) => prove(c, p, name),
        #[cfg(feature = "risc")]
        ZKP::Risc0(r) => prove(c, r, name),
        #[cfg(feature = "halo2")]
        ZKP::Halo2(h) => prove(c, h, name),
        #[cfg(feature = "vampir_p")]
        ZKP::VampIR_Plonk(vp) => prove(c, vp, name),
        #[cfg(feature = "vampir_halo2")]
        ZKP::VampIR_Halo2(vp) => prove(c, vp, name),
    }
}

pub fn verify_zkp(c: &mut Group, z: ZKP, name: String) {
    match z {
        #[cfg(feature = "triton")]
        ZKP::Triton(t) => verify(c, t, name),
        #[cfg(feature = "miden")]
        ZKP::Miden(m) => verify(c, m, name),
        #[cfg(feature = "plonk")]
        ZKP::Plonk(p) => verify(c, p, name),
        #[cfg(feature = "risc")]
        ZKP::Risc0(r) => verify(c, r, name),
        #[cfg(feature = "halo2")]
        ZKP::Halo2(h) => verify(c, h, name),
        #[cfg(feature = "vampir_p")]
        ZKP::VampIR_Plonk(vp) => verify(c, vp, name),
        #[cfg(feature = "vampir_halo2")]
        ZKP::VampIR_Halo2(vp) => verify(c, vp, name),
    }
}

pub fn prove_and_verify_zkp(c: &mut Group, z: ZKP, name: String) {
    match z {
        #[cfg(feature = "triton")]
        ZKP::Triton(t) => prove_and_verify(c, t, name),
        #[cfg(feature = "miden")]
        ZKP::Miden(m) => prove_and_verify(c, m, name),
        #[cfg(feature = "plonk")]
        ZKP::Plonk(p) => prove_and_verify(c, p, name),
        #[cfg(feature = "risc")]
        ZKP::Risc0(r) => prove_and_verify(c, r, name),
        #[cfg(feature = "halo2")]
        ZKP::Halo2(h) => prove_and_verify(c, h, name),
        #[cfg(feature = "vampir_p")]
        ZKP::VampIR_Plonk(vp) => prove_and_verify(c, vp, name),
        #[cfg(feature = "vampir_halo2")]
        ZKP::VampIR_Halo2(vp) => prove_and_verify(c, vp, name),
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
            |mut c| v.prove(&mut c),
            criterion::BatchSize::SmallInput,
        );
    });
}

pub fn verify<Z: ZeroKnowledge>(c: &mut Group, v: Z, name: String) {
    c.bench_function(name, |b| {
        b.iter_batched(
            || {
                let mut circuit = v.compile();
                let receipt = v.prove(&mut circuit);
                (circuit, receipt)
            },
            |(mut c, p)| v.verify(p, &mut c),
            criterion::BatchSize::SmallInput,
        );
    });
}

pub fn prove_and_verify<Z: ZeroKnowledge>(c: &mut Group, v: Z, name: String) {
    c.bench_function(name, |b| b.iter(|| v.prove_and_verify()));
}
