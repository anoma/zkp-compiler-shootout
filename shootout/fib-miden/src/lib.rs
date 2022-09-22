#![feature(allocator_api)]
use miden::{Assembler, ExecutionError, Program, ProgramInputs, ProofOptions};
use miden_core::ProgramOutputs;
use std::alloc::Global;

use std::path::Path;

pub fn compile(path: &Path) -> Result<Program, miden::AssemblyError> {
    // TODO return an assembly error instead of unwrapping
    let contents = std::fs::read_to_string(path).unwrap();
    Assembler::default().compile(&contents)
}

// we just alias this really, so Ι can remember to call it for
// benchmarking
pub fn trace(
    program: &Program,
    inputs: &ProgramInputs,
) -> Result<miden::ExecutionTrace, ExecutionError> {
    miden::execute(program, inputs)
}

pub fn prove(
    program: &Program,
    inputs: &ProgramInputs,
) -> Result<(ProgramOutputs, miden::StarkProof), ExecutionError> {
    miden::prove(program, inputs, &ProofOptions::default())
}

pub fn verify_from_start(
    program: &Program,
    answer: &ProgramOutputs,
    proof: miden::StarkProof,
    inputs: &[u64],
) -> Result<(), miden::VerificationError> {
    miden::verify(program.hash(), inputs, answer, proof)
}

pub fn inputs(inputs: &[u64], advice: &[u64]) -> Result<ProgramInputs, miden::InputError> {
    ProgramInputs::new(inputs, advice, vec![])
}

pub fn prove_and_verify(path: &Path, answer: Option<&[u64]>, input: &[u64], advice: &[u64]) {
    let program = compile(path).unwrap();
    let inputs = inputs(input, advice).unwrap();
    let (outputs, proof) = prove(&program, &inputs).unwrap();
    // might as well check the answer is what we expect in this case
    match answer {
        Some(answer) => assert_eq!(answer, outputs.stack()),
        None => (),
    };
    // println!("ANSWERS: {:?}", outputs);
    verify_from_start(&program, &outputs, proof, input).unwrap();
}
