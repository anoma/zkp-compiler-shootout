#![feature(allocator_api)]
use miden::{Assembler, ProgramInputs, ProofOptions, Program, ExecutionError};
use std::alloc::Global;

use std::path::Path;

pub fn compile(path : &Path) -> Result<Program, miden::AssemblyError> {
    // TODO return an assembly error instead of unwrapping
    let contents = std::fs::read_to_string(path).unwrap();
    Assembler::default().compile(&contents)
}

// we just alias this really, so Ι can remember to call it for
// benchmarking
pub fn trace(program : &Program, inputs : &ProgramInputs)
             -> Result<miden::ExecutionTrace, ExecutionError> {
    miden::execute(program,inputs)
}

pub fn prove(program : &Program, inputs : &ProgramInputs)
             -> Result<(Vec<u64, Global>, miden::StarkProof), ExecutionError> {
    miden::prove(program, inputs, 1, &ProofOptions::default())
}

pub fn verify_from_start(program : &Program, answer : &[u64], proof : miden::StarkProof)
                         -> Result<(), miden::VerificationError> {
    miden::verify(program.hash(), &[0,1], answer, proof)
}

pub fn inputs(inputs : &[u64]) -> Result<ProgramInputs, miden::InputError> {
    ProgramInputs::from_stack_inputs(inputs)
}

pub fn prove_and_verify(path : &Path, answer : &[u64]) {
    let program = compile(path).unwrap();
    let inputs = ProgramInputs::from_stack_inputs(&[0, 1]).unwrap();
    let (outputs, proof) = prove(&program, &inputs).unwrap();
    // might as well check the answer is what we expect in this case
    assert_eq!(answer, outputs);
    verify_from_start(&program, answer, proof).unwrap();
}
