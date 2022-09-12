use miden::{Assembler, ProgramInputs, ProofOptions};

use std::path::Path;

pub fn compile(path : &Path) -> Result<miden::Program, miden::AssemblyError> {
    // TODO return an assembly error instead of unwrapping
    let contents = std::fs::read_to_string(path).unwrap();
    Assembler::default().compile(&contents)
}

// we just alias this really, so Ι can remember to call it for
// benchmarking
pub fn trace(program : miden::Program, inputs : miden::ProgramInputs)
             -> Result<miden::ExecutionTrace, miden::ExecutionError> {
    miden::execute(program,inputs)
}

// pub fn prove()
