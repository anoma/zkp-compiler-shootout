#![feature(allocator_api)]
use miden::{Assembler, ExecutionError, Program, ProgramInputs, ProofOptions};
use miden_core::ProgramOutputs;
use std::path::Path;

#[derive(Clone)]
pub struct Miden {
    pub path: String,
    pub name: String,
    pub input: Vec<u64>,
    pub advice: Vec<u64>
}

impl zero_knowledge::ZeroKnowledge for Miden {
    type C = Program;
    type R = (ProgramOutputs, miden::StarkProof);
    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        compile(Path::new(&self.path)).unwrap()
    }

    fn prove(&self, program : &Program) -> Self::R {
        let inputs = inputs(&self.input, &self.advice).unwrap();
        prove(program, &inputs).unwrap()
    }

    fn verify(&self, receipt: Self::R, program: &Self::C) {
        let (outputs, proof) = receipt;
        verify_from_start(&program, &outputs, proof, &self.input).unwrap();
    }
}

impl Miden {
    pub fn trace(&self, program: &Program) -> Result<miden::ExecutionTrace, ExecutionError> {
        let inputs = inputs(&self.input, &self.advice).unwrap();
        miden::execute(program, &inputs)
    }
}

pub fn compile(path: &Path) -> Result<Program, miden::AssemblyError> {
    // TODO return an assembly error instead of unwrapping
    let contents = std::fs::read_to_string(path).unwrap();
    Assembler::default().compile(&contents)
}

pub fn sudoku(advice: Vec<u64>) -> Miden {
    Miden {
        path: String::from("../../miden-assembler/miden/sudoku.masm"),
        name: String::from("Miden"),
        advice,
        input: vec![],
    }
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
