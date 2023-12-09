use giza_prover::{prove_trace, StarkProof};
use winterfell::verify;
use giza_runner::ExecutionTrace;
use giza_air::{ProcessorAir, PublicInputs, ProofOptions};
use std::path::PathBuf;

#[derive(Clone)]
pub struct CairoGiza {
    pub name: String,
    pub program: String,
    pub memory: String,
    pub trace: String,
}

impl zero_knowledge::ZeroKnowledge for CairoGiza {
    type C = ExecutionTrace;
    type R = (StarkProof, PublicInputs);
    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        // Number of serilized outputs to 1
        ExecutionTrace::from_file(PathBuf::from(&self.program), PathBuf::from(&self.trace), PathBuf::from(&self.memory), Some(1))
    }

    fn prove(&self, trace : &mut Self::C) -> Self::R {
        // Proof options are:
        //    number of queris
        //    blowup factor
        //    grinding factor
        //    fri folding factor
        //    fri max reminder size
        let trace = ExecutionTrace::from_file(PathBuf::from(&self.program), PathBuf::from(&self.trace), PathBuf::from(&self.memory), Some(1));
        let proof_options = ProofOptions::with_proof_options(None, None, None, None, None);
        prove_trace(trace, &proof_options).unwrap()
    }

    fn verify(&self, receipt: Self::R, _program: &mut Self::C) {
        match verify::<ProcessorAir>(receipt.0, receipt.1) {
            Ok(_) => println!("Execution verified"),
            Err(err) => println!("Failed to verify execution: {}", err),
        }
    }
}