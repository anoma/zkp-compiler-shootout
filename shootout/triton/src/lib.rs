use triton_vm::BFieldElement;
pub use triton_vm::example_programs::FIBONACCI_SEQUENCE;
pub use triton_vm::example_programs::VERIFY_SUDOKU;
use triton_vm::Program;
use triton_vm::Proof;
use triton_vm::Claim;
use triton_vm::stark::*;

#[derive(Clone)]
pub struct Triton {
    pub name: String,
    pub program: Program,
    pub public_input: Vec<u64>,
    pub secret_input: Vec<u64>,
}

impl zero_knowledge::ZeroKnowledge for Triton {
    type C = Program;
    type R = (Claim, Proof);

    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        self.program.clone()
    }

    fn prove(&self, program: &mut Self::C) -> Self::R {
        let (_parameters, claim, proof) = triton_vm::prove_program(
            &program,
            &self.public_input,
            &self.secret_input.clone().into(),
        ).unwrap();
        (claim, proof)
    }

    fn verify(&self, claim_and_proof: Self::R, _program: &mut Self::C) {
        let parameters = StarkParameters::default();
        let (claim, proof) = claim_and_proof;
        let verdict = triton_vm::verify(&parameters, &claim, &proof);
        assert!(verdict);
    }
}

impl Triton {
    /// Convert a vector of u64s to a vector of base field elements, i.e., `BFieldElement`s.
    pub fn u64s_to_bfes(input: &[u64]) -> Vec<BFieldElement> {
        input.iter().map(|&x| BFieldElement::new(x)).collect::<Vec<_>>()
    }

    /// Convert a vector of base field elements, i.e., `BFieldElement`s, to a vector of u64s.
    pub fn bfes_to_u64s(input: &[BFieldElement]) -> Vec<u64> {
        input.iter().map(|&x| x.value()).collect::<Vec<_>>()
    }
}
