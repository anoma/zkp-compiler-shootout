use triton_opcodes::program::Program;
use triton_vm::proof::Proof;
pub use triton_vm::shared_tests::FIBONACCI_SEQUENCE;
pub use triton_vm::shared_tests::VERIFY_SUDOKU;
use triton_vm::stark::*;
use twenty_first::shared_math::b_field_element::BFieldElement;

#[derive(Clone)]
pub struct Triton {
    pub name: String,
    pub source_code: String,
    pub standard_input: Vec<u64>,
    pub secret_input: Vec<u64>,
}

impl zero_knowledge::ZeroKnowledge for Triton {
    type C = Program;
    type R = Proof;

    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        Program::from_code(&self.source_code).unwrap()
    }

    fn prove(&self, _program: &mut Self::C) -> Self::R {
        let (_parameters, proof) = triton_vm::prove_from_source(
            &self.source_code,
            &self.standard_input,
            &self.secret_input
        ).unwrap();
        proof
    }

    fn verify(&self, proof: Self::R, _program: &mut Self::C) {
        let parameters = StarkParameters::default();
        let verdict = triton_vm::verify(&parameters, &proof);
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
