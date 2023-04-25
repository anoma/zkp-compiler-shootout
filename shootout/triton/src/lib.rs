use triton_opcodes::program::Program;
use triton_vm::proof::Claim;
use triton_vm::proof::Proof;
pub use triton_vm::shared_tests::FIBONACCI_SEQUENCE;
pub use triton_vm::shared_tests::VERIFY_SUDOKU;
use triton_vm::stark::*;
use triton_vm::table::master_table::MasterBaseTable;
use triton_vm::vm;
use twenty_first::shared_math::b_field_element::BFieldElement;
use twenty_first::shared_math::tip5::Tip5;
use twenty_first::util_types::algebraic_hasher::AlgebraicHasher;

#[derive(Clone)]
pub struct Triton {
    pub name: String,
    pub source_code: String,
    pub standard_input: Vec<u64>,
    pub secret_input: Vec<u64>,
}

impl zero_knowledge::ZeroKnowledge for Triton {
    type C = Program;
    type R = (Claim, Proof);

    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        Program::from_code(&self.source_code).unwrap()
    }

    fn prove(&self, program: &mut Self::C) -> Self::R {
        let public_input = Self::u64s_to_bfes(&self.standard_input);
        let secret_input = Self::u64s_to_bfes(&self.secret_input);

        let (aet, public_output, maybe_error) = vm::simulate(program, public_input, secret_input);
        if let Some(error) = maybe_error {
            panic!("Simulation error: {}", error);
        }
        let standard_output = Self::bfes_to_u64s(&public_output);

        let claim = Claim {
            input: self.standard_input.clone(),
            program_digest: Tip5::hash(program),
            output: standard_output,
            padded_height: MasterBaseTable::padded_height(&aet),
        };

        let stark = Stark::new(claim.clone(), StarkParameters::default());
        let proof = stark.prove(aet, &mut None);
        (claim, proof)
    }

    fn verify(&self, receipt: Self::R, _program: &mut Self::C) {
        let (claim, proof) = receipt;
        let stark = Stark::new(claim, StarkParameters::default());
        let verdict = stark.verify(proof, &mut None);
        if let Err(error) = verdict {
            panic!("Verification error: {error}");
        }
        assert!(verdict.unwrap());
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
