use triton_opcodes::program::Program;
use triton_vm::proof::Claim;
use triton_vm::proof::Proof;
pub use triton_vm::shared_tests::FIBONACCI_SEQUENCE;
pub use triton_vm::shared_tests::VERIFY_SUDOKU;
use triton_vm::stark::*;
use triton_vm::table::master_table::MasterBaseTable;
use triton_vm::vm;
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
    type R = (Claim, Proof);

    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        Program::from_code(&self.source_code).unwrap()
    }

    fn prove(&self, program: &mut Self::C) -> Self::R {
        let standard_input = self
            .standard_input
            .iter()
            .map(|&x| BFieldElement::new(x))
            .collect::<Vec<_>>();
        let secret_input = self
            .secret_input
            .iter()
            .map(|&x| BFieldElement::new(x))
            .collect::<Vec<_>>();
        let (aet, public_output, maybe_error) =
            vm::simulate(&program, standard_input.clone(), secret_input);
        if let Some(error) = maybe_error {
            panic!("Simulation error: {}", error);
        }

        let claim = Claim {
            input: standard_input,
            program: program.to_bwords(),
            output: public_output.clone(),
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
