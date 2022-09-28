use std::fs;
pub use methods_fib::{FIB_ID,           FIB_PATH,
                      FIB_FIFTY_ID,     FIB_FIFTY_PATH,
                      FIB_NINTY_TWO_ID, FIB_NINTY_TWO_PATH,
                      SUDOKU_ID,        SUDOKU_PATH};
use risc0_zkvm_host::Prover;
use risc0_zkvm_host::Receipt;

#[derive(Clone)]
pub struct Risc {
    pub method_id: &'static [u8],
    pub method_path: &'static str,
    pub input: Vec<u32>,
    pub name: String
}

impl zero_knowledge::ZeroKnowledge for Risc {
    type C = Prover;
    type R = Receipt;

    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        let file_contents = fs::read(self.method_path).unwrap();
        let mut prover    = Prover::new(&file_contents, &self.method_id).unwrap();
        prover.add_input(&self.input).unwrap();
        prover
    }

    fn prove(&self, setup: &Self::C) -> Self::R {
        setup.run().unwrap()
    }

    fn verify(&self, receipt: Self::R, _setup: &Self::C) {
        receipt.verify(&self.method_id).unwrap()
    }
}

pub fn fib(input: u32) -> Risc {
    Risc {
        method_id: FIB_ID,
        method_path: FIB_PATH,
        input: vec![input],
        name: format!("Risc0: iter-{}", input),
    }
}
