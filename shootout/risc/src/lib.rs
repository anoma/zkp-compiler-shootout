use std::fs;
pub use methods_fib::{FIB_ID,           FIB_PATH,
                      FIB_FIFTY_ID,     FIB_FIFTY_PATH,
                      FIB_NINTY_TWO_ID, FIB_NINTY_TWO_PATH};
use risc0_zkvm_host::Prover;
use risc0_zkvm_serde::from_slice;
use risc0_zkvm_host::Receipt;
use std::path::Path;

pub struct Risc<'a> {
    method_id: &'a[u8],
    method_path: &'a dyn AsRef<Path>,
    input: &'a[u32],
    name: String
}

impl<'a> zero_knowledge::ZeroKnowledge for Risc<'a> {
    type C = Prover;
    type R = Receipt;

    fn name(&self) -> &String {
        &self.name
    }

    fn compile(&self) -> Self::C {
        let file_contents = fs::read(self.method_path).unwrap();
        let mut prover    = Prover::new(&file_contents, self.method_id).unwrap();
        prover.add_input(self.input).unwrap();
        prover
    }

    fn prove(&self, setup: &Self::C) -> Self::R {
        setup.run().unwrap()
    }

    fn verify(&self, receipt: Self::R, _setup: &Self::C) {
        receipt.verify(self.method_id).unwrap()
    }
}

pub fn setup(up_to : u32) -> Prover {
    let file_contents = fs::read(FIB_PATH).unwrap();
    let mut prover    = Prover::new(&file_contents, FIB_ID).unwrap();
    prover.add_input(&[up_to]).unwrap();
    prover
}

pub fn setup_fix(method_id : &[u8], method_path : &dyn AsRef<Path>) -> Prover {
    let file_contents = fs::read(method_path).unwrap();
    let mut prover    = Prover::new(&file_contents, method_id).unwrap();
    prover.add_input(&[0, 1]).unwrap();
    prover
}

pub fn prove(prover : Prover) -> Receipt {
    prover.run().unwrap()
}

pub fn digest(receipt : &Receipt) -> u64 {
    let journal = receipt.get_journal_vec().unwrap();
    from_slice(&journal).unwrap()
}

pub fn verify(method : &[u8], receipt : &Receipt) {
    receipt.verify(method).unwrap();
}

pub fn prove_and_verify(up_to : u32) {
    let prover  = setup(up_to);
    let receipt = prove(prover);
    let digest  = digest(&receipt);
    verify(FIB_ID, &receipt);
    println!("Ι know the secret is {}", &digest);
}

pub fn prove_and_verify_fix(method_id : &[u8], method_path : &dyn AsRef<Path>) {
    let prover  = setup_fix(method_id, method_path);
    let receipt = prove(prover);
    let digest  = digest(&receipt);
    verify(method_id, &receipt);
    println!("Ι know the secret is {}", &digest);
}
