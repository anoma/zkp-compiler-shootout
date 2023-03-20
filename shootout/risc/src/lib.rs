use blake2::{Blake2b512, Digest};
use digest::generic_array::GenericArray;
pub use methods_fib::{
    BLAKE2FAST_ID, BLAKE2FAST_PATH, FIB_FIFTY_ID, FIB_FIFTY_PATH, FIB_ID, FIB_NINTY_TWO_ID,
    FIB_NINTY_TWO_PATH, FIB_PATH, SUDOKU_ID, SUDOKU_PATH,
};
use risc0_zkvm::Prover;
use risc0_zkvm::Receipt;
use std::fs;
use std::str;
use std::string::String;
use typenum::bit::{B0, B1};
use typenum::uint::{UInt, UTerm};

#[derive(Clone)]
pub struct Risc {
    pub method_id: &'static str,
    pub method_path: &'static str,
    pub input: Vec<u32>,
    pub name: String,
}

impl zero_knowledge::ZeroKnowledge for Risc {
    type C = Prover<'static>;
    type R = Receipt;

    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        let method_code = fs::read(self.method_path).unwrap();
        let mut prover = Prover::new(&method_code, self.method_id).unwrap();
        prover.add_input_u32_slice(&self.input);
        prover
    }

    fn prove(&self, setup: &mut Self::C) -> Self::R {
        setup.run().unwrap()
    }

    fn verify(&self, receipt: Self::R, _setup: &mut Self::C) {
        receipt.verify(self.method_id).unwrap()
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

pub fn blake2b(input: String) -> Risc {
    let sed = risc0_zkvm::serde::to_vec(&input).unwrap();
    Risc {
        method_id: BLAKE2FAST_ID,
        method_path: BLAKE2FAST_PATH,
        input: sed,
        name: format!("Risc0: Library-{}", input),
    }
}

// Here is mainly for testing our risc0 code
pub fn test() {
    let ans = hash("The quick brown fox jumps over the lazy dog".to_string());
    print!("{:?}", &vec!(&ans[..]));
}

pub fn hash(
    str: String,
) -> GenericArray<u8, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>> {
    let mut hasher = Blake2b512::new();
    hasher.update(str);
    hasher.finalize()
}
