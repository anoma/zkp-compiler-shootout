use blake2::{Blake2b512, Digest};
use digest::generic_array::GenericArray;
pub use methods_fib::{
    BLAKE2FAST_ELF, BLAKE2FAST_ID, FIB_ELF, FIB_FIFTY_ELF, FIB_FIFTY_ID, FIB_ID, FIB_NINTY_TWO_ELF,
    FIB_NINTY_TWO_ID, SUDOKU_ELF, SUDOKU_ID,
};
use risc0_zkvm::{ExecutorEnv, Receipt};
use std::str;
use std::string::String;
use typenum::bit::{B0, B1};
use typenum::uint::{UInt, UTerm};

#[derive(Clone)]
pub struct Risc {
    pub method_id: [u32; 8],
    pub method_elf: &'static [u8],
    pub input: Vec<u32>,
    pub name: String,
}

impl zero_knowledge::ZeroKnowledge for Risc {
    type C = ExecutorEnv<'static>;
    type R = Receipt;

    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        let env = ExecutorEnv::builder()
            .add_input(&self.input)
            .build()
            .unwrap();
        env
    }

    fn prove(&self, env: &mut Self::C) -> Self::R {
        let prover = risc0_zkvm::default_prover();
        prover.prove_elf(env.clone(), self.method_elf).unwrap()
    }

    fn verify(&self, receipt: Self::R, _setup: &mut Self::C) {
        receipt.verify(self.method_id).unwrap()
    }
}

pub fn fib(input: u32) -> Risc {
    Risc {
        method_id: FIB_ID,
        method_elf: FIB_ELF,
        input: vec![input],
        name: format!("Risc0: iter-{}", input),
    }
}

pub fn blake2b(input: String) -> Risc {
    let sed = risc0_zkvm::serde::to_vec(&input).unwrap();
    Risc {
        method_id: BLAKE2FAST_ID,
        method_elf: BLAKE2FAST_ELF,
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
