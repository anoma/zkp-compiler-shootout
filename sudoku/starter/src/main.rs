use std::fs;
use starter::starter;
use methods::{MULTIPLY_ID, MULTIPLY_PATH};
use risc0_zkvm_core::Digest;
use risc0_zkvm_host::Prover;
use risc0_zkvm_serde::{from_slice, to_vec};
use sudoku_core::Sudoku;

    pub fn main () {
        starter::prove_and_verify();
    }
