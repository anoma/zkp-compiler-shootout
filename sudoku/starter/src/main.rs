use std::fs;
use methods::{MULTIPLY_ID, MULTIPLY_PATH};
use risc0_zkvm_core::Digest;
use risc0_zkvm_host::Prover;
use risc0_zkvm_serde::{from_slice, to_vec};
use sudoku_core::Sudoku;

    pub fn main () {

        let puzzle = Sudoku ([[ 7, 6, 9, 5, 3, 8, 1, 2, 4],
                              [ 2, 4, 3, 7, 1, 9, 6, 5, 8],
                              [ 8, 5, 1, 4, 6, 2, 9, 7, 3],
                              [ 4, 8, 6, 9, 7, 5, 3, 1, 2],
                              [ 5, 3, 7, 6, 2, 1, 4, 8, 9],
                              [ 1, 9, 2, 8, 4, 3, 7, 6, 5],
                              [ 6, 1, 8, 3, 5, 4, 2, 9, 7],
                              [ 9, 7, 4, 2, 8, 6, 5, 3, 1],
                              [ 3, 2, 5, 1, 9, 7, 8, 4, 6]]);
        let file_contents = fs::read(MULTIPLY_PATH).unwrap();
        let mut prover = Prover::new(&file_contents, MULTIPLY_ID).unwrap();
        let puzzle_vec = to_vec(&puzzle).unwrap();

        prover.add_input(&puzzle_vec).unwrap();

        let receipt = prover.run().unwrap();

        let journal = receipt.get_journal_vec().unwrap();

        let sudoku_hash: Digest = from_slice(&journal).unwrap();

        println!( "Sudoku hash is {}", &sudoku_hash);

        receipt.verify(MULTIPLY_ID).unwrap();
    }
