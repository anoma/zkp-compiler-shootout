#![no_std]
#![no_main]
#![feature(slice_flatten)]

use risc0_zkvm_guest::{env, sha};
use sudoku_core::Sudoku;
risc0_zkvm_guest::entry!(main);


pub fn main() {
    let mut puzzle: Sudoku = env::read(); 

    if !valid_solution(&puzzle){
         panic!("invalid solution");
    }
    else {
    let solution_hash = sha::digest_u8_slice(&puzzle.0.flatten());
    env::commit(&solution_hash);
    }
}

fn valid_solution(sudoku: &Sudoku) -> bool {
    for i in 0..9 {
        let mut line = 0;
        let mut col = 0;
        let mut sub = 0;
        
        for j in 0..9 {
            line += sudoku.0[i][j];
            col += sudoku.0[j][i];
            sub += sudoku.0[i / 3 * 3 + j / 3][i % 3 * 3 + j % 3];
        }
        
        if line != 45 || col != 45 || sub != 45 {
            return false;
        }
    }
    return true;
}



