#![no_std]

use serde::{Deserialize, Serialize};

#[derive(Clone, Serialize, Deserialize, Debug, Eq, PartialEq)]
pub struct Sudoku(pub [[u8; 9]; 9]);
