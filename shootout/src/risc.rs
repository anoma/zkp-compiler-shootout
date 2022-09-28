use risc::Risc;
pub use risc::fib;

pub fn fib_fixed(name: String, method_id: &'static [u8], method_path: &'static str) -> Risc {
    Risc {
        method_id,
        method_path,
        input: vec![0, 1],
        name: format!("Risc0: fixed-{}", name),
    }
}

pub fn sudoku() -> Risc {
    Risc {
        method_id: risc::SUDOKU_ID,
        method_path: risc::SUDOKU_PATH,
        input: vec![
            7, 6, 9, 5, 3, 8, 1, 2, 4, 2, 4, 3, 7, 1, 9, 6, 5, 8, 8, 5, 1, 4, 6, 2, 9, 7, 3, 4, 8,
            6, 9, 7, 5, 3, 1, 2, 5, 3, 7, 6, 2, 1, 4, 8, 9, 1, 9, 2, 8, 4, 3, 7, 6, 5, 6, 1, 8, 3,
            5, 4, 2, 9, 7, 9, 7, 4, 2, 8, 6, 5, 3, 1, 3, 2, 5, 1, 9, 7, 8, 4, 6,
        ],
        name: String::from("Risc"),
    }
}
