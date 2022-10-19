use miden_interface::Miden;

pub fn sudoku() -> Miden {
    Miden {
        path: String::from("../miden-assembler/miden/sudoku.masm"),
        name: String::from("Miden"),
        advice: vec![
            7, 6, 9, 0, 5, 3, 8, 0, 1, 2, 4, 0, 2, 4, 3, 0, 7, 1, 9, 0, 6, 5, 8, 0, 8, 5, 1, 0, 4,
            6, 2, 0, 9, 7, 3, 0, 4, 8, 6, 0, 9, 7, 5, 0, 3, 1, 2, 0, 5, 3, 7, 0, 6, 2, 1, 0, 4, 8,
            9, 0, 1, 9, 2, 0, 8, 4, 3, 0, 7, 6, 5, 0, 6, 1, 8, 0, 3, 5, 4, 0, 2, 9, 7, 0, 9, 7, 4,
            0, 2, 8, 6, 0, 5, 3, 1, 0, 3, 2, 5, 0, 1, 9, 7, 0, 8, 4, 6, 0,
        ],
        input: vec![],
    }
}

pub fn fib_fixed(fib_number: &str) -> Miden {
    let name = format!("fib{}", fib_number);
    Miden {
        path: format!("../miden-assembler/miden/{}.masm", name),
        name: format!("Miden: fixed-{}", fib_number),
        advice: vec![],
        input: vec![0, 1],
    }
}

pub fn fib_iter(fib_number: u64) -> Miden {
    Miden {
        path: format!("../miden-assembler/miden/fib.masm"),
        name: format!("Miden: iter-{}", fib_number),
        advice: vec![],
        input: vec![fib_number],
    }
}
