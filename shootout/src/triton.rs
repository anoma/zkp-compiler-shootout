use triton::Triton;
use triton::FIBONACCI_SEQUENCE;
use triton::VERIFY_SUDOKU;

pub fn sudoku() -> Triton {
    Triton {
        name: "Triton".to_string(),
        program: VERIFY_SUDOKU.clone(),
        public_input: vec![
            7, 6, 9, /**/ 5, 3, 8, /**/ 1, 2, 4, //
            2, 4, 3, /**/ 7, 1, 9, /**/ 6, 5, 8, //
            8, 5, 1, /**/ 4, 6, 2, /**/ 9, 7, 3, //
            /**********************************/ //
            4, 8, 6, /**/ 9, 7, 5, /**/ 3, 1, 2, //
            5, 3, 7, /**/ 6, 2, 1, /**/ 4, 8, 9, //
            1, 9, 2, /**/ 8, 4, 3, /**/ 7, 6, 5, //
            /**********************************/ //
            6, 1, 8, /**/ 3, 5, 4, /**/ 2, 9, 7, //
            9, 7, 4, /**/ 2, 8, 6, /**/ 5, 3, 1, //
            3, 2, 5, /**/ 1, 9, 7, /**/ 8, 4, 6, //
        ],
        secret_input: vec![],
    }
}

pub fn fib(fib_number: u64) -> Triton {
    Triton {
        name: format!("Triton: fibonacci-{fib_number}"),
        program: FIBONACCI_SEQUENCE.clone(),
        public_input: vec![fib_number],
        secret_input: vec![],
    }
}
