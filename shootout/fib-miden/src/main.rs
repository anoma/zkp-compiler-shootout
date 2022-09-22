use std::path::Path;

fn main() {
    // overflows at greater than u64, so we can only test at 93(92 in our program output).
    let path = Path::new("../../miden-assembler/miden/loads.masm");
    let path2 = Path::new("../../miden-assembler/miden/sudoku.masm");
    fib_miden::prove_and_verify(path, None, &[0, 1], &[94, 94, 94, 94, 94]);
    fib_miden::prove_and_verify(path2, None, &[0, 0, 0, 0, 0],
                                &[7, 6, 9, 0, 5, 3, 8, 0, 1, 2, 4, 0,
                                  2, 4, 3, 0, 7, 1, 9, 0, 6, 5, 8, 0,
                                  8, 5, 1, 0, 4, 6, 2, 0, 9, 7, 3, 0,
                                  4, 8, 6, 0, 9, 7, 5, 0, 3, 1, 2, 0,
                                  5, 3, 7, 0, 6, 2, 1, 0, 4, 8, 9, 0,
                                  1, 9, 2, 0, 8, 4, 3, 0, 7, 6, 5, 0,
                                  6, 1, 8, 0, 3, 5, 4, 0, 2, 9, 7, 0,
                                  9, 7, 4, 0, 2, 8, 6, 0, 5, 3, 1, 0,
                                  3, 2, 5, 0, 1, 9, 7, 0, 8, 4, 6, 0
                                ]);
    println!("Hello, world!");
}
