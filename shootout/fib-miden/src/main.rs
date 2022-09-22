use std::path::Path;

fn main() {
    // overflows at greater than u64, so we can only test at 93(92 in our program output).
    let path = Path::new("../../miden-assembler/miden/loads.masm");
    let path2 = Path::new("../../miden-assembler/miden/trying.masm");
    fib_miden::prove_and_verify(path, None, &[0, 1], &[94, 94, 94, 94, 94]);
    fib_miden::prove_and_verify(path2, None, &[0, 0, 0, 0, 0],
                                &[7, 6, 9, 5, 3, 8, 1, 2, 4,
                                  2, 4, 3, 7, 1, 9, 6, 5, 8,
                                  8, 5, 1, 4, 6, 2, 9, 7, 3,
                                  4, 8, 6, 9, 7, 5, 3, 1, 2,
                                  5, 3, 7, 6, 2, 1, 4, 8, 9,
                                  5, 3, 7, 6, 2, 1, 4, 8, 9,
                                  1, 9, 2, 8, 4, 3, 7, 6, 5,
                                  6, 1, 8, 3, 5, 4, 2, 9, 7,
                                  9, 7, 4, 2, 8, 6, 5, 3, 1,
                                  3, 2, 5, 1, 9, 7, 8, 4, 6
                                ]);
    println!("Hello, world!");
}
