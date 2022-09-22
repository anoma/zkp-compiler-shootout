use std::path::Path;

fn main() {
    // overflows at greater than u64, so we can only test at 93(92 in our program output).
    let path = Path::new("../../miden-assembler/miden/loads.masm");
    fib_miden::prove_and_verify(path, None, &[0, 1], &[94, 94, 94, 94, 94]);
    println!("Hello, world!");
}
