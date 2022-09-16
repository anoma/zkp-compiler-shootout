use std::path::Path;

fn main() {
    // overflows at greater than u64, so we can only test at 93(92 in our program output).
    let path = Path::new("../../miden-assembler/miden/fib92.masm");
    fib_miden::prove_and_verify(path, &[12200160415121876738], &[0,1]);
    println!("Hello, world!");
}
