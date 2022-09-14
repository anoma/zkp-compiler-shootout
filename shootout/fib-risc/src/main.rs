fn main() {
    fib_risc::prove_and_verify(51);
    fib_risc::prove_and_verify_fix(fib_risc::FIB_FIFTY_ID, &fib_risc::FIB_FIFTY_PATH);
    fib_risc::prove_and_verify_fix(fib_risc::FIB_NINTY_TWO_ID, &fib_risc::FIB_NINTY_TWO_PATH);
    println!("Hello, world!");
}
