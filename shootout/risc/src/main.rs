fn main() {
    risc::prove_and_verify(51);
    risc::prove_and_verify_fix(risc::FIB_FIFTY_ID, &risc::FIB_FIFTY_PATH);
    risc::prove_and_verify_fix(risc::FIB_NINTY_TWO_ID, &risc::FIB_NINTY_TWO_PATH);
    println!("Hello, world!");
}
