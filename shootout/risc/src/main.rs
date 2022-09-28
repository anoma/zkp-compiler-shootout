use zero_knowledge::ZeroKnowledge;

fn main() {
    risc::fib(51).prove_and_verify();
    println!("Hello, world!");
}
