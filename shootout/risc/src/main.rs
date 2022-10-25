use hex_literal::hex;
use zero_knowledge::ZeroKnowledge;

fn main() {
    risc::fib(51).prove_and_verify();
    let b2 = risc::blake2b("The quick brown fox jumps over the lazy dog".to_string());
    let c = b2.compile();
    println!("{:?}", b2.prove(&c).get_journal());
    // roughly same answers, just weirdly formatted back, but works
    // for speed testing
    risc::test();
    println!("Hello, world!");
}
