use starter;

pub fn main () {
    println!("WHAT {}", 7 / 3 * 3);
    starter::prove_and_verify();
    starter::halo::prove_and_verify().unwrap();
}
