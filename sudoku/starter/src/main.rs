mod halo;
use starter::starter;


pub fn main () {
    println!("WHAT {}", 7 / 3 * 3);
    starter::prove_and_verify();
    halo::main().unwrap();
}
