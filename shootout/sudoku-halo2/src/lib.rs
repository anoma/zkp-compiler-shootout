use std::time::Instant;

use halo2_proofs::{arithmetic::FieldExt, plonk::Error};
use pasta_curves::pallas;
use rand::rngs::OsRng;

use crate::sudoku::{Circuit, VerifyingKey, ProvingKey, Proof};

pub mod circuit;
pub mod sudoku;


pub fn prove_and_verify() ->  Result<(), Error> {

    let time = Instant::now();

    let sudoku = [
        [7, 6, 9, 5, 3, 8, 1, 2, 4],
        [2, 4, 3, 7, 1, 9, 6, 5, 8],
        [8, 5, 1, 4, 6, 2, 9, 7, 3],
        [4, 8, 6, 9, 7, 5, 3, 1, 2],
        [5, 3, 7, 6, 2, 1, 4, 8, 9],
        [1, 9, 2, 8, 4, 3, 7, 6, 5],
        [6, 1, 8, 3, 5, 4, 2, 9, 7],
        [9, 7, 4, 2, 8, 6, 5, 3, 1],
        [3, 2, 5, 1, 9, 7, 8, 4, 6],
    ];

    let circuit = Circuit { sudoku };

    let public_input = &[pallas::Base::from_u128(45 as u128); 27];
    
    println!("circuit: \t\t{:?}ms", (Instant::now() - time).as_millis());

    // Compile the circuit
    let time = Instant::now();

    let pk = ProvingKey::build();
    let vk = VerifyingKey::build();

    println!("key generation: \t{:?}ms",(Instant::now() - time).as_millis());

    // Prover POV
    let time = Instant::now();

    let proof = Proof::create(&pk, circuit, &[public_input], &mut OsRng).unwrap();

    println!("proof: \t\t\t{:?}ms", (Instant::now() - time).as_millis());

    // Verifier POV
    let time = Instant::now();

    let res = proof.verify(&vk, &[public_input]);

    println!("verification: \t\t{:?}ms", (Instant::now() - time).as_millis());
    res
}
