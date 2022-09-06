//! Sudoku PLONK Example

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::TEModelParameters;
use ark_ed_on_bls12_381::EdwardsParameters as JubjubParameters;
use ark_ff::PrimeField;
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::{sonic_pc::SonicKZG10, PolynomialCommitment};
use plonk::error::to_pc_error;
use plonk_core::circuit::{verify_proof, Circuit};
use plonk_core::constraint_system::StandardComposer;
use plonk_core::error::Error;
use plonk_core::prelude::*;
use rand_core::OsRng;

use std::time::Instant;
use std::{cmp::min, marker::PhantomData};

use plonk_core::prelude::Variable;
use plonk_hashing::poseidon::{
    constants::PoseidonConstants,
    poseidon::{PlonkSpec, Poseidon},
};

pub fn fiat_shamir_gadget<
        F: PrimeField,
    P: TEModelParameters<BaseField = F>,
    >(
    composer: &mut StandardComposer<F, P>,
    secret: &[u8],
) -> Variable {
    // fiat-shamir using Poseidon hash with two inputs, so it works for a secret
    // of at most 2*32=64 bytes
    assert!(secret.len() < 64);

    // for two inputs we need to set 2+1 = 3 in the Poseidon parameters
    let poseidon_hash_param = PoseidonConstants::generate::<3>();
    let mut poseidon_circuit =
        Poseidon::<_, PlonkSpec<3>, 3>::new(composer, &poseidon_hash_param);

    // fill the Poseidon inputs with the bytes
    for i in 0..secret.len() / 32 {
        let f = F::from_le_bytes_mod_order(
            &secret[32 * i..min(32 * (i + 1), secret.len())],
        );
        let var_f = composer.add_input(f);
        poseidon_circuit.input(var_f).unwrap();
    }
    poseidon_circuit.output_hash(composer)
}

pub fn field_addition_gadget<
        F: PrimeField,
    P: TEModelParameters<BaseField = F>,
    >(
    composer: &mut StandardComposer<F, P>,
    var_a: Variable,
    var_b: Variable,
) -> Variable {
    // simple circuit for the computaiton of a+b (and return the variable
    // corresponding to c=a+b).
    let one = F::one();
    let c = composer.get_value(&var_a) + composer.get_value(&var_b);
    let var_zero = composer.zero_var();
    // Make first constraint a + b = c (as public input)
    composer.arithmetic_gate(|gate| {
        gate.witness(var_a, var_b, Some(var_zero))
            .add(one, one)
            .pi(-c)
    });
    composer.add_input(c)
}

pub fn field_multiplication_gadget<
        F: PrimeField,
    P: TEModelParameters<BaseField = F>,
    >(
    composer: &mut StandardComposer<F, P>,
    var_a: Variable,
    var_b: Variable,
) -> Variable {
    // simple circuit for the computaiton of a+b (and return the variable
    // corresponding to c=a+b).
    let one = F::one();
    let c = composer.get_value(&var_a) * composer.get_value(&var_b);
    let var_zero = composer.zero_var();
    // Make first constraint a + b = c (as public input)
    composer.arithmetic_gate(|gate| {
        gate.witness(var_a, var_b, Some(var_zero)).mul(one).pi(-c)
    });
    composer.add_input(c)
}

// create the circuit corresponding to the last theorem of the PLONK paper, i.e.
// checking that prod([i + gamma for i in range(9)]) == prod([sigma[i] + gamma
// for i in range(9)]) for random gamma.
pub fn permutation_gadget<
        F: PrimeField,
    P: TEModelParameters<BaseField = F>,
    >(
    composer: &mut StandardComposer<F, P>,
    permutation: [u8; 9],
    var_gamma: Variable,
) {
    // prod_i (i + gamma) and prod_i (sigma(i) + gamma)
    let mut var_lhs = composer.add_input(F::one());
    let mut var_rhs = composer.add_input(F::one());
    for i in 0..9 {
        // t = i + gamma
        // lhs = lhs * t
        let var_i = composer.add_input(F::from(i as u8));
        let var_t = field_addition_gadget::<F, P>(composer, var_i, var_gamma);
        var_lhs = field_multiplication_gadget::<F, P>(composer, var_lhs, var_t);
        // u = sigma(i) + gamma
        // rhs = rhs * u
        let var_sigma_i = composer.add_input(F::from(permutation[i]));
        let var_u =
            field_addition_gadget::<F, P>(composer, var_sigma_i, var_gamma);
        var_rhs = field_multiplication_gadget::<F, P>(composer, var_rhs, var_u);
    }
    composer.assert_equal(var_lhs, var_rhs);
}

pub fn main() -> Result<(), Error> {
    // Implements a circuit that checks if a sudoku works.
    #[derive(derivative::Derivative)]
    #[derivative(Debug(bound = ""), Default(bound = ""))]
    pub struct SudokuCircuit<F, P> {
        sudoku: [[u8; 9]; 9],
        _marker1: PhantomData<F>,
        _marker2: PhantomData<P>,
    }

    impl<F, P> Circuit<F, P> for SudokuCircuit<F, P>
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
    {
        const CIRCUIT_ID: [u8; 32] = [0xff; 32];

        fn gadget(
            &mut self,
            composer: &mut StandardComposer<F, P>,
        ) -> Result<(), Error> {
            // sudoku as a list of bytes
            let sudoku = self.sudoku.concat();
            // entries of the sudoku are actually < 16. We can halve the size of
            // the list representing the sudoku.
            let s1 = &sudoku[..sudoku.len() / 2];
            let s2 = &sudoku[sudoku.len() / 2..];
            let smaller_sudoku: Vec<u8> = s1
                .iter()
                .zip(s2.iter())
                .map(|(b1, b2)| b1 + 16 * b2)
                .collect();
            // we generate gamma from this shorter list
            let var_gamma =
                fiat_shamir_gadget::<F, P>(composer, &smaller_sudoku);
            for row in self.sudoku {
                permutation_gadget::<F, P>(composer, row, var_gamma);
            }
            for i in 0..9 {
                let col: Vec<_> =
                    self.sudoku.iter().map(move |row| row[i]).collect();
                let col_to_array: [u8; 9] = col.try_into().unwrap();
                permutation_gadget::<F, P>(composer, col_to_array, var_gamma);
            }
            for i in 0..3 {
                for j in 0..3 {
                    let sub_lines = &self.sudoku[i * 3..(i + 1) * 3];
                    let square: Vec<_> = sub_lines
                        .iter()
                        .map(|line| &line[j * 3..(j + 1) * 3])
                        .collect();
                    let perm: [u8; 9] =
                        square.concat()[0..9].try_into().unwrap();
                    permutation_gadget::<F, P>(composer, perm, var_gamma);
                }
            }
            Ok(())
        }

        fn padded_circuit_size(&self) -> usize {
            1 << 11
        }
    }

    let mut circuit = SudokuCircuit::<Fr, JubjubParameters>::default();

    // Generate CRS
    type PC = SonicKZG10<Bls12_381, DensePolynomial<Fr>>;
    let time = Instant::now();
    let pp =
        PC::setup(1 << 11, None, &mut OsRng).map_err(to_pc_error::<Fr, PC>)?;
    println!("setup: \t\t\t{:?}ms", (Instant::now() - time).as_millis());

    // Compile the circuit
    let time = Instant::now();
    let (pk_p, vk) = circuit.compile::<PC>(&pp)?;
    println!(
        "key generation: \t{:?}ms",
        (Instant::now() - time).as_millis()
    );

    // Prover POV
    let time = Instant::now();
    let (proof, pi) = {
        let mut circuit: SudokuCircuit<Fr, JubjubParameters> = SudokuCircuit {
            sudoku: [[ 7, 6, 0,   5, 3, 8,   1, 2, 4],
                     [ 2, 4, 3,   7, 1, 0,   6, 5, 8],
                     [ 8, 5, 1,   4, 6, 2,   0, 7, 3],

                     [ 4, 8, 6,   0, 7, 5,   3, 1, 2],
                     [ 5, 3, 7,   6, 2, 1,   4, 8, 0],
                     [ 1, 0, 2,   8, 4, 3,   7, 6, 5],

                     [ 6, 1, 8,   3, 5, 4,   2, 0, 7],
                     [ 0, 7, 4,   2, 8, 6,   5, 3, 1],
                     [ 3, 2, 5,   1, 0, 7,   8, 4, 6]],
            _marker1: PhantomData::<Fr>,
            _marker2: PhantomData::<JubjubParameters>,
        };
        circuit.gen_proof::<PC>(&pp, pk_p, b"Test")
    }?;
    println!("proof: \t\t\t{:?}ms", (Instant::now() - time).as_millis());

    // Verifier POV
    let time = Instant::now();
    let verifier_data = VerifierData::new(vk, pi);
    let res = verify_proof::<Fr, JubjubParameters, PC>(
        &pp,
        verifier_data.key,
        &proof,
        &verifier_data.pi,
        b"Test",
    );
    println!("verification: \t\t{:?}ms",
             (Instant::now() - time).as_millis());
    res
}
