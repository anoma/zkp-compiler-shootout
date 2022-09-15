//! Sudoku PLONK Example

use ark_bls12_381::{Bls12_381, Fr, FrParameters};
use ark_ec::TEModelParameters;
use ark_ed_on_bls12_381::EdwardsParameters as JubjubParameters;
use ark_ff::{Fp256, PrimeField};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::{kzg10::UniversalParams, sonic_pc::SonicKZG10, PolynomialCommitment};
use plonk::error::to_pc_error;
use plonk::proof_system::pi::PublicInputs;
use plonk_core::circuit::{verify_proof, Circuit};
use plonk_core::constraint_system::StandardComposer;
use plonk_core::error::Error;
use plonk_core::prelude::*;
use rand_core::OsRng;

use std::marker::PhantomData;
use std::time::Instant;

use plonk_core::prelude::Variable;

pub fn field_addition_gadget<F: PrimeField, P: TEModelParameters<BaseField = F>>(
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

////////////////////////////////////////////////////////////////////////////////
// Example Sudoku runner
////////////////////////////////////////////////////////////////////////////////

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

    fn gadget(&mut self, composer: &mut StandardComposer<F, P>) -> Result<(), Error> {
        // new circuit
        let vars: Vec<Vec<Variable>> = self
            .sudoku
            .iter()
            .map(|line| {
                let u: Vec<Variable> = line
                    .iter()
                    .map(|x| {
                        let t = composer.add_input(F::from(*x));
                        t
                    })
                    .collect();
                u
            })
            .collect();

        let var36 = composer.add_input(F::from(0x24 as u32));

        for i in 0..9 {
            let mut line = composer.zero_var();
            let mut col = composer.zero_var();
            let mut sub = composer.zero_var();

            for j in 0..9 {
                line = field_addition_gadget::<F, P>(composer, line, vars[i][j]);
                col = field_addition_gadget::<F, P>(composer, col, vars[j][i]);
                sub = field_addition_gadget::<F, P>(
                    composer,
                    sub,
                    vars[((i / 3) * 3) + j / 3][i % 3 * 3 + j % 3],
                );
            }
            composer.assert_equal(line, var36);
            composer.assert_equal(col, var36);
            composer.assert_equal(sub, var36);
        }
        Ok(())
    }

    fn padded_circuit_size(&self) -> usize {
        1 << 9
    }
}

type PC = SonicKZG10<Bls12_381, DensePolynomial<Fr>>;

type JubSudoku = SudokuCircuit<Fr, JubjubParameters>;

type ProverKey256 = ProverKey<Fp256<FrParameters>>;

type SonicZKG256 = SonicKZG10<Bls12_381, DensePolynomial<Fp256<FrParameters>>>;

type VerifierKey256 = VerifierKey<Fp256<FrParameters>, SonicZKG256>;

type PublicInput256 = PublicInputs<Fp256<FrParameters>>;

pub fn setup() -> Result<UniversalParams<Bls12_381>, Error> {
    PC::setup(1 << 9, None, &mut OsRng).map_err(to_pc_error::<Fr, PC>)
}

pub fn key_generation(
    pp: &UniversalParams<Bls12_381>,
    mut circuit: JubSudoku,
) -> Result<(ProverKey256, VerifierKey256), Error> {
    circuit.compile::<PC>(pp)
}

// Prover POV
pub fn proof(
    pp: &UniversalParams<Bls12_381>,
    pk_p: ProverKey256,
) -> Result<(Proof<Fp256<FrParameters>, SonicZKG256>, PublicInput256), Error> {
    {
        let mut circuit: SudokuCircuit<Fr, JubjubParameters> = SudokuCircuit {
            sudoku: [
                [7, 6, 0, 5, 3, 8, 1, 2, 4],
                [2, 4, 3, 7, 1, 0, 6, 5, 8],
                [8, 5, 1, 4, 6, 2, 0, 7, 3],
                [4, 8, 6, 0, 7, 5, 3, 1, 2],
                [5, 3, 7, 6, 2, 1, 4, 8, 0],
                [1, 0, 2, 8, 4, 3, 7, 6, 5],
                [6, 1, 8, 3, 5, 4, 2, 0, 7],
                [0, 7, 4, 2, 8, 6, 5, 3, 1],
                [3, 2, 5, 1, 0, 7, 8, 4, 6],
            ],
            _marker1: PhantomData::<Fr>,
            _marker2: PhantomData::<JubjubParameters>,
        };
        circuit.gen_proof::<PC>(&pp, pk_p, b"Test")
    }
}

// Verifier POV
pub fn verify(
    vk: VerifierKey256,
    pi: PublicInput256,
    pp: &UniversalParams<Bls12_381>,
    proof: Proof<Fp256<FrParameters>, SonicZKG256>,
) -> Result<(), Error> {
    let verifier_data = VerifierData::new(vk, pi);
    verify_proof::<Fr, JubjubParameters, PC>(
        &pp,
        verifier_data.key,
        &proof,
        &verifier_data.pi,
        b"Test",
    )
}

pub fn circuit() -> JubSudoku {
    SudokuCircuit::<Fr, JubjubParameters>::default()
}

pub fn prove_and_verify() -> Result<(), Error> {
    let time = Instant::now();

    let circuit = circuit();

    println!("circuit: \t\t{:?}ms", (Instant::now() - time).as_millis());

    // Generate CRS
    let time = Instant::now();

    let pp = setup()?;

    println!("setup: \t\t\t{:?}ms", (Instant::now() - time).as_millis());

    // Compile the circuit
    let time = Instant::now();

    let (pk_p, vk) = key_generation(&pp, circuit)?;

    println!(
        "key generation: \t{:?}ms",
        (Instant::now() - time).as_millis()
    );

    // Prover POV
    let time = Instant::now();

    let (proof, pi) = proof(&pp, pk_p)?;

    println!("proof: \t\t\t{:?}ms", (Instant::now() - time).as_millis());

    // Verifier POV
    let time = Instant::now();

    let res = verify(vk, pi, &pp, proof);

    println!(
        "verification: \t\t{:?}ms",
        (Instant::now() - time).as_millis()
    );
    res
}
