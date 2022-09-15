use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{floor_planner, AssignedCell, Layouter, Value},
    plonk::{self, Advice, Column, Instance as InstanceColumn, SingleVerifier},
    transcript::{Blake2bRead, Blake2bWrite},
};
use pasta_curves::{pallas, vesta, Fp};
use rand::RngCore;

use crate::circuit::gadget::{
    add_chip::{self, AddChip, AddConfig},
    assign_free_advice, AddInstruction,
};

#[derive(Clone, Debug)]
pub struct SudokuConfig {
    primary: Column<InstanceColumn>,
    advices: [Column<Advice>; 5],
    add_config: AddConfig,
}

impl SudokuConfig {
    pub(super) fn add_chip(&self) -> add_chip::AddChip {
        add_chip::AddChip::construct(self.add_config.clone())
    }
}

#[derive(Clone, Debug, Default)]
pub struct Circuit {
    pub sudoku: [[u8; 9]; 9],
}

impl plonk::Circuit<pallas::Base> for Circuit {
    type Config = SudokuConfig;
    type FloorPlanner = floor_planner::V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut plonk::ConstraintSystem<pallas::Base>) -> Self::Config {
        let advices = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        // Addition of two field elements.
        let add_config = AddChip::configure(meta, advices[1], advices[2], advices[0]);

        // Instance column used for public inputs
        let primary = meta.instance_column();
        meta.enable_equality(primary);

        // Permutation over all advice columns.
        for advice in advices.iter() {
            meta.enable_equality(*advice);
        }

        // // Poseidon requires four advice columns, while ECC incomplete addition requires
        // // six, so we could choose to configure them in parallel. However, we only use a
        // // single Poseidon invocation, and we have the rows to accommodate it serially.
        // // Instead, we reduce the proof size by sharing fixed columns between the ECC and
        // // Poseidon chips.
        let lagrange_coeffs = [meta.fixed_column()];

        // Also use the first Lagrange coefficient column for loading global constants.
        // It's free real estate :)
        meta.enable_constant(lagrange_coeffs[0]);

        SudokuConfig {
            primary,
            advices,
            add_config,
        }
    }

    #[allow(non_snake_case)]
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<pallas::Base>,
    ) -> Result<(), plonk::Error> {
        let vars: Vec<Vec<AssignedCell<_, _>>> = self
            .sudoku
            .iter()
            .map(|line| {
                let u: Vec<AssignedCell<_, _>> = line
                    .iter()
                    .map(|x| {
                        assign_free_advice(
                            layouter.namespace(|| "sudoku_cell"),
                            config.advices[0],
                            Value::known(pallas::Base::from_u128(*x as u128)),
                        )
                        .unwrap()
                    })
                    .collect();
                u
            })
            .collect();

        let mut cpt = 0;
        for i in 0..9 {
            let mut line = assign_free_advice(
                layouter.namespace(|| "lhs init"),
                config.advices[0],
                Value::known(Fp::zero()),
            )
            .unwrap();
            let mut col = assign_free_advice(
                layouter.namespace(|| "lhs init"),
                config.advices[0],
                Value::known(Fp::zero()),
            )
            .unwrap();
            let mut sub = assign_free_advice(
                layouter.namespace(|| "lhs init"),
                config.advices[0],
                Value::known(Fp::zero()),
            )
            .unwrap();

            for j in 0..9 {
                line = AddInstruction::add(
                    &config.add_chip(),
                    layouter.namespace(|| "line + vars[i][j]"),
                    &line,
                    &vars[i][j],
                )
                .unwrap();
                col = AddInstruction::add(
                    &config.add_chip(),
                    layouter.namespace(|| "col + vars[j][i]"),
                    &col,
                    &vars[j][i],
                )
                .unwrap();
                sub = AddInstruction::add(
                    &config.add_chip(),
                    layouter.namespace(|| "sub + vars[((i / 3) * 3) + j / 3][i % 3 * 3 + j % 3]"),
                    &sub,
                    &vars[((i / 3) * 3) + j / 3][i % 3 * 3 + j % 3],
                )
                .unwrap();
            }

            layouter
                .constrain_instance(line.cell(), config.primary, cpt)
                .unwrap();
            cpt += 1;
            layouter
                .constrain_instance(col.cell(), config.primary, cpt)
                .unwrap();
            cpt += 1;
            layouter
                .constrain_instance(sub.cell(), config.primary, cpt)
                .unwrap();
            cpt += 1;
        }

        Ok(())
    }
}

pub const K: u32 = 9;

#[derive(Debug)]
pub struct VerifyingKey {
    pub(crate) params: halo2_proofs::poly::commitment::Params<vesta::Affine>,
    pub(crate) vk: plonk::VerifyingKey<vesta::Affine>,
}

impl VerifyingKey {
    /// Builds the verifying key.
    pub fn build() -> Self {
        let params = halo2_proofs::poly::commitment::Params::new(K);
        let circuit: Circuit = Default::default();

        let vk = plonk::keygen_vk(&params, &circuit).unwrap();

        VerifyingKey { params, vk }
    }
}

#[derive(Debug)]
pub struct ProvingKey {
    params: halo2_proofs::poly::commitment::Params<vesta::Affine>,
    pk: plonk::ProvingKey<vesta::Affine>,
}

impl ProvingKey {
    /// Builds the proving key.
    pub fn build() -> Self {
        let params = halo2_proofs::poly::commitment::Params::new(K);
        let circuit: Circuit = Default::default();

        let vk = plonk::keygen_vk(&params, &circuit).unwrap();
        let pk = plonk::keygen_pk(&params, vk, &circuit).unwrap();

        ProvingKey { params, pk }
    }
}

#[derive(Clone)]
pub struct Proof(Vec<u8>);

impl Proof {
    /// Creates a proof for the given circuits and instances.
    pub fn create(
        pk: &ProvingKey,
        circuit: Circuit,
        instance: &[&[pallas::Base]],
        mut rng: impl RngCore,
    ) -> Result<Self, plonk::Error> {
        let mut transcript = Blake2bWrite::<_, vesta::Affine, _>::init(vec![]);
        plonk::create_proof(
            &pk.params,
            &pk.pk,
            &[circuit],
            &[instance],
            &mut rng,
            &mut transcript,
        )?;
        Ok(Proof(transcript.finalize()))
    }

    /// Verifies this proof with the given instances.
    pub fn verify(
        &self,
        vk: &VerifyingKey,
        instance: &[&[pallas::Base]],
    ) -> Result<(), plonk::Error> {
        let strategy = SingleVerifier::new(&vk.params);
        let mut transcript = Blake2bRead::init(&self.0[..]);
        plonk::verify_proof(&vk.params, &vk.vk, strategy, &[instance], &mut transcript)
    }

    /// Constructs a new Proof value.
    pub fn new(bytes: Vec<u8>) -> Self {
        Proof(bytes)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use halo2_proofs::{arithmetic::FieldExt, dev::MockProver};
    use pasta_curves::pallas;
    use rand::rngs::OsRng;

    use crate::sudoku::{Proof, ProvingKey, VerifyingKey, K};

    use super::Circuit;

    #[test]
    fn test_sudoku() {
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
        assert_eq!(
            MockProver::run(K, &circuit, vec![public_input.to_vec()])
                .unwrap()
                .verify(),
            Ok(())
        );

        let time = Instant::now();
        let vk = VerifyingKey::build();
        let pk = ProvingKey::build();
        println!(
            "key generation: \t{:?}ms",
            (Instant::now() - time).as_millis()
        );

        let mut rng = OsRng;
        let time = Instant::now();
        let proof = Proof::create(&pk, circuit, &[public_input], &mut rng).unwrap();
        println!("proof: \t\t\t{:?}ms", (Instant::now() - time).as_millis());

        let time = Instant::now();
        assert!(proof.verify(&vk, &[public_input]).is_ok());
        println!(
            "verification: \t\t{:?}ms",
            (Instant::now() - time).as_millis()
        );
    }
}
