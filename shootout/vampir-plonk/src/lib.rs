use plonk_core::prelude::VerifierData;
use plonk_core::proof_system::{ProverKey, VerifierKey, Proof};
use plonk_core::proof_system::pi::PublicInputs;
use plonk_core::error::Error;
use plonk::error::to_pc_error;
use ark_bls12_381::{Bls12_381, Fr as BlsScalar};
use ark_ed_on_bls12_381::EdwardsParameters as JubJubParameters;
use ark_poly_commit::{kzg10::UniversalParams, sonic_pc::SonicKZG10, PolynomialCommitment};
use ark_poly::polynomial::univariate::DensePolynomial;
use plonk_core::circuit::{Circuit, verify_proof};

use std::collections::HashMap;
use std::fs;
use std::rc::Rc;
use rand_core::OsRng;

use vamp_ir::plonk::synth::PlonkModule;
use vamp_ir::ast::Module;
use vamp_ir::transform::compile;
use vamp_ir::plonk::synth::{PrimeFieldOps, make_constant};
use vamp_ir::util::prompt_inputs;

type PC = SonicKZG10<Bls12_381, DensePolynomial<BlsScalar>>;

static NAME: &'static str = "Vamp-IR zk-garage plonk: Blake2s";

#[derive(Clone)]
pub struct Blake2sCircuit<'a> {
    pub path: &'a str,
}

impl zero_knowledge::ZeroKnowledge for Blake2sCircuit <'_>{

    type C = (UniversalParams<Bls12_381>, PlonkModule<BlsScalar, JubJubParameters>,
              (ProverKey::<BlsScalar>, (VerifierKey::<BlsScalar, PC>, Vec<usize>)));
    type R = (Proof<BlsScalar, PC>, PublicInputs<BlsScalar>);

    fn name(&self) -> String { NAME.to_string() }

    fn compile(&self) -> Self::C {
        let pp = setup().unwrap();
        let mut circuit = vamp_compile();
        let (pk_p, (vk_0, vk_1)) = key_gen(&pp, &mut circuit);
        (pp, circuit, (pk_p, (vk_0, vk_1)))
    }

    fn prove(&self, (pp, circuit, (pk_p, (_vk_0, _vk_1))): &mut Self::C) -> Self::R{
        prove(&pp, circuit, (*pk_p).clone())
    }

    fn verify(&self, (proof, pi): Self::R, (pp, _circuit, (_pk_p, (vk_0, _vk_1))): &mut Self::C) {
        verify(&proof, pi, &pp, (*vk_0).clone()).unwrap()
    }
}

pub fn setup() -> Result<UniversalParams<Bls12_381>, Error> {
    Ok(PC::setup(1 << 19, None, &mut OsRng)
        .map_err(to_pc_error::<BlsScalar, PC>)
        .expect("unable to setup polynomial commitment scheme public parameters"))
}

pub fn vamp_compile() -> PlonkModule<BlsScalar, JubJubParameters> {
    let blake2s_circuit = Blake2sCircuit { path: "vampir-plonk/blake2s.pir" };
    let unparsed_file = fs::read_to_string(blake2s_circuit.path).expect("cannot read file");
    let module = Module::parse(&unparsed_file).unwrap();
    let module_3ac = compile(module, &PrimeFieldOps::<BlsScalar>::default());

    let module_rc = Rc::new(module_3ac);
    PlonkModule::<BlsScalar, JubJubParameters>::new(module_rc)
}

pub fn key_gen(
    pp: &UniversalParams<Bls12_381>,
    circuit: &mut PlonkModule::<BlsScalar, JubJubParameters>,
) -> (ProverKey::<BlsScalar>, (VerifierKey::<BlsScalar, PC>, Vec<usize>)) {   circuit.compile::<PC>(&pp).expect("unable to compile circuit") }

pub fn prove(
    pp: &UniversalParams<Bls12_381>,
    circuit: &mut PlonkModule::<BlsScalar, JubJubParameters>,
    pk_p: ProverKey<BlsScalar>,
) ->  (Proof<BlsScalar, PC>, PublicInputs<BlsScalar>) {
    let var_assignments_ints = prompt_inputs(&circuit.module);
    let mut var_assignments = HashMap::new();
    for (k, v) in var_assignments_ints {
        var_assignments.insert(k, make_constant(&v));
    }
    // Populate variable definitions
    circuit.populate_variables(var_assignments);
    // Start proving witnesses
    circuit.gen_proof::<PC>(&pp, pk_p, b"Test").unwrap()
}

pub fn verify(
    proof: &Proof<BlsScalar, PC>,
    pi: PublicInputs<BlsScalar>,
    pp: &UniversalParams<Bls12_381>,
    vk_0: VerifierKey<BlsScalar, PC>,
) -> Result<(), Error> {
    let verifier_data = VerifierData::new(vk_0, pi);
    verify_proof::<BlsScalar, JubJubParameters, PC>(
        &pp,
        verifier_data.key,
        &proof,
        &verifier_data.pi,
        b"Test",
    )
}