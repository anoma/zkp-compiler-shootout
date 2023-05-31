use halo2_proofs::pasta::{EqAffine, Fp};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::plonk::{ProvingKey, VerifyingKey};

use std::collections::HashMap;
use std::fs;
use std::rc::Rc;

use vamp_ir::error::Error;
use vamp_ir::ast::Module;
use vamp_ir::halo2::synth::{keygen, prover, verifier, Halo2Module, PrimeFieldOps, make_constant};
use vamp_ir::transform::compile;
use vamp_ir::util::{prompt_inputs, Config};

use ff::{PrimeField};

#[derive(Clone)]
pub struct VampIRCircuit {
    pub path: &'static str,
    pub name: String,
}

impl zero_knowledge::ZeroKnowledge for VampIRCircuit {
    type C = (
        Params<EqAffine>,
        Halo2Module<Fp>,
        (ProvingKey<EqAffine>, VerifyingKey<EqAffine>),
    );
    type R = (Vec<u8>, Vec<u8>);

    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        let circuit = vamp_compile(self.clone());
        let params: Params<EqAffine> = Params::new(circuit.k);
        let (pk, vk) = keygen(&circuit, &params).expect("Keygen failed in halo2 benchmark");
        (params, circuit, (pk, vk))
    }

    fn prove(&self, (params, circuit, (pk, _vk)): &mut Self::C) -> Self::R {
        prove(&params, circuit, &pk)
    }

    fn verify(&self, (proof, pi): Self::R, (params, _circuit, (_pk, vk)): &mut Self::C) {
        verify(&proof, &pi, vk, &params).unwrap()
    }
}

pub fn vamp_compile(vamp_circuit: VampIRCircuit) -> Halo2Module<Fp> {
    let unparsed_file = fs::read_to_string(vamp_circuit.path).expect("cannot read file");
    let module = Module::parse(&unparsed_file).unwrap();
    let module_3ac = compile(
        module,
        &PrimeFieldOps::<Fp>::default(),
        &Config { quiet: true },
    );
    let module_rc = Rc::new(module_3ac);
    Halo2Module::<Fp>::new(module_rc)
}

pub fn prove(
    params: &Params<EqAffine>,
    circuit: &mut Halo2Module<Fp>,
    pk: &ProvingKey<EqAffine>,
) -> (Vec<u8>, Vec<u8>) {

    let var_assignments_ints = prompt_inputs(&circuit.module);
    let mut var_assignments = HashMap::new();
    for (k, v) in var_assignments_ints {
        var_assignments.insert(k, make_constant(v));
    }

    // Populate variable definitions
    circuit.populate_variables(var_assignments.clone());

    // Get public inputs Fp
    let binding = circuit.module.pubs
        .iter()
        .map(|inst| var_assignments[&inst.id])
        .collect::<Vec<Fp>>();
    let instances = binding.as_slice();

    // Start proving witnesses
    let proof = prover(circuit.clone(), &params, &pk, instances).expect("prover failed in halo2 benchmark");
    let public_inputs: Vec<u8> = instances
        .iter()
        .flat_map(|fp| {
            let repr = fp.to_repr();
            repr.as_ref().to_vec()
        })
        .collect();
    (proof, public_inputs)
}

pub fn verify(
    proof: &Vec<u8>,
    pi: &Vec<u8>,
    vk: &VerifyingKey<EqAffine>,
    params: &Params<EqAffine>,
) -> Result<(), Error> {

    let instances_vec: Vec<Fp> = pi
        .chunks(32)
        .map(|chunk| {
            let mut array = [0u8; 32];
            array.copy_from_slice(&chunk[..32]);
            Fp::from_repr(array).unwrap()
        })
        .collect();
    let instances: &[Fp] = instances_vec.as_slice();
    let result = verifier(&params, &vk, &proof, instances).map_err(|error| Error::from(error));
    result
}