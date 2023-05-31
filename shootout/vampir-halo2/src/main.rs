use vampir_plonk;
use zero_knowledge::ZeroKnowledge;

pub fn main() {
    let circuit = vampir_plonk::VampIRCircuit {
        path: "sudoku.pir",
        name: "Vamp-IR halo2: Sudoku".to_string(),
    };
    circuit.prove_and_verify();
}
