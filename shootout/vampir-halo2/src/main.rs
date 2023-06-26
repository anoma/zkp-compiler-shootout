use vampir_halo2;
use zero_knowledge::ZeroKnowledge;

pub fn main() {
    let circuit = vampir_halo2::VampIRCircuit {
        path: "sudoku.pir",
        name: "Vamp-IR halo2: Sudoku".to_string(),
    };
    circuit.prove_and_verify();
}
