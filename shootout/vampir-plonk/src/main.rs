use vampir_plonk;
use zero_knowledge::ZeroKnowledge;

pub fn main() {
    let circuit = vampir_plonk::VampIRCircuit {
        path: "sudoku.pir",
        name: "Vamp-IR zk-garage plonk: Sudoku".to_string(),
        m: 9,
    };
    circuit.prove_and_verify();
}
