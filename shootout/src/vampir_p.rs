// To do: add SRS here

pub fn blake2s() -> vampir_plonk::VampIRCircuit {
    vampir_plonk::VampIRCircuit {
        path: "vampir-plonk/blake2s.pir",
        name: "Vamp-IR zk-garage plonk: Blake2s".to_string(),
        m: 19,
    }
}

pub fn sudoku() -> vampir_plonk::VampIRCircuit {
    vampir_plonk::VampIRCircuit {
        path: "vampir-plonk/sudoku.pir",
        name: "Vamp-IR zk-garage plonk: sudoku".to_string(),
        m: 9,
    }
}
