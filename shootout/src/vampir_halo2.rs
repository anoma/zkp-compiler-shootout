// To do: add SRS here

pub fn blake2s() -> vampir_halo2::VampIRCircuit {
    vampir_halo2::VampIRCircuit {
        path: "vampir-halo2/blake2s.pir",
        name: "Vamp-IR halo2: Blake2s".to_string(),
    }
}

pub fn sudoku() -> vampir_halo2::VampIRCircuit {
    vampir_halo2::VampIRCircuit {
        path: "vampir-halo2/sudoku.pir",
        name: "Vamp-IR halo2: sudoku".to_string(),
    }
}
