pub fn blake2s() -> cairo_giza::CairoGiza {
    cairo_giza::CairoGiza {
        name: "Cairo-Giza: Blake2s".to_string(),
        program: "cairo-giza/blake2s/blake.json".to_string(),
        memory: "cairo-giza/blake2s/memory.bin".to_string(),
        trace: "cairo-giza/blake2s/trace.bin".to_string(),
    }
}