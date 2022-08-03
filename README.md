# zkp-compiler-shootout
Evaluating &amp; benchmarking ZKP compilation strategies.

## RISC0
We have a RISC0 implementation of a program that verifies that a Sudoku solution is indeed valid.

### How to run it
1. navigate to the `sudoku` folder
2. in your terminal, `cargo run`
3. to view the RISC0 log, `RISC0_LOG=2 cargo run`

### Benchmarks
Cloning the [RISC0 official repo](github.com/risc0/risc0) and running `bazelisk run risc0/zkvm/prove/bench:bench` gives a set of quick benchmarks.

We will provide better benchmarking tools for our Sudoku program in due course.

## Alucard/VAMP-IR
todo
