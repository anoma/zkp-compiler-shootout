# zkp-compiler-shootout
Evaluating &amp; benchmarking ZKP compilation strategies.

## RISC0
We have a RISC0 implementation of a program that verifies that a Sudoku solution is indeed valid.

### How to run it
1. navigate to the `sudoku` folder
2. in your terminal, `cargo run`
3. to view the RISC0 log, `RISC0_LOG=2 cargo run`

### Benchmarks

#### Native
Cloning the [RISC0 official repo](github.com/risc0/risc0) and running `bazelisk run risc0/zkvm/prove/bench:bench` gives a set of quick benchmarks.

#### Criterion
For our sudoku example, we use a rust package called [criterion](https://github.com/bheisler/criterion.rs) for benchmarking. 
1. in the `shootout` folder, run `cargo bench`
2. analysis of the results can be found in `sudoku/target/criterion/report/index.html`.


## Alucard/VAMP-IR
Please see the offical [Alucard repository](https://github.com/anoma/juvix-circuits).

## Geb

See the [Geb repository](https://github.com/anoma/geb).
