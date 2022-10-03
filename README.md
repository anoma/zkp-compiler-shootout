# zkp-compiler-shootout
Evaluating &amp; benchmarking ZKP compilation strategies.

Currently we are testing the following Zero Knowledge machines

1. [RISC0](https://github.com/risc0/risc0)
2. [Miden](https://github.com/maticnetwork/miden)
3. [Plonk](https://github.com/ZK-Garage/plonk)
4. [Halo2](https://github.com/zcash/halo2)

Results can be seen in the [BENCHMARKS.md](./BENCHMARKS.md) file. The
results were collected on a `AMD Ryzen 7 5700X 8-Core @ 16x 3.4GHz`
CPU.

To see very rough notes about the languages in the benchmark and
potential improvement points please read [my notes
file](./shootout/notes.org).
## How to get benchmark results

There are two commands for producing results

1. `make table`
2. `make bench`

It is recommended to run `make table`. However it requires two
external dependencies

1. `cargo-criterion`
2. `criterion-table`

these can both be installed with the following command.

```sh
cargo install cargo-criterion
cargo install criterion-table
```

Make sure cargo packages are on your path.

Either way, the results can be seen

1. run `make table`
   - or `make bench`, if one does not wish to install the cargo packages
2. sit back and watch your CPU spin
3. The HTML results should be in `./shootout/target/criterion/reports/index.html`
4. If `make table` was run, the updated benchmark results should be
   seen in `./BENCHMARKS.md`

## Contributing




## Alucard/VAMP-IR
Please see the offical [Alucard repository](https://github.com/anoma/juvix-circuits).

## Geb

See the [Geb repository](https://github.com/anoma/geb).
