# zkp-compiler-shootout
Evaluating &amp; benchmarking ZKP compilation strategies.

Currently we are testing the following Zero Knowledge machines

1. [RISC0](https://github.com/risc0/risc0)
2. [Miden](https://github.com/maticnetwork/miden)
3. [Plonk](https://github.com/ZK-Garage/plonk)
4. [Halo](https://github.com/zcash/halo2)

### How to get benchmark results
1. navigate to the `shoout` folder
2. run `cargo bench`
3. sit back and watch your CPU spin
4. load the HTML file  in `/shootout/target/criterion/report/index.html`

## Alucard/VAMP-IR
Please see the offical [Alucard repository](https://github.com/anoma/juvix-circuits).

## Geb

See the [Geb repository](https://github.com/anoma/geb).
