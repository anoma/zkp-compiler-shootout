# RISC Zero Rust Starter

The `risc0-rust-starter` repository is a minimal starting project for zero-knowledge software development. In this RISC Zero "Hello World" project, we use zero-knowledge proof techniques to prove that we know the factors of some composite number `N`, without revealing what the factors are. 

For more information, check out the [risc0/risc0 repository](https://www.github.com/risc0/risc0) and the [RISC Zero website](https://www.RISCZero.com).

# Quick Start

First, make sure [rustup](https://rustup.rs) is installed. This project uses a [nightly](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html) version of [Rust](https://doc.rust-lang.org/book/ch01-01-installation.html), `rustup` will automatically install the correct version.

To build all methods and execute the method within the zkVM, run the following command:

```
cargo run --release
```

## Zero-Knowledge Programs

A zkVM program is composed of a `host` and a `guest`. The [host](starter/src/main.rs) code runs like any other rust program and launches a zkVM instance using the [Prover](https://docs.rs/risc0-zkvm-host/0.10.0/risc0_zkvm_host/struct.Prover.html) interface. The [guest](methods/guest/src/bin/multiply.rs) code is compiled for `riscv32im` and runs inside a zkVM. Guest code does not have access to `std` since the zkVM is similar to an embedded system. Use the [env](https://docs.rs/risc0-zkvm-guest/0.10.0/risc0_zkvm_guest/env/index.html) in your zkVM guest code to communicate with the host.

## Contributor's Guide
We welcome contributions to documentation and code via [PRs and GitHub Issues](http://www.github.com/risc0).

## Questions, Feedback, and Collaborations
We'd love to hear from you on [Discord](https://discord.gg/risczero) or [Twitter](https://twitter.com/risczero).
