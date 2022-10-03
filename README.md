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

This repository serves as a base for contributions and so
contributions should hopefully be easy, and deficiencies on the
implementations well known.

Hopefully the process is rather straight forward, however we give a
guide below to more quickly get familiar with the structure of the
project.


To get a quick `TL;DR` feeling of this you could alternatively read
how the `miden` backend plugs in both in the `miden.rs`, `main.rs`,
`bench.rs`, and the `miden` sub directory for project layout. That
should hopefully be readable enough without having to read the full
guide below.

### Layout Structure: SRC

The project has two components of organization, the `shootout`
directory has an `src` folder that hosts a file per backend. These
files (`miden.rs`, `risc.rs`, etc.) are rather basic, just hosting an
implementation of the given backend `struct` that was created.


```bash
.
├── Cargo.lock
├── Cargo.toml
├── src
│   ├── bench.rs
│   ├── halo.rs
│   ├── main.rs
│   ├── miden.rs
│   ├── plonk.rs
│   └── risc.rs
```

We can see other files as well such as `bench.rs` and `main.rs`

For creating a new backend to test, one will have to touch
[`bench.rs`](shootout/src/bench.rs) to have their new backend be
tested. Since the code added is just a way to get around Rust's lack
of typing of existentials this should be an easy task.

Finally, in [`main.rs`](shootout/src/main.rs) we hook up our tests to
a certain benchmark we care about.

```rust
pub fn bench_sudoku(c: &mut Criterion) {
    let to_bench = vec![
        ZKP::Miden(miden::sudoku()),
        ZKP::Plonk(plonk::sudoku()),
        ZKP::Risc0(risc::sudoku()),
        ZKP::Halo2(halo::sudoku()),
    ];
    bench_zkp(c, String::from("Sudoku"), to_bench)
}
```


As we can see it's just adding the backend's struct to a vector list
and wrapped with the enum found in `bench.rs`.

This structure should also make it easy to add new benchmark programs,
please feel free to add new kinds of programs we wish to test here
with whatever backend you are interested in! Hopefully others,
including myself, can contribute to other backends for your test!

### Layout Structure: sub directories

The layout structures of the other directories are as follows:

```bash
.
├── Cargo.lock
├── Cargo.toml
├── miden
├── notes.org
├── risc
├── sudoku-halo2
├── sudoku-plonk
└── zero-knowledge
    ├── Cargo.toml
    └── src
```

The most important folder is `zero-knowledge` as this has the trait
needed to implement to have the benchmarker work.

```rust
pub trait ZeroKnowledge {
    type C;
    type R;
    fn name(&self) -> String;
    fn compile(&self) -> Self::C;
    fn prove(&self, setup: &Self::C) -> Self::R;
    fn verify(&self, receipt: Self::R, program: &Self::C) -> ();
    fn prove_and_verify(&self) -> () {
        let circuit = self.compile();
        let receipt = self.prove(&circuit);
        self.verify(receipt, &circuit);
    }
}
```

Here for a custom backend one just needs to implement `compile`,
`prove`, `verify`, and a `name`, and your new zero knowledge backend
can be tested!

The other folders like `miden` and `risc`, represent stand alone
backends. Adding a new program to benchmark or improve a current
benchmark should be quite easy.

the `sudoku-halo2` and `sudoku-plonk` are similar, but represent a
single program/project style structure (In the future we will likely
transform these to fit the mold of what `risc` and `miden` have).

Lastly, the `notes.org` file lays out notes about the backends and
deficiencies in any particular implementation, hopefully over time all
the programs will be optimal for their specific backend to have a more
accurate and fair results.

### Project Structure

For adding a new backend or adding new programs for backends like
`halo2` or `plonk`. One may have to create a new sub directory.

this can be done with `cargo new`, or if you already have working
code, just copy and paste your code into the directory! each of the
sub-directories are standalone independent projects with their own
`workspace`. The only new dependency you'll have to add is:

```rust
[dependencies]
zero-knowledge = { path = "../zero-knowledge" }
```

and make sure the top level `Cargo.toml` excludes the project and
brings it in as a dependency.

If you are importing existing code for a new backend, make sure you
implement the `ZeroKnowledge` trait, and you're all set!

We will now talk about backend specific considerations, feel free to
skip these if they aren't a backend you care about contributing to

### Project Structure: Miden

The miden backend can be found in the `miden` sub directory. Really
one does not have to alter this code at all, just add your program to
`src/miden.rs` to mainly fill in the starting advice tape or the
starting stack, along with the file path where the miden program is
stored.

Ι personally keep my miden code in
[miden-assembler](miden-assembler/miden), as Ι generate out miden
code from my Common lisp DSL in
[programs](miden-assembler/src/programs.lisp) sub directory. All one
needs to run this code is
[quick-lisp](https://www.quicklisp.org/beta/) and just write

```lisp
;; if you need to load the file by hand
;; I will assume the repl is in the miden-assembler directory
(load "miden-assembler.asd")
;; load the project
(ql:quickload :miden-assembler)
;; switch to the project
(in-package :miden)
;; dump the code changes
(dump)
```

However you may keep it wherever you feel, just make sure path is
properly given in the `miden.rs` file.

the rest is just hooking up your new program to `main.rs` which should
be straight forward.

### Project Structure: Risc0

Risc0 can compile straight rust code, which is nice, however this
means the structure is a bit different from `miden` or other ZKVMs.

```bash
.
├── Cargo.toml
├── methods
│   ├── build.rs
│   ├── Cargo.toml
│   ├── guest
│   └── src
├── README.md
├── src
│   ├── lib.rs
│   └── main.rs
├── sudoku-core
│   ├── Cargo.toml
│   └── src
└── target
```

the `src` directory contains `lib.rs` which you will only need to
touch the imports from the `methods` directory. the `Risc` struct
should be general enough to handle any program you wish to compile.

```bash
.
├── build.rs
├── Cargo.toml
├── guest
│   ├── build.rs
│   ├── Cargo.lock
│   ├── Cargo.toml
│   ├── src
│   │   └── bin
│   │       ├── fib_fifty.rs
│   │       ├── fib_ninty_two.rs
│   │       ├── fib.rs
│   │       └── sudoku.rs
└── src
    └── lib.rs
```

inside `methods`, you should place your code in the `bin` of
`guest`. As you can see the names of the current programs, these
correspond to the imports in `lib.rs`

```rust
pub use methods_fib::{FIB_ID,           FIB_PATH,
                      FIB_FIFTY_ID,     FIB_FIFTY_PATH,
                      FIB_NINTY_TWO_ID, FIB_NINTY_TWO_PATH,
                      SUDOKU_ID,        SUDOKU_PATH};
```

Note that any dependency you want to be compiled with these should be
placed in the `Cargo.toml` in the guest directory. This includes
shared code like we have for `sudoku-core`, which is linked both to
the `guest` and to the native rust code in `src`.

Much like miden, all that is now required is to make the `Risc` struct
in `shootout/src/risc.rs` for your new program and tell `main.rs` to
benchmark it!

### Project Structure: Stand alone.

Hopefully `miden` shows a good way to create standalone projects. So
if one has existing `halo2` or `plonk` code, one could just copy and
paste it into a directory and implement the `ZeroKnowledge` trait. for
their program.

## Alucard/VAMP-IR
Please see the official [Alucard repository](https://github.com/anoma/juvix-circuits).

## Geb

See the [Geb repository](https://github.com/anoma/geb).
