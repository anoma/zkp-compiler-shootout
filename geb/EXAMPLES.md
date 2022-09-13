# Geb by example

## Setup instructions

To follow along, first
[install Idris-2](https://idris2.readthedocs.io/en/latest/tutorial/starting.html), check out and `cd` into the `zkp-compiler-shootout` repository,
then build Geb and launch the
[REPL](https://idris2.readthedocs.io/en/latest/tutorial/interactive.html)
by `cd`-ing to the `geb` directory and running
`rlwrap idris2 --repl geb.ipkg` (or just `idris2 --repl geb.ipkg`, if
you don't have or don't wish to use `rlwrap`).

If everything works, you should see a prompt and should be able to
enter a command that uses Geb code, and get a sensible result.  For
example, you could check the type of `SubstMorph`:

```haskell
Executable.Test.Main> :t SubstMorph
LanguageDef.PolyCat.SubstMorph : SubstObjMu -> SubstObjMu -> Type
Executable.Test.Main>
```

The main declarations in this tutorial are in
[PolyCat.idr](src/LanguageDef/PolyCat.idr),
and the tests are in the corresponding test file
[PolyCatTest.idr](src/LanguageDef/Test/PolyCatTest.idr),
so you'll need to import and load those to follow along:

```haskell
Executable.Test.Main> :module LanguageDef.PolyCat
Imported module LanguageDef.PolyCat
Executable.Test.Main>
Executable.Test.Main> :load "src/LanguageDef/Test/PolyCatTest.idr"
Loaded file src/LanguageDef/Test/PolyCatTest.idr
LanguageDef.Test.PolyCatTest>
```

You can use `:?` at the REPL prompt to get a list of commands.

## Code tour

There are two principal categories explored in this tour:

- The API which Geb presents to Juvix.  This is the category
which compiles (from Juvix) to Geb.  Its objects are
`SubstObjMu` and its morphisms are `SubstMorph`.  (The
"subst" is meant to denote that it supports just enough
operations to perform substitution.)
- The category which models the subset of VampIR which Geb
uses (so far).  This is the category which Geb compiles to.
Its objects are `Nat` and its morphisms are `BNCPolyM`.
(That is probably a terrible name which I will eventually
change.  The "BNC" stands for "bounded nat(-ural numer)
category".)

We'll explore the `Subst` category first.
