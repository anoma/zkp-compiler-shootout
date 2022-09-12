# Geb by example

## Setup instructions

To follow along, first
[install Idris-2](https://idris2.readthedocs.io/en/latest/tutorial/starting.html), check out and `cd` into the `zkp-compiler-shootout` repository,
then build Geb and launch the
[REPL](https://idris2.readthedocs.io/en/latest/tutorial/interactive.html)
by `cd`-ing to the `geb` directory and running
`rlwrap idris2 --repl geb.ipkg` (or just `idris2 --repl geb.ipkg`, if
you don't have or don't wish to use `rlmap`).

If everything works, you should see a prompt and should be able to
enter a command that uses Geb code, and get a sensible result.  For
example, you could check the type of `SubstMorph`:

```haskell
Executable.Test.Main> :t SubstMorph
LanguageDef.PolyCat.SubstMorph : SubstObjMu -> SubstObjMu -> Type
Executable.Test.Main>
```

## ...
