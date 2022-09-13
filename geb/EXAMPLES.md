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

```shell
Executable.Test.Main> :t SubstMorph
LanguageDef.PolyCat.SubstMorph : SubstObjMu -> SubstObjMu -> Type
Executable.Test.Main>
```

The main declarations in this tutorial are in
[PolyCat.idr](src/LanguageDef/PolyCat.idr),
and the tests are in the corresponding test file
[PolyCatTest.idr](src/LanguageDef/Test/PolyCatTest.idr),
so you'll need to import and load those to follow along:

```shell
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
change.  The "BNC" stands for "bounded nat(-ural number)
category".)

### The category `SubstObjMu`/`SubstMorph`

We'll explore the `Subst` category first.

#### Objects

The objects are the terms of the type `SubstObjMu`, which
is the initial algebra of an endofunctor in Idris's `Type`:

```haskell
public export
data SubstObjF : Type -> Type where
  -- Initial
  SO0 : SubstObjF carrier

  -- Terminal
  SO1 : SubstObjF carrier

  -- Coproduct
  (!!+) : carrier -> carrier -> SubstObjF carrier

  -- Product
  (!!*) : carrier -> carrier -> SubstObjF carrier
```

```haskell
data SubstObjMu : Type where
  InSO : SubstObjF SubstObjMu -> SubstObjM
```

There are aliases for `InSO` applied to each constructor:
`Subst0`, `Subst1`, `!+`, `!*`.

These objects are category theory's way of extracting what is general
among the types commonly available in functional (and other) programming
languages:

- `Subst0`, the initial object, is analogous to `Void`
- `Subst1`, the terminal object, is analogous to `Unit`
- `!+`, which produces the coproduct of two objects, is analogous
to a sum type or ADT
- `!*`, which produces the product of two objects, is analogous to
a record type or tuple

Because this category compiles to polynomial circuits, which have no
recursion and thus can perform only a number of operations with a
precomputable bound, all of these types are finite (from a type-system
perspective, they have finite numbers of terms; the categorial view is
that all of the hom-sets -- the sets of functions between each pair of
types -- are finite).

We can examine some predefined types, and make our own.  `Bool`
is isomorphic to `Either Unit Unit`, so here's how we represent it:

```shell
LanguageDef.Test.PolyCatTest> SubstBool
InSO (InSO SO1 !!+ InSO SO1)
```

Bounded unary natural numbers are
`Either Unit (Either Unit (Either Unit ... (Either Unit Unit)))`:

```shell
LanguageDef.Test.PolyCatTest> SUNat 0
InSO SO0
LanguageDef.Test.PolyCatTest> SUNat 1
InSO SO1
LanguageDef.Test.PolyCatTest> SUNat 2
InSO (InSO SO1 !!+ InSO SO1)
LanguageDef.Test.PolyCatTest> SUNat 5
InSO (InSO SO1 !!+ InSO (InSO SO1 !!+ InSO (InSO SO1 !!+ InSO (InSO SO1 !!+ InSO SO1))))
LanguageDef.Test.PolyCatTest>
```

N-bit binary natural numbers are `N` products of `Bool`:

```shell
LanguageDef.Test.PolyCatTest> SBNat 0
InSO SO1
LanguageDef.Test.PolyCatTest> SBNat 1
InSO (InSO SO1 !!+ InSO SO1)
LanguageDef.Test.PolyCatTest> SBNat 2
InSO (InSO (InSO SO1 !!+ InSO SO1) !!* InSO (InSO SO1 !!+ InSO SO1))
LanguageDef.Test.PolyCatTest> SBNat 5
InSO (InSO (InSO SO1 !!+ InSO SO1) !!* InSO (InSO (InSO SO1 !!+ InSO SO1) !!* InSO (InSO (InSO SO1 !!+ InSO SO1) !!* InSO (InSO (InSO SO1 !!+ InSO SO1) !!* InSO (InSO SO1 !!+ InSO SO1)))))
```

You can define your own in the REPL (as well as in source files for
compiled tests, of course):

```shell
LanguageDef.Test.PolyCatTest> :let SmallLeaf : SubstObjMu
LanguageDef.Test.PolyCatTest> SmallLeaf = SubstBool
LanguageDef.Test.PolyCatTest> :let SmallTree2 = SmallLeaf !* SmallLeaf
LanguageDef.Test.PolyCatTest> :let SmallTree4 = SmallTree2 !* SmallTree2
LanguageDef.Test.PolyCatTest> :let SmallTree16 = SmallTree4 !* SmallTree4
```

We can compute the cardinality of `SmallTree16`:

```shell
LanguageDef.Test.PolyCatTest> substObjCard SmallTree16
substObjFold Nat SOCardAlg (\p' => substObjFold Nat SOCardAlg (\q' => substObjFold Nat SOCardAlg (\p' =>
substObjFold Nat SOCardAlg (\q' => substObjFold Nat SOCardAlg (\p' => substObjFold Nat SOCardAlg (\q' =>
substObjFold Nat SOCardAlg (\p' => substObjFold Nat SOCardAlg (\q' =>
mult (mult (mult p' q') (mult p' q')) (mult (mult p' q') (mult p' q'))) SmallLeaf) SmallLeaf) SmallLeaf) SmallLeaf) SmallLeaf) SmallLeaf) SmallLeaf) SmallLeaf
```

Unfortunately, the Idris-2 REPL appears to me to have some severe
limitations:  it won't reduce the above expression, for example, even
though it's just a `Nat`.  I've tried playing with evaluation options,
but haven't found any which induces this reduction, or even allows
me to check that the result is what I expect.  I've only been able
to do so by editing a file and compiling it (the REPL does at least
offer interactive editing, but it's not obvious to me that it would
be any faster than, or even as fast as, editing the file in an IDE or
editor and then reloading).

There are several convenience functions for defining types, such as:

```haskell
infix 10 !:*
public export
(!:*) : Nat -> SubstObjMu -> SubstObjMu
n !:* p = foldrNatNoUnit ((!+) p) Subst0 p n

infix 10 !*^
public export
(!*^) : SubstObjMu -> Nat -> SubstObjMu
p !*^ n = foldrNatNoUnit ((!*) p) Subst1 p

public export
SOCoproductN : {n : Nat} -> Vect n SubstObjMu -> SubstObjMu
SOCoproductN [] = Subst0
SOCoproductN [x] = x
SOCoproductN (x :: xs@(_ :: _)) = x !+ SOCoproductN x

public export
SOProductN : {n : Nat} -> Vect n SubstObjMu -> SubstObjMu
SOProductN [] = Subst1
SOProductN [x] = x
SOProductN (x :: xs@(_ :: _)) = x !* SOProductN x

public export
SubstBool : SubstObjMu
SubstBool = Subst1 !+ Subst

public export
SMaybe : SubstObjMu -> SubstObjMu
SMaybe x = Subst1 !+ x

-- Unary natural numbers less than the input.
public export
SUNat : Nat -> SubstObjMu
SUNat Z = Subst0
SUNat (S Z) = Subst1
SUNat (S (S n)) = SMaybe $ SUNat (S n)

-- `n`-bit natural numbers.
public export
SBNat : Nat -> SubstObjMu
SBNat Z = Subst1
SBNat (S Z) = SubstBool
SBNat (S (S n)) = SubstBool !* SBNat (S n)

public export
SList : Nat -> SubstObjMu -> SubstObjMu
SList Z x = Subst1
SList (S n) x = SBList n x !+ (x !*^ S n)

public export
SBinTree : Nat -> SubstObjMu -> SubstObjMu
SBinTree Z x = Subst0
SBinTree (S n) x = SMaybe (x !* SBinTree n x !* SBinTree n x)
```

All of the "recursive" types are depth-indexed, since only finite
types exist in the polynomial-circuit category.

#### Morphisms

The morphisms are terms of the type `SubstMorph`:

```haskell
data SubstMorph : SubstObjMu -> SubstObjMu -> Type where
  SMId : (x : SubstObjMu) -> SubstMorph x x
  (<!) : {x, y, z : SubstObjMu} ->
    SubstMorph y z -> SubstMorph x y -> SubstMorph x z
  SMFromInit : (x : SubstObjMu) -> SubstMorph Subst0 x
  SMToTerminal : (x : SubstObjMu) -> SubstMorph x Subst1
  SMInjLeft : (x, y : SubstObjMu) -> SubstMorph x (x !+ y)
  SMInjRight : (x, y : SubstObjMu) -> SubstMorph y (x !+ y)
  SMCase : {x, y, z : SubstObjMu} ->
    SubstMorph x z -> SubstMorph y z -> SubstMorph (x !+ y) z
  SMPair : {x, y, z : SubstObjMu} ->
    SubstMorph x y -> SubstMorph x z -> SubstMorph x (y !* z)
  SMProjLeft : (x, y : SubstObjMu) -> SubstMorph (x !* y) x
  SMProjRight : (x, y : SubstObjMu) -> SubstMorph (x !* y) y
  SMDistrib : (x, y, z : SubstObjMu) ->
    SubstMorph (x !* (y !+ z)) ((x !* y) !+ (x !* z)
```
