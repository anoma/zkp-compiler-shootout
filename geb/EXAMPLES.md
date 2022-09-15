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

To run the non-interactive tests, after building (just `make` in
the `geb` directory will suffice), you can run:

```shell
./build/exec/geb
```

This will spout a bunch of what will probably look like random
gibberish unless you've read the code.  (The build itself will also
have checked various compile-time assertions).  You can add your own
non-interactive tests by adding to the `*Test` functions with
`IO ()` signatures in the `*Test.idr` files, such as `polyCatTest`
in `LanguageDef/Test/PolyCatTest.idr`, and you can add compile-time
assertions in the `*Test` files by using the `Assertion` type and
`Assert` function from the `Test.TestLibrary` module.

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

#### Subst Objects

The objects are the terms of the type `SubstObjMu`, which
is the initial algebra of an endofunctor in Idris's `Type`:

```haskell
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
(!:*) : Nat -> SubstObjMu -> SubstObjMu
n !:* p = foldrNatNoUnit ((!+) p) Subst0 p n

infix 10 !*^
(!*^) : SubstObjMu -> Nat -> SubstObjMu
p !*^ n = foldrNatNoUnit ((!*) p) Subst1 p

SOCoproductN : {n : Nat} -> Vect n SubstObjMu -> SubstObjMu
SOCoproductN [] = Subst0
SOCoproductN [x] = x
SOCoproductN (x :: xs@(_ :: _)) = x !+ SOCoproductN x

SOProductN : {n : Nat} -> Vect n SubstObjMu -> SubstObjMu
SOProductN [] = Subst1
SOProductN [x] = x
SOProductN (x :: xs@(_ :: _)) = x !* SOProductN x

SubstBool : SubstObjMu
SubstBool = Subst1 !+ Subst

SMaybe : SubstObjMu -> SubstObjMu
SMaybe x = Subst1 !+ x

-- Unary natural numbers less than the input.
SUNat : Nat -> SubstObjMu
SUNat Z = Subst0
SUNat (S Z) = Subst1
SUNat (S (S n)) = SMaybe $ SUNat (S n)

-- `n`-bit natural numbers.
SBNat : Nat -> SubstObjMu
SBNat Z = Subst1
SBNat (S Z) = SubstBool
SBNat (S (S n)) = SubstBool !* SBNat (S n)

SList : Nat -> SubstObjMu -> SubstObjMu
SList Z x = Subst1
SList (S n) x = SList n x !+ (x !* SList n x)

SBinTree : Nat -> SubstObjMu -> SubstObjMu
SBinTree Z x = Subst0
SBinTree (S n) x = SMaybe (x !* SBinTree n x !* SBinTree n x)

SSExp : Nat -> SubstObjMu -> SubstObjMu
SSExp Z x = Subst0
SSExp (S Z) x = x -- atom
SSExp (S (S n)) x = SSExp (S n) x !+ (SSExp (S n) x !* (SSExp (S n) x))
```

All of the "recursive" types are depth-indexed, since only finite
types exist in the polynomial-circuit category.

#### Subst Morphisms

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
    SubstMorph (x !* (y !+ z)) ((x !* y) !+ (x !* z))
```

In this particular category, the morphisms correspond to
functions between ADTs, and the objects may be viewed as
having "terms" which are morphisms from the terminal object
(`Subst1`), which correspond to the functional-language
notion of terms of a type (neither of those statements is
true in all categories):

- `SMId` corresponds to the identity function
- `SMFromInit` corresponds to `absurd`
- `SMToTerminal` corresponds to `const ()`
- `SMInjLeft` and `SMInjRight` correspond to constructor applications
or `Either` introduction (`Left`, `Right`)
- `SMCase` corresponds to pattern-matching
- `SMPair` corresponds to `Pair` or record construction (`,`)
- `SMProjLeft` and `SMProjRight` correspond to `fst` and
`snd` or to accessing fields of records

`SMDistrib` is special; it expresses that products distribute
over coproducts up to isomorphism, analogously to how
multiplication distributes over addition:

`x !* (y !+ z) === (x !* y) !+ (x !* z)`

It could be viewed as a compiler transformation which expands
a datatype of the form on the left into one of the form on the
right (or as a programmer-defined pattern-match which does the
same thing). In category theory, this is referred to as the
category being "distributive".

Because all of the morphisms except `SMDistrib` are universal
morphisms in category theory, and because the category is
defined as containing _only_ the morphisms which are generated
by the requirement that all such morphisms exist, we may
view `SubstObjMu/SubstMorph` as the _minimal_ category with
an initial object, a terminal object, all coproducts, all
products, and distributivity.  More concisely, it is the minimal
distributive finite bicartesian category.

This, by the way, encapsulates the notion that a morphism
from the terminal object to a given object may be viewed as
a term of the type which that object represents:

```haskell
SOTerm : SubstObjMu -> Type
SOTerm = SubstMorph Subst1
```

There are a number of convenience functions for defining
morphisms, such as:

```haskell
-- The inverse of SMDistrib.
soGather : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !* y) !+ (x !* z)) (x !* (y !+ z))

soSwap : (x, y : SubstObjMu) -> SubstMorph (x !* y) (y !* x)

soConstruct : {n : Nat} -> {x : SubstObjMu} -> {v : Vect n SubstObjMu} ->
  (m : Nat) -> {auto ok : IsYesTrue (isLT m n)} ->
  SubstMorph x (indexNL m {ok} v) -> SubstMorph x (SOCoproductN v)

SOMorphN : {n : Nat} -> SubstObjMu -> Vect n SubstObjMu -> Vect n Type
SOMorphN x v = map (SubstMorph x) v

SOMorphHV : {n : Nat} -> SubstObjMu -> Vect n SubstObjMu -> Type
SOMorphHV {n} x v = HVect (SOMorphN x v)

soTuple : {n : Nat} -> {x : SubstObjMu} -> {v : Vect n SubstObjMu} ->
  SOMorphHV {n} x v -> SubstMorph x (SOProductN v)

SFalse : SOTerm SubstBool

STrue : SOTerm SubstBool

SNot : SubstMorph SubstBool SubstBool

SHigherAnd : SubstMorph SubstBool (SubstBool !-> SubstBool)

SHigherOr : SubstMorph SubstBool (SubstBool !-> SubstBool)

SAnd : SubstMorph (SubstBool !* SubstBool) SubstBool

SOr : SubstMorph (SubstBool !* SubstBool) SubstBool

SIfElse : {x : SubstObjMu} ->
  SOTerm SubstBool -> SOTerm x -> SOTerm x -> SOTerm x

SHigherIfElse : {x, y : SubstObjMu} ->
  SubstMorph x SubstBool -> SubstMorph x y -> SubstMorph x y -> SubstMorph x y

SEqual : (x : SubstObjMu) -> SubstMorph (x !* x) SubstBool

SEqualF : {x, y : SubstObjMu} -> (f, g : SubstMorph x y) ->
  SubstMorph x SubstBool

SIfEqual : {x, y, z : SubstObjMu} ->
  (test, test' : SubstMorph x y) -> (ftrue, ffalse : SubstMorph x z) ->
  SubstMorph x z

MkSUNat : {m : Nat} -> (n : Nat) -> {x : SubstObjMu} ->
  {auto lt : IsYesTrue (isLT n m)} ->
  SubstMorph x (SUNat m)

suPromote : {n : Nat} -> SubstMorph (SUNat n) (SUNat (S n))

suPromoteN : {m, n : Nat} -> {auto ok : LTE m n} ->
  SubstMorph (SUNat m) (SUNat n)

-- Catamorphism on unary natural numbers.
suNatCata : (n : Nat) -> (x : SubstObjMu) ->
  SubstMorph ((Subst1 !+ x) !-> x) (SUNat (S n) !-> x)

suZ : {n : Nat} -> {x : SubstObjMu} -> SubstMorph x (SUNat (S n))

suSucc : {n : Nat} -> SubstMorph (SUNat n) (SUNat (S n))

-- Successor, which returns `Nothing` (`Left`) if the input is the
-- maximum value of `SUNat n`.
suSuccMax : {n : Nat} -> SubstMorph (SUNat n) (SMaybe (SUNat n))

-- Successor modulo `n`.
suSuccMod : {n : Nat} -> SubstMorph (SUNat n) (SUNat n)

su1 : {n : Nat} -> {x : SubstObjMu} -> SubstMorph x (SUNat (S n))

suAdd : {n : Nat} -> SubstMorph (SUNat n !* SUNat n) (SUNat n)

suAddUnrolled : {k : Nat} ->
  SOTerm (SUNat k) -> SubstMorph (SUNat k) (SUNat k)

suMul : {n : Nat} -> SubstMorph (SUNat n !* SUNat n) (SUNat n)

suRaiseTo : {n : Nat} -> SubstMorph (SUNat n !* SUNat n) (SUNat n)

suPow : {n : Nat} -> SubstMorph (SUNat n !* SUNat n) (SUNat n)
suPow = soFlip suRaiseTo

sListNil : {n : Nat} -> {x : SubstObjMu} -> SOTerm (SList n x)

sListPromote : {n : Nat} -> {x : SubstObjMu} ->
  SubstMorph (SList n x) (SList (S n) x)

sListPromoteN : {m, n : Nat} -> {x : SubstObjMu} ->
  {auto ok : LTE m n} -> SubstMorph (SList m x) (SList n x)

sListCons : {n : Nat} -> {x : SubstObjMu} ->
  SubstMorph (x !* SList n x) (SList (S n) x)

sListEvalCons : {n : Nat} -> {x : SubstObjMu} ->
  SOTerm x -> SOTerm (SList n x) -> SOTerm (SList (S n) x)

sListCata : (n : Nat) -> (a, x : SubstObjMu) ->
  SubstMorph ((Subst1 !+ (a !* x)) !-> x) (SList n a !-> x)

sListFoldUnrolled : {k : Nat} -> {a, x : SubstObjMu} ->
  SOTerm x -> SubstMorph (a !* x) x -> SubstMorph (SList k a) x

public export
sListEvalCata : {n : Nat} -> {a, x : SubstObjMu} ->
  SOTerm x -> SubstMorph (a !* x) x -> SOTerm (SList n a) -> SOTerm x
```

#### Higher-order functions

The core objects and morphisms of the category defined above
translate directly to polynomial-circuit operations -- we
shall see the translation in more detail below, but the
summary is that an object translates to a natural number
equal to its cardinality, and morphisms are translated by
arithmetic modulo those natural numbers, with the initial
object corresponding to zero, the terminal object corresponding
to 1, coproducts corresponding to addition, and products
corresponding to multiplication.  The case statement, which
eliminates coproducts, becomes a less-than test, and the
projections, which eliminate products, become div/mod.

The first enhancement that `SubstObjMu`/`SubstMorph` provides
that polynomial circuits do not offer in such a direct way --
an enhancement upon which many future enhancements can and
will be built, such as internal, homoiconic representations of
functors, natural transformations, equality types, quotient
types, and dependent types -- is higher-order functions.
Although we did not build higher-order functions into the
construction above -- and in a sense we could not, because
the above category is meant to represent a data-structures
view of exactly what polynomial circuits provide -- we can
_implement_ higher-order functions in terms of the objects and
morphisms that we have defined.

That is to say, we can represent functions as data structures.
Or, put another way, we can write Lisp in the minimal finite
bicartesian distributive category (and therefore in polynomial
circuits).  Not all of Lisp, of course, since Lisp has recursion
(furthermore, it's Turing-complete) -- but the finite, non-recursive,
terminating subset of it.  That minimal category therefore has
all exponentials -- it is, not by definition but by proof
(implementation), Cartesian _closed_.

The function _type_, which in category theory is generalized to
the notion of exponential object (or "hom-object"), is computed
in what amounts to a lifting to the type level of a recursive
function which defines exponentiation in terms of multiplication:

```haskell
SubstHomObj : SubstObjMu -> SubstObjMu -> SubstObjMu
-- 0 -> y == 1
SubstHomObj (InSO SO0) _ = Subst1
-- 1 -> y == y
SubstHomObj (InSO SO1) y = y
-- (x + y) -> z == (x -> z) * (y -> z)
SubstHomObj (InSO (x !!+ y)) z = SubstHomObj x z !* SubstHomObj y z
-- (x * y) -> z == x -> y -> z
SubstHomObj (InSO (x !!* y)) z = SubstHomObj x (SubstHomObj y z)
```

There are a couple of operators to provide shorthand notations
for exponential objects:

```haskell
infixr 10 !->
(!->) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!->) = SubstHomObj

infix 10 !^
(!^) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!^) = flip SubstHomObj
```

The categorial universal morphism which accompanies the
exponential object is known as `eval`, and this matches Lisp's
usage, in that its signature is a higher-order function which
takes two parameters, a function of a given type and an argument
of the type of the function's domain, and returns a value of the
type of the function's codomain.  In other words, the `eval`
morphism for a particular exponential object may be viewed as an
interpreter for a particular function type:

```haskell
soEval : (x, y : SubstObjMu) ->
  SubstMorph ((x !-> y) !* x) y
soEval (InSO SO0) y = SMFromInit y <! SMProjRight Subst1 Subst0
soEval (InSO SO1) y = SMProjLeft y Subst1
soEval (InSO (x !!+ y)) z =
  SMCase
    (soEval x z <! soForgetMiddle _ _ _)
    (soEval y z <! soForgetFirst _ _ _)
  <! SMDistrib _ _ _
soEval (InSO (x !!* y)) z =
  let
    eyz = soEval y z
    exhyz = soEval x (SubstHomObj y z)
  in
  eyz <!
    SMPair
      (exhyz <! soForgetRight _ _ _)
      (SMProjRight _ _ <! SMProjRight _ _)
```

This function is nearly all just bookkeeping -- the interesting
part is just figuring out which recursive calls to make, in
particular in the product case:  `soEval` is a higher-order
function, and in the product case, one of the arguments to
one of the recursive calls is not one of the projections of
the product, but is rather a hom-object.  Note also that
distributivity plays a vital role in allowing this function
to be defined (exactly once, in the coproduct case).

We can also define another characteristic notion of functional
programming, currying:

```haskell
soCurry : {x, y, z : SubstObjMu} ->
  SubstMorph (x !* y) z -> SubstMorph x (y !-> z)
soCurry {x} {y=(InSO SO0)} f = SMToTerminal x
soCurry {x} {y=(InSO SO1)} {z} f = f <! SMPair (SMId x) (SMToTerminal x)
soCurry {x} {y=(InSO (y !!+ y'))} {z} f =
  let fg = f <! soGather x y y' in
  SMPair (soCurry $ soLeft fg) (soCurry $ soRight fg)
soCurry {x} {y=(InSO (y !!* y'))} {z} f =
  let
    cxyz = soCurry {x=(x !* y)} {y=y'} {z}
    cxhyz = soCurry {x} {y} {z=(SubstHomObj y' z)}
  in
  cxhyz $ cxyz $ soProdLeftAssoc f
```

As in a typical functional programming language, this allows
us to define higher-order functions in terms of functions with
multiple parameters.

Uncurrying and partial application emerge directly from these
definitions:

```haskell
soUncurry : {x, y, z : SubstObjMu} ->
  SubstMorph x (y !-> z) -> SubstMorph (x !* y) z
soUncurry {x} {y} {z} f =
  soEval y z <! SMPair (f <! SMProjLeft x y) (SMProjRight x y)

soPartialApp : {w, x, y, z : SubstObjMu} ->
  SubstMorph (x !* y) z -> SubstMorph w x -> SubstMorph (w !* y) z
soPartialApp g f = soUncurry $ soCurry g <! f
```

Evaluation and currying also allow for straightforward definitions
of the covariant and contravariant Yoneda embeddings:

```haskell
covarYonedaEmbed : {a, b : SubstObjMu} ->
  SubstMorph b a -> (x : SubstObjMu) -> SubstMorph (a !-> x) (b !-> x)
covarYonedaEmbed {a} {b} f x =
  soCurry (soEval a x <! SMPair (SMProjLeft _ _) (f <! SMProjRight _ _))

contravarYonedaEmbed : {a, b : SubstObjMu} ->
  SubstMorph a b -> (x : SubstObjMu) -> SubstMorph (x !-> a) (x !-> b)
contravarYonedaEmbed {a} {b} f x =
  soCurry (f <! soEval x a)
```

#### Homoiconicity and reflection

As explored in the previous section, the minimal finite
distributive bicartesian category has all exponential
objects:  that is, it can represent its own morphisms,
and evaluate the representations.  This is a foundational
form of homoiconicity and reflection upon which many
others can be built.  It corresponds to a notion which
theorem provers and compilers illustrate:  `Subst`
is the categorial abstraction of the general notion of (finite)
ADTs with functions defined by pattern-matching (substitution),
and theorem provers and compilers implement mathematics and
programming using ADTs.  A proof assistant's representation
of a theorem, or a compiler's representation of a function,
is a data structure.

Some homoiconic and reflective functionality has already
been written, although much more is to come.  Perhaps most
fundamentally, a term of a type (categorially, a morphism
from the terminal object to a given object) which happens
to be a function type (categorially, an object which happens
to be the exponential object of some pair of objects) may
be viewed as a morphism, and vice versa:

```haskell
HomTerm : SubstObjMu -> SubstObjMu -> Type
HomTerm = SOTerm .* SubstHomObj

TermAsMorph : {x, y : SubstObjMu} -> HomTerm x y -> SubstMorph x y
TermAsMorph {x} {y} t = soProd1LeftElim $ soUncurry {x=Subst1} {y=x} {z=y} t

MorphAsTerm : {x, y : SubstObjMu} -> SubstMorph x y -> HomTerm x y
MorphAsTerm {x} {y} f = soCurry {x=Subst1} {y=x} {z=y} $ soProdLeftIntro f
```

Note that this follows immediately once we can implement
currying and uncurrying (the latter in turn is just sugar
on top of `eval`).  For a given morphism `f`, we could view
`MorphAsTerm f` as the "quoted" form of `f`, which we can
evaluate to produce a morphism (which in `Subst` is a function
on ADTs) by using `TermAsMorph`.

`Subst` can also reflect its own morphisms, meaning that it
can define morphisms which construct quoted morphisms from
quoted morphisms, in parallel to the metalanguage definition
of `Subst` itself.  For example, here again is the metalanguage
definition of the unique morphism from the initial object to
any given object:

```haskell
SMFromInit : (x : SubstObjMu) -> SubstMorph Subst0 x
```

Here's a version reflected into `Subst` itself:

```haskell
soReflectedFromInit : (x, y : SubstObjMu) -> SubstMorph x (Subst0 !-> y)
soReflectedFromInit x y = soConst $ SMId Subst1
```

(The additional `x` type parameter just makes it more generic
-- it means that we are producing a constant-valued function from
any object `x` _to_ a quoted morphism from the initial object to
a given object `y`.  If we were to call this function with `x`
being `Subst1`, we would have an exact analogue of the metalanguage
definition.)

Note that the implementation is quite trivial, as are many,
but not all, of the reflected functions -- however, it does
have the sublety that the reflection of the morphism from
the _initial_ object is the identity on the _terminal_ object.
That is because the hom-object for morphisms out of the
initial object is the terminal object rather than the initial
object -- that means it has _one_ term, like the unit type,
with that term being the unique morphism out of the initial
object.  It would be wrong for it to be the initial object,
as that would mean that it had _zero_ terms, like the void
type.

Some of the reflected functions do have more complicated
implementations.  For example, here again is the metalanguage
signature of product introduction (pairing):

```haskell
 SMPair : {x, y, z : SubstObjMu} ->
    SubstMorph x y -> SubstMorph x z -> SubstMorph x (y !* z)
```

And here is the version reflected into `Subst` itself:

```haskell
soReflectedPair : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !-> y) !* (x !-> z)) (x !-> (y !* z))
soReflectedPair (InSO SO0) _ _ = SMToTerminal _
soReflectedPair (InSO SO1) _ _ = SMId _
soReflectedPair (InSO (w !!+ x)) y z =
  let
    wyz = soReflectedPair w y z
    xyz = soReflectedPair x y z
  in
  SMPair
    (wyz <!
      SMPair
        (SMProjLeft _ _ <! SMProjLeft _ _)
        (SMProjLeft _ _ <! SMProjRight _ _))
    (xyz <!
      SMPair
        (SMProjRight _ _ <! SMProjLeft _ _)
        (SMProjRight _ _ <! SMProjRight _ _))
soReflectedPair (InSO (w !!* x)) y z =
  let
    xyz = soReflectedPair x y z
    wxyz = soReflectedPair w (x !-> y) (x !-> z)
  in
  contravarYonedaEmbed xyz w <! wxyz
```

And here again is the metalanguage signature of composition:

```haskell
 (<!) : {x, y, z : SubstObjMu} ->
    SubstMorph y z -> SubstMorph x y -> SubstMorph x z
```

And here is the reflected version:

```haskell
soReflectedCompose : (x, y, z : SubstObjMu) ->
  SubstMorph ((y !-> z) !* (x !-> y)) (x !-> z)
soReflectedCompose (InSO SO0) y z = SMToTerminal _
soReflectedCompose (InSO SO1) y z = soEval y z
soReflectedCompose (InSO (w !!+ x)) y z =
  let
    cwyz = soReflectedCompose w y z
    cxyz = soReflectedCompose x y z
  in
  SMPair
    (cwyz <! SMPair (SMProjLeft _ _) (SMProjLeft _ _ <! SMProjRight _ _))
    (cxyz <! SMPair (SMProjLeft _ _) (SMProjRight _ _ <! SMProjRight _ _))
soReflectedCompose (InSO (w !!* x)) y z =
  soCurry $ soCurry $
    soEval y z <! SMPair
      (SMProjLeft _ _ <! SMProjLeft _ _ <! SMProjLeft _ _)
      (soEval x y <! SMPair
        (soEval w (x !-> y) <! SMPair
          (SMProjRight _ _ <! SMProjLeft _ _ <! SMProjLeft _ _)
          (SMProjRight _ _ <! SMProjLeft _ _))
        (SMProjRight _ _))
```

Some other reflections are implemented as well.  In general,
what these reflected functions allow `Subst` to do is
operate on quoted morphisms to produce other quoted morphisms.
For example, `soReflectedCompose` takes two quoted morphisms
(with compatible signatures) and produces a quoted morphism
equal to their composition (which could then be evaluated).

### The category `Nat`/`BNCPolyM`

This category represents a subset of the functionality of
a polynomial circuit, and in particular of that provided
by VampIR or Alucard.  (If it ever includes any objects or
morphisms which can _not_ be translated straightforwardly
into VampIR/Alucard, that's a bug!)

(The "BNC" stands for "bounded natural-number category",
a name which I suspect won't stick.)

#### BNC Objects (`Nat`)

The objects of the BNC category are simply natural numbers.
Morphisms into an object are functions modulo the corresponding
natural number. Note that Geb will not (unless it has bugs!)
use the modulus, though -- no code that it generates should
ever overflow.  The type signature, therefore, is an assertion
rather than a computation.

#### BNC Morphisms

The morphisms of the BNC category correspond to a subset of
the operations provided by a polynomial circuit -- just that
subset required by the core category of Geb described above,
compiled in the simplest unoptimized way.  It will be extended
in the future to allow various optimizations.

```haskell
data BNCPolyM : Type where
  -- Polynomial operations --

  -- Constant
  (#|) : Nat -> BNCPolyM

  -- Identity
  PI : BNCPolyM

  -- Compose
  (#.) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Add
  (#+) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Multiply
  (#*) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Inverse operations --

  -- Subtract
  (#-) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Divide (division by zero returns zero)
  (#/) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Modulus (modulus by zero returns zero)
  (#%) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Branch operation(s)

  -- Compare with zero: equal takes first branch; not-equal takes second branch
  IfZero : BNCPolyM -> BNCPolyM -> BNCPolyM -> BNCPolyM

  -- If the first argument is strictly less than the second, then
  -- take the first branch (which is the third argument); otherwise,
  -- take the second branch (which is the fourth argument)
  IfLT : BNCPolyM -> BNCPolyM -> BNCPolyM -> BNCPolyM -> BNCPolyM
```

(Unoptimized Geb does not even need both branch operations; either
of `IfZero` or `IfLT` would suffice.  It currently uses `IfLT`
because that yields more natural code, but I've left `IfZero` in
for testing.)

### Compiling `SubstObjMu`/`SubstMorph` to `Nat`/`BNCPolyM`

The translation of the core category of Geb to the category
which represents VampIR/Alucard is straightforward.  The
object translation is just type cardinality:

```haskell
substObjToNat : SubstObjMu -> Nat
substObjToNat = substObjCard
```

The morphism translation is just the aforementioned one
turning `Void`, `Unit`, `Either`, and `Pair` into
0, 1, add, and multiply (together with their inverse
operations for elimination) respectively:

```haskell
substMorphToBNC : {x, y : SubstObjMu} -> SubstMorph x y -> BNCPolyM
substMorphToBNC {y=x} (SMId x) = PI
substMorphToBNC ((<!) {x} {y} {z} g f) = substMorphToBNC g #. substMorphToBNC f
substMorphToBNC {x=Subst0} (SMFromInit y) = #| 0
substMorphToBNC {y=Subst1} (SMToTerminal x) = #| 0
substMorphToBNC (SMInjLeft x y) = PI
substMorphToBNC (SMInjRight x y) = #| (substObjToNat x) #+ PI
substMorphToBNC (SMCase {x} {y} {z} f g) with (substObjToNat x)
  substMorphToBNC (SMCase {x} {y} {z} f g) | cx =
    if cx == 0 then
      substMorphToBNC g
    else
      IfLT PI (#| cx)
        (substMorphToBNC f)
        (substMorphToBNC g #. (PI #- #| cx))
substMorphToBNC (SMPair {x} {y} {z} f g) with (substObjToNat y, substObjToNat z)
  substMorphToBNC (SMPair {x} {y} {z} f g) | (cy, cz) =
    #| cz #* substMorphToBNC f #+ substMorphToBNC g
substMorphToBNC (SMProjLeft x y) with (substObjToNat y)
  substMorphToBNC (SMProjLeft x y) | cy =
    if cy == 0 then
      #| 0
    else
      PI #/ #| cy
substMorphToBNC (SMProjRight x y) with (substObjToNat y)
  substMorphToBNC (SMProjRight x y) | cy =
    if cy == 0 then
      #| 0
    else
      PI #% #| cy
substMorphToBNC {x=(x' !* (y' !+ z'))} {y=((x' !* y') !+ (x' !* z'))}
  (SMDistrib x' y' z') =
    let
      cx = substObjToNat x'
      cy = substObjToNat y'
      cz = substObjToNat z'
    in
    if cy == 0 && cz == 0 then
      #| 0
    else
      let
        yz = cy + cz
        xin = PI #/ #| yz
        yzin = PI #% #| yz
      in
      IfLT yzin (#| cy)
        (#| cy #* xin #+ yzin)
        (#| cz #* xin #+ (yzin #- #| cy) #+ #| (cx * cy))
```

There is a function which interprets a Geb morphism into
a metalanguage function on integers:

```haskell
substMorphToFunc : {a, b : SubstObjMu} -> SubstMorph a b -> Integer -> Integer
substMorphToFunc {a} {b} f =
  metaBNCPolyM (natToInteger $ pred $ substObjToNat b) (substMorphToBNC f)
```

There are also convenience functions for translating between
natural numbers and the terms which they represent (within the
context of a given type):

```haskell
substTermToNat : {a : SubstObjMu} -> SOTerm a -> Nat

natToSubstTerm : (a : SubstObjMu) -> Nat -> Maybe (SOTerm a)

NatToSubstTerm : (a : SubstObjMu) -> (n : Nat) ->
  {auto ok : IsJustTrue (natToSubstTerm a n)} -> SOTerm a
```

And there are convenience functions for Gödel-numbering morphisms:

```haskell
substMorphToGNum : {a, b : SubstObjMu} -> SubstMorph a b -> Nat
substMorphToGNum = substTermToNat . MorphAsTerm

substGNumToMorph : (a, b : SubstObjMu) -> Nat -> Maybe (SubstMorph a b)

SubstGNumToMorph : (a, b : SubstObjMu) -> (n : Nat) ->
  {auto ok : IsJustTrue (substGNumToMorph a b n)} -> SubstMorph a b
```

This Gödel-number is per-type, not across all types -- the latter
would require something more complicated, such as Cantor pairing.
Note that equality on the Gödel numbers of morphisms decides
(pointwise) equality of the morphisms themselves.
