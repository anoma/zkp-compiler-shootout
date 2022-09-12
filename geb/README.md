# Compiling through categories: Geb as a circuit frontend

Because the core logic of [Geb](https://hackmd.io/wo_tUfBsQR6YsxQobNLRtQ?view)
has a zeroth-order sub-category which coincides precisely with what can be
expressed by polynomial operations and constraints -- finite products,
finite coproducts, and equalizers -- that logic might be used as an IR
for compilation of user programs to circuits.

Geb uses those polynomial category-theoretic constructions to represent
datatypes, so it would present a front end that would look like typical
functional programming (with dependent types -- the zeroth-order category
of Geb is a topos).

This could be done through some sequence of categories such as the following,
in order from back-end to front-end.

## Geb by example

For test sessions illustrating various functions of Geb, see the
[examples page](./EXAMPLES.md).

## The back-end category: a representation of Alucard/VampIR

Represented as a category, the subset of Alucard/VampIR that Geb
needs to compile to would have as its objects possibly-empty
ranges of natural numbers:

```haskell
public export
NatRange : Type
NatRange = (Nat, Nat)

public export
validRange : DecPred NatRange
validRange (m, n) = m <= n

public export
betweenPred : Nat -> Nat -> DecPred Nat
betweenPred min max n = (min <= n) && (n <= max)

-- `Nothing` means an empty range (Void).
public export
AugNatRange : Type
AugNatRange = Maybe NatRange
```

The morphisms include polynomial operations (where coproduct
introduction compiles to addition and product introduction to
multiplication) and a less-than test (for eliminating coproducts)
and div/mod (for projections, i.e. eliminating products):

```haskell
public export
data RangedNatMorphF : Type -> Type where
  RNMComposeF : {0 carrier : Type} ->
    carrier -> carrier -> RangedNatMorphF carrier
  RNMPolyF : {0 carrier : Type} ->
    NatRange -> PolyShape -> RangedNatMorphF carrier
  RNMSwitchF : {0 carrier : Type} ->
    Nat -> carrier -> carrier -> RangedNatMorphF carrier
  RNMDivF : {0 carrier : Type} ->
    NatRange -> Nat -> RangedNatMorphF carrier
  RNMModF : {0 carrier : Type} ->
    NatRange -> Nat -> RangedNatMorphF carrier
  RNMExtendCodBelowF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier
  RNMExtendCodAboveF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier
  RNMRestrictDomBelowF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier
  RNMRestrictDomAboveF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier

-- `Left` means the unique morphism from Void to the given (augmented) range.
public export
AugRNM : Type
AugRNM = Either AugNatRange MuRNM

public export
AugRNMSig : Type
AugRNMSig = (AugNatRange, AugNatRange)
```

(The morphisms above also include "extend-codomain" and "restrict-domain"
operators for relaxing constraints.)

Polynomials themselves could be represented in a normalized
form to decide isomorphism:

```haskell
public export
PolyTerm : Type
PolyTerm = (Nat, Nat)

public export
ptPow : PolyTerm -> Nat
ptPow = fst

public export
ptCoeff : PolyTerm -> Nat
ptCoeff = snd

-- A list of (power, coefficient) pairs.
public export
PolyShape : Type
PolyShape = List PolyTerm

public export
validPT : DecPred (Nat, Nat)
validPT t = ptCoeff t /= 0

-- We define a valid (normalized) polynomial shape as follows:
--   - The shape of the polynomial is a list of pairs of natural numbers,
--     where each list element represents a term (monomial), and the
--     pair represents (power, coefficient)
--   - Entries are sorted by strictly descending power
--   - There are no entries for powers with zero coefficients
-- Consequences of these rules include:
--  - Equality of valid polynomials is equality of underlying shapes
--  - The tail of a valid polynomial is always valid
--  - The meaning of an entry (a term) is independent of which list
--    it appears in, and thus can be determined by looking at the term
--    in isolation
--  - The degree of the polynomial is the left element of the head of the
--    list (or zero if the list is empty)
public export
validPoly : DecPred PolyShape
validPoly (t :: ts@(t' :: _)) =
  if (validPT t && ptPow t > ptPow t') then validPoly ts else False
validPoly [t] = validPT t
validPoly [] = True
```

## The zeroth-order topos

The zeroth-order topos of Geb, which is called
"Programmer's FinSet" in the
[Geb notes](https://hackmd.io/qxHXAuyYQuGMUYSZ_neuXA?view),
is inductively defined as the smallest category closed under
all of the following:

- initial object
- terminal object
- finite products
- finite coproducts
- equalizers
- coequalizers

Equalizers are implemented as `Either`-valued predicates.
A coequalizer is a predicate together with a function from
terms which _fail_ to satisfy the predicate to terms which
_do_ satisfy the predicate.  The predicate can be viewed as
specifying that a type has a "normal form", and the function
is a normalizer.  It serves as a coequalizer by mapping each
equivalence class to a single term which serves as a
representative of that class.  (In effect, this gives a type
a built-in equivalence relation.)

## Polynomial endofunctors of PFS

The category in which user-defined data structures appear is
that of the polynomial endofunctors of the zeroth-order topos.

The objects of this category are the polynomial endofunctors,
which are described by the same data structure as in the
back-end category.

The morphisms -- the functions on user-defined data structures --
are natural transformations.  A natural transformation from
`p` to `q` consists of:

- A function `onPos` from the set of all coefficients (which,
when a polynomial is viewed as functor, are sometimes called
"positions") of `p` to the set of all coefficients of `q`
- A dependent function `onDir` which, for each position `i`
of `p`, maps the set of powers `q[onPos(i)]` to the set of
powers `p[i]`

A natural transformation corresponds to a function written
by pattern-matching, if we view the polynomials as data
structures:  `onPos` matches on constructors of `p` and
maps them to constructors of `q`, and `onDir` selects, for
each constructor of `q`, which fields of the constructor
of `p` that maps to it to draw its own fields from.

The dependency of `onDir` on `onPos` will lead to the natural
transformation being compiled by using `RNMSwitchF` on the
output of `onPos` to select from a family of `onDir` functions.

## Front-end recursive categories

Although a pure polynomial circuit can not express recursion,
using a category-theoretic definition of recursion by functor
iteration does make it natural to allow a recursive front-end
language to write _macros_ which output circuits of parameterized
depths.  For example, a polynomial circuit can not process an
arbitrarily-long list, but a front-end language could generate
code for a circuit that would process a list of up to some given
length -- the data type would be generated by iterating a
functor.  For example, `List[3] = 1 + x + x^2`;
`List[5] = 1 + x + x^2 + x^3 + x^4` (where `List[n]` is a list
of length strictly less than `n`).

## Simply-typed lambda calculus

Although I personally prefer combinator calculi to lambda calculi
by now, the latter are more familiar to most functional programmers,
so we might want to provide an STLC front-end which would in turn be
compiled to the zeroth-order topos.  Algorithms to do this have
existed for a long time; see for example
[this implementation](https://github.com/thma/lambda-cat) inspired
by [Compiling to Categories](http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf).
