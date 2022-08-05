module LanguageDef.UniversalCategory

import Library.IdrisCategories
import public LanguageDef.RefinedADT

%default total

-- “Ah Love! could thou and I with Fate conspire
-- To grasp this sorry Scheme of Things entire,
-- Would not we shatter it to bits -- and then
-- Re-mould it nearer to the Heart's Desire!”
--  - _Rubaiyat of Omar Khayyam_ (tr. Edward FitzGerald)

---------------------------------------------------
---------------------------------------------------
---- Free equivalence-parameterized categories ----
---------------------------------------------------
---------------------------------------------------

-----------------------------
---- Paths and morphisms ----
-----------------------------

-------------------------------------
---- Cartesian closed categories ----
-------------------------------------

-------------------------------------
-------------------------------------
---- Categorial algebra in Idris ----
-------------------------------------
-------------------------------------

--------------------
---- F-Algebras ----
--------------------

----------------
---- Magmas ----
----------------

-- A functor which generates binary combinations of its input type.
-- Note that this is a generator, not an interface -- the user does
-- not assert that some type implements the binary operation, but
-- rather calls the functor to _produce_ a type which has a binary
-- operation on the input type.
infixr 8 <>
public export
data MagmaF : Type -> Type where
  (<>) : a -> a -> MagmaF a

public export
Functor MagmaF where
  map f (x <> y) = f x <> f y

-------------------
---- Relations ----
-------------------

-- The Idris type of symmetric binary relations.
SymBinRel : Type -> Type
SymBinRel a = a -> a -> Type

--------------------
---- Semigroups ----
--------------------

infixr 8 <<>>
public export
data SemigroupOpF :
    ((Type -> Type), (Type -> Type -> Type)) -> (Type -> Type) where
  (<<>>) : a -> a -> SemigroupOpF (op, rel) a

-----------------
---- Monoids ----
-----------------

-- A functor whose free algebra generates a free monoid on the input type.
-- It expresses the identity and associativity laws by including terms
-- which express rewriting according to those laws, in the style of
-- a quotient type.
public export
data MonoidF : Type -> Type where
  MId : MonoidF a
  MOp : a -> a -> MonoidF a
  MCancelIdL : a -> MonoidF a
  MCancelIdR : a -> MonoidF a
  MShiftR : a -> a -> a -> MonoidF a

-------------------------
---- Natural numbers ----
-------------------------

---------------
---- Lists ----
---------------

-----------------------------
---- Polynomial algebras ----
-----------------------------

public export
powerToListAlg : Algebra (PowerF v) a -> Algebra (ListF (v, NatF a)) a
powerToListAlg alg = alg . FactorsF

public export
polyToPowerAlg : Algebra (PolynomialF v) a -> Algebra (ListF (PowerF v a)) a
polyToPowerAlg alg = alg . PolyTermsF

public export
polyToListAlg :
  Algebra (PolynomialF v) a -> Algebra (ListF (ListF (v, NatF a) a)) a
polyToListAlg alg = polyToPowerAlg alg . mapFst FactorsF

-- Although not _all_ endofunctors have initial algebras, there are some
-- _classes_ of endofunctors that can be guaranteed to have initial algebras.
-- Polynomials are one such class.

-------------
-------------
---- Geb ----
-------------
-------------

-- Geb is defined by doing category theory "in reverse":  rather than
-- defining some structures and then proving that they are categories,
-- we axiomatize the notions of categories, define some higher categories,
-- and then examine the lower-order categories which emerge necessarily
-- from our postulating the existence of the higher categories.
--
-- The higher categories are defined with with two primary goals:
--
--  - To be able to express all definitions as universal constructions,
--    so that _any_ correct interpreters for Geb must be isomorphic.
--  - To enable the definitions to be expressed in software in a homoiconic
--    and "à la carte" style, so that the languages (plural -- each category
--    is a language) may be extended, and new languages defined, either from
--    scratch or by extending existing ones, including Geb itself.
--
-- Any combination of universal properties defines a category inductively
-- as the smallest category which contains all objects and morphisms specified
-- by those universal constructions.  The high-level categorial construction
-- of Geb overall defines a category containing each combination of properties
-- by creating a defining two-category for it, generating other categories from
-- the root category (which is the category to be defined), such as product
-- categories, functor categories, and F-(co)algebra categories, and
-- specifying the functors, natural transformations, and adjunctions which
-- define the universal properties.  The objects and morphisms of the defined
-- category are therefore precisely the ones required for the specified
-- functors, natural transformations, and adjunctions to exist, and no more.
-- (This is the reverse of typical category theory, where we define various
-- collections of objects and morphisms and then investigate which functors,
-- natural transformations, and adjunctions can be found among them.)
--
-- The set of universal properties defined by the core language specification
-- of Geb is designed to be precisely those which are required to allow any
-- other possible universal constructions to be defined _in_ Geb, including
-- by extension of Geb itself within Geb (as well as devising new categories
-- from scratch).  Conveniently for programmers, that set is drawn from the
-- traditional constructions of programming languages -- initial and terminal
-- objects, products and coproducts, and initial algebras and terminal
-- coalgebras -- as well as constructions less common in the most popular
-- languages but ubiquitous in dependently-typed languages, such as equality
-- types, and (albeit, I think, less commonly) quotient types.
--
-- The set of universal properties required to be defined by the core of Geb
-- does _not_ include exponential objects (also known as currying, and also
-- known as the product-hom adjunction).  This is the categorial reflection
-- of Gödel's construction when proving the incompleteness theorems:  the
-- arithmetic required for self-representation does not need to be higher-order.
-- But self-representation does suffice to define what it _means_ to define
-- other, stronger languages correctly.  So it is in libraries written in Geb,
-- not in the core language definition, that extensions to strictly stronger
-- languages and logics can be made.  The self-representation remains, and
-- consequently, so does the well-typed (including dependently-typed)
-- metaprogramming.
--
-- In addition to well-typed metaprogramming, the explicit use of multiple
-- categories within the same language makes Geb a "programming language of
-- programming languages", intended particularly for uses such as correct-by-
-- construction compilers, and other language-design matters such as modular
-- language extension and algebraic effects.
--
-- The refinement types required to express statically-checked formal
-- properties can be expressed in two equivalent ways.
-- This equivalence translates between two different ways of constraining
-- the interpretation of ADTs:
--   - The categorial way: equalizers and coequalizers
--   - The programming-language way: a typechecker function
--
-- Refined types can be "compiled" to unrefined ones (by erasing the equalizers
-- and coequalizers, or equivalently, by using the categorial equivalence to map
-- from the refined category to the unrefined-plus-typechecker-morphism
-- category and then forgetting the typechecker morphism).
--
-- For any object `a` of any category `C` which has a terminal object, we
-- define the "term category" of `a` as the category whose objects are morphisms
-- of `C` from the terminal object (in `C`) into `a` and whose morphisms are the
-- endomorphisms (in `C`) of `a` which make the resulting diagrams commute.
-- This is a special case of a comma category where the two functors which
-- define the comma category are:
--  - The functor from the terminal category to `C` whose value (on its only
--    input) is the terminal object of `C`
--  - The inclusion functor into `C` from the full subcategory of `C` whose
--    only object is `a`)
-- Geb's notion of well-typed metaprogramming is that each category in its
-- mathematical definition is equivalent to the term category of one of its
-- objects (which is unique up to unique isomorphism, because it is isomorphic
-- to a mathematical object defined solely by universal constructions), and
-- that one of its objects can be interpreted as the type of all of its terms.
--
-- Note that those terms are heterogeneous -- some are categories, some are
-- functors, some are other, programming-related constructs entirely.  The
-- object emerges, after all, as a type in a software implementation.  So
-- while that object (or its term category) can be interpreted as a higher
-- category, because some of its term category's objects are categories, not
-- _all_ of its term category's objects are categories.  This is useful,
-- because it means that terms can represent heterogeneous functions; someone
-- could write, for example, a function from natural numbers to programming
-- languages, where the output of the function for input `n` is `n`-order
-- arithmetic.

mutual
  data GebUniversalPropF : Type -> Type where
    InitialObjectProp : GebUniversalPropF prop
    TerminalObjectProp : GebUniversalPropF prop
    ProductProp : GebUniversalPropF prop
    CoproductProp : GebUniversalPropF prop
    EqualizerProp : GebUniversalPropF prop
    CoequalizerProp : GebUniversalPropF prop
    FreeAlgebraProp : GebUniversalPropF prop
    CofreeAlgebraProp : GebUniversalPropF prop
    HigherOrderProp : GebUniversalPropF prop
    TuringCompleteProp : GebUniversalPropF prop

  -- The functor which defines the object of the refined first-order ADT
  -- category from which all other constructs of Geb can be extracted, and
  -- which can be extended to generate super-languages of Geb.
  data RefinedADTCatF : Type -> Type -> Type where
    GebUP : GebUniversalPropF prop -> RefinedADTCatF prop term

    -- The object in the category of first-order refined ADTs whose term
    -- category is isomorphic to the Idris GebTypeF (or that of any other
    -- correct interpreter in any host language).
    Geb : RefinedADTCatF prop term

FreeRefinedADTCat : Type -> Type -> Type
FreeRefinedADTCat prop = FreeMonad $ RefinedADTCatF prop

CofreeRefinedADTCat : Type -> Type -> Type
CofreeRefinedADTCat prop = CofreeComonad $ RefinedADTCatF prop
