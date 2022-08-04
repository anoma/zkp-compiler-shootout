module LanguageDef.PolyCat

import Library.IdrisUtils
import Library.IdrisCategories

%default total

-------------------------
-------------------------
---- Dependent types ----
-------------------------
-------------------------

public export
SliceObj : Type -> Type
SliceObj a = a -> Type

public export
Pi : {a : Type} -> SliceObj a -> Type
Pi {a} p = (x : a) -> p x

public export
Sigma : {a : Type} -> SliceObj a -> Type
Sigma {a} p = (x : a ** p x)

public export
SigmaToPair : {0 a, b : Type} -> (Sigma {a} (const b)) -> (a, b)
SigmaToPair (x ** y) = (x, y)

public export
PairToSigma : {0 a, b : Type} -> (a, b) -> (Sigma {a} (const b))
PairToSigma (x, y) = (x ** y)

-----------------------
---- Refined types ----
-----------------------

public export
DecPred : Type -> Type
DecPred a = a -> Bool

public export
TruePred : (a : Type) -> DecPred a
TruePred a = const True

public export
FalsePred : (a : Type) -> DecPred a
FalsePred a = const False

public export
NotPred : {0 a : Type} -> DecPred a -> DecPred a
NotPred pred = not . pred

public export
AndPred : {0 a : Type} -> DecPred a -> DecPred a -> DecPred a
AndPred p q = \x => p x && q x

public export
OrPred : {0 a : Type} -> DecPred a -> DecPred a -> DecPred a
OrPred p q = \x => p x || q x

public export
ImpliesPred : {0 a : Type} -> DecPred a -> DecPred a -> DecPred a
ImpliesPred p q = \x => not (p x) || q x

public export
AndNotPred : {0 a : Type} -> DecPred a -> DecPred a -> DecPred a
AndNotPred p q = \x => p x && not (q x)

public export
Satisfies : {0 a : Type} -> DecPred a -> a -> Type
Satisfies p x = p x = True

public export
Refinement : {a : Type} -> DecPred a -> Type
Refinement {a} p = Subset0 a (Satisfies p)

public export
TrueRefinement : Type -> Type
TrueRefinement a = Refinement (TruePred a)

public export
FalseRefinement : Type -> Type
FalseRefinement a = Refinement (FalsePred a)

public export
NotRefinement : {a : Type} -> DecPred a -> Type
NotRefinement = Refinement . NotPred

public export
AndRefinement : {a : Type} -> DecPred a -> DecPred a -> Type
AndRefinement p q = Refinement (AndPred p q)

public export
OrRefinement : {a : Type} -> DecPred a -> DecPred a -> Type
OrRefinement p q = Refinement (OrPred p q)

public export
ImpliesRefinement : {a : Type} -> DecPred a -> DecPred a -> Type
ImpliesRefinement p q = Refinement (ImpliesPred p q)

public export
AndNotRefinement : {a : Type} -> DecPred a -> DecPred a -> Type
AndNotRefinement p q = Refinement (AndNotPred p q)

public export
MkRefinement : {0 a : Type} -> {0 p : DecPred a} ->
  (x : a) -> {auto 0 satisfies : Satisfies p x} ->
  Refinement {a} p
MkRefinement x {satisfies} = Element0 x satisfies

public export
shape : {0 a : Type} -> {0 p : DecPred a} -> Refinement {a} p -> a
shape = fst

public export
VoidRefinement : DecPred Void
VoidRefinement = voidF Bool

public export
Refined : Type
Refined = Subset0 Type DecPred

--------------------------
---- Refined functors ----
--------------------------

public export
DecPredF : (Type -> Type) -> Type
DecPredF f = NaturalTransformation DecPred (DecPred . f)

public export
RefinedF : {f : Type -> Type} -> DecPredF f -> Refined -> Refined
RefinedF {f} pf (Element0 a pred) = Element0 (f a) (pf a pred)

----------------------------------
---- Bicomplete refined types ----
----------------------------------

public export
Normalized : {a : Type} ->
  (pred : DecPred a) -> (norm : DecPred a) -> Type
Normalized {a} pred norm = AndRefinement pred norm

public export
NonNormalized : {a : Type} ->
  (pred : DecPred a) -> (norm : DecPred a) -> Type
NonNormalized {a} pred norm = AndNotRefinement pred norm

public export
Normalizer : {a : Type} ->
  (pred : DecPred a) -> (norm : DecPred a) -> Type
Normalizer {a} pred norm = NonNormalized pred norm -> Normalized pred norm

public export
Coequalized : Type
Coequalized =
  (a : Type ** pred : DecPred a ** norm : DecPred a ** Normalizer pred norm)

public export
normalizedCompose :
  {0 a, b, c : Type} ->
  {0 pred : DecPred b} ->
  {norm : DecPred b} ->
  {fn : Normalizer pred norm} ->
  (g : Normalized {a=b} pred norm -> c) ->
  (f : a -> Refinement {a=b} pred) ->
  a -> c
normalizedCompose {norm} {fn} g f x = g $ case f x of
  Element0 x' satisfies => case decEq (norm x') True of
    Yes normalized => Element0 x' $ rewrite satisfies in normalized
    No nonNormalized => fn $ Element0 x' $
      rewrite satisfies in rewrite notTrueIsFalse nonNormalized in Refl

public export
NormalizerF : {f : Type -> Type} -> (predf, normf : DecPredF f) -> Type
NormalizerF {f} predf normf =
  (a : Type) -> (pred, norm : DecPred a) ->
  Normalizer pred norm -> Normalizer (predf a pred) (normf a norm)

public export
CoequalizedF :
  {f : Type -> Type} ->
  (predf, normf : DecPredF f) ->
  (normalizerf : NormalizerF {f} predf normf) ->
  Coequalized -> Coequalized
CoequalizedF {f} predf normf normalizerf (a ** pred ** norm ** fn) =
  (f a ** predf a pred ** normf a norm ** normalizerf a pred norm fn)

---------------------------------------------
---------------------------------------------
---- Natural numbers as directed colimit ----
---------------------------------------------
---------------------------------------------

--------------------------------
---- General F-(co)algebras ----
--------------------------------

public export
FAlg : (Type -> Type) -> Type -> Type
FAlg f a = f a -> a

public export
FCoalg : (Type -> Type) -> Type -> Type
FCoalg f a = a -> f a

public export
data TranslateF : (0 f : Type -> Type) -> (0 a, x : Type) -> Type where
  InTF : {0 f : Type -> Type} -> {0 a, x : Type} ->
    Either a (f x) -> TranslateF f a x

public export
InVar : {0 f : Type -> Type} -> {0 a, x : Type} -> a -> TranslateF f a x
InVar = InTF . Left

public export
InCom : {0 f : Type -> Type} -> {0 a, x : Type} -> f x -> TranslateF f a x
InCom = InTF . Right

public export
data LinearF : (0 f : Type -> Type) -> (0 a, x : Type) -> Type where
  InLF : {0 f : Type -> Type} -> {0 a, x : Type} ->
    Pair a (f x) -> LinearF f a x

public export
InNode : {0 f : Type -> Type} -> {0 a, x : Type} -> a -> f x -> LinearF f a x
InNode = ((.) InLF) . MkPair

public export
data FreeM : (0 f : Type -> Type) -> (0 x : Type) -> Type where
  InFreeM : {0 f : Type -> Type} -> {0 x : Type} ->
    TranslateF f x (FreeM f x) -> FreeM f x

public export
InFVar : {0 f : Type -> Type} -> {0 x : Type} -> x -> FreeM f x
InFVar = InFreeM . InVar

public export
InFCom : {0 f : Type -> Type} -> {0 x : Type} -> f (FreeM f x) -> FreeM f x
InFCom = InFreeM . InCom

public export
data CofreeCM : (0 f : Type -> Type) -> (0 x : Type) -> Type where
  InCofreeCM : {0 f : Type -> Type} -> {0 x : Type} ->
    Inf (LinearF f x (CofreeCM f a)) -> CofreeCM f x

public export
InCFNode : {0 f : Type -> Type} -> {0 x : Type} ->
  x -> f (CofreeCM f x) -> CofreeCM f x
InCFNode ex efx = InCofreeCM $ InLF (ex, efx)

public export
MuF : (0 f : Type -> Type) -> Type
MuF f = FreeM f Void

public export
NuF : (0 f : Type -> Type) -> Type
NuF f = CofreeCM f Unit

public export
MuCata : (Type -> Type) -> Type -> Type
MuCata f x = Algebra f x -> MuF f -> x

public export
FromInitialFAlg : (Type -> Type) -> Type
FromInitialFAlg f = (x : Type) -> MuCata f x

public export
NuAna : (Type -> Type) -> Type -> Type
NuAna f x = Coalgebra f x -> x -> NuF f

public export
ToTerminalFCoalg : (Type -> Type) -> Type
ToTerminalFCoalg f = (x : Type) -> NuAna f x

-----------------------
---- Pair algebras ----
-----------------------

public export
PairFAlg : (Type -> Type) -> Type -> Type
PairFAlg f = FAlg f . FAlg f

public export
MuPairCata : (Type -> Type) -> Type -> Type
MuPairCata f x = PairFAlg f x -> MuF f -> MuF f -> x

public export
FromInitialPairFAlg : (Type -> Type) -> Type
FromInitialPairFAlg f = (x : Type) -> MuPairCata f x

public export
muPairCata : {f : Type -> Type} -> FromInitialFAlg f -> FromInitialPairFAlg f
muPairCata {f} cata x alg e e' = cata x (cata (FAlg f x) alg e) e'

-------------------------------------
---- Types dependent on algebras ----
-------------------------------------

public export
MuSliceObj : (f : Type -> Type) -> Type
MuSliceObj f = (MuCata f Type, FAlg f Type)

public export
MuPiType : {f : Type -> Type} -> MuSliceObj f -> Type
MuPiType {f} (cata, tyAlg) = (e : MuF f) -> cata tyAlg e

public export
MuSigmaType : {f : Type -> Type} -> MuSliceObj f -> Type
MuSigmaType {f} (cata, tyAlg) = (e : MuF f ** cata tyAlg e)

--------------------------------------
---- Algebras of refined functors ----
--------------------------------------

public export
0 PreservesRefinement : {a, b : Type} ->
  (0 pa : DecPred a) -> (0 pb : DecPred b) -> (a -> b) -> Type
PreservesRefinement {a} {b} pa pb f =
  (e : a) -> (0 satisfies : Satisfies pa e) -> Satisfies pb (f e)

public export
RefinedMorphism : Refined -> Refined -> Type
RefinedMorphism (Element0 a pa) (Element0 b pb) =
  Subset0 (a -> b) (PreservesRefinement pa pb)

public export
RefinedAlg : {f : Type -> Type} -> DecPredF f -> Refined -> Type
RefinedAlg {f} pf x = RefinedMorphism (RefinedF pf x) x

public export
RefinedCoalg : {f : Type -> Type} -> DecPredF f -> Refined -> Type
RefinedCoalg {f} pf x = RefinedMorphism x (RefinedF pf x)

---------------------------------
---- Natural number functors ----
---------------------------------

public export
MaybeEUF : Type -> Type
MaybeEUF = Either Unit

public export
NatOF : Type -> Type
NatOF = MaybeEUF

public export
NatOAlg : Type -> Type
NatOAlg = FAlg NatOF

public export
NatOAlgC : Type -> Type
NatOAlgC a = (a, a -> a)

public export
NatOAlgCToAlg : {a : Type} -> NatOAlgC a -> NatOAlg a
NatOAlgCToAlg {a} (z, s) e = case e of
  Left () => z
  Right n => s n

public export
NatOCoalg : Type -> Type
NatOCoalg = FCoalg NatOF

public export
FreeNatO : Type -> Type
FreeNatO x = FreeM NatOF x

public export
MuNatO : Type
MuNatO = MuF NatOF

public export
NatO0 : {0 x : Type} -> FreeNatO x
NatO0 = InFCom $ Left ()

public export
NatOS : {0 x : Type} -> FreeNatO x -> FreeNatO x
NatOS = InFCom . Right

public export
NatO1 : {0 x : Type} -> FreeNatO x
NatO1 = NatOS NatO0

public export
natOCata : FromInitialFAlg NatOF
natOCata x alg (InFreeM $ InTF $ Left v) = void v
natOCata x alg (InFreeM $ InTF $ Right c) = alg $ case c of
  Left () => Left ()
  Right n => Right $ natOCata x alg n

public export
natOCataC : {x : Type} -> NatOAlgC x -> MuNatO -> x
natOCataC {x} alg = natOCata x (NatOAlgCToAlg alg)

public export
CofreeNatO : Type -> Type
CofreeNatO x = CofreeCM NatOF x

public export
NuNatO : Type
NuNatO = NuF NatOF

public export
natOAna : ToTerminalFCoalg NatOF
natOAna x coalg e = InCofreeCM $ InLF $ MkPair () $ case coalg e of
  Left () => Left ()
  Right n => Right $ natOAna x coalg n

public export
muToNatAlg : NatOAlgC Nat
muToNatAlg = (Z, S)

public export
muToNat : MuNatO -> Nat
muToNat = natOCataC muToNatAlg

public export
natToMu : Nat -> MuNatO
natToMu Z = NatO0
natToMu (S n) = NatOS $ natToMu n

public export
Show MuNatO where
  show = show . muToNat

public export
MuNatIdAlg : NatOAlgC MuNatO
MuNatIdAlg = (NatO0, NatOS)

public export
mapNatAlg : {0 x : Type} -> (x -> x) -> NatOAlgC x -> NatOAlgC x
mapNatAlg f (z, s) = (f z, f . s)

----------------------------------
---- Pairs of natural numbers ----
----------------------------------

public export
NatOPairF : Type -> Type
NatOPairF = ProductMonad . NatOF

public export
NatOPairAlg : Type -> Type
NatOPairAlg = FAlg NatOPairF

public export
NatOPairAlgC : Type -> Type
NatOPairAlgC x = (x, x -> x, x -> x, (x, x) -> x)

public export
NatOPairAlgCToAlg : {a : Type} -> NatOPairAlgC a -> NatOPairAlg a
NatOPairAlgCToAlg (zz, zs, sz, ss) e = case e of
  (Left (), Left ()) => zz
  (Left (), Right n) => zs n
  (Right n, Left ()) => sz n
  (Right m, Right n) => ss (m, n)

public export
NatOAlgToPairL0Alg : {0 x : Type} -> NatOAlgC x -> NatOPairAlgC x
NatOAlgToPairL0Alg (z, sl) = (z, const z, sl, sl . fst)

public export
NatAlgToPair0RAlg : {0 x : Type} -> NatOAlgC x -> NatOPairAlgC x
NatAlgToPair0RAlg (z, sr) = (z, sr, const z, sr . snd)

public export
NatOPairCoalg : Type -> Type
NatOPairCoalg = FCoalg NatOPairF

public export
natSumAlg : NatOAlgC (MuNatO -> MuNatO)
natSumAlg = (id, (.) NatOS)

public export
natSum : MuNatO -> MuNatO -> MuNatO
natSum = natOCataC natSumAlg

public export
natMulAlg : NatOAlgC (MuNatO -> MuNatO)
natMulAlg = (const NatO0, \alg, n => natSum (alg n) n)

public export
natMul : MuNatO -> MuNatO -> MuNatO
natMul = natOCataC natMulAlg

public export
natRaiseToAlg : NatOAlgC (MuNatO -> MuNatO)
natRaiseToAlg = (const NatO1, \alg, n => natMul (alg n) n)

public export
natRaiseTo : MuNatO -> MuNatO -> MuNatO
natRaiseTo = natOCataC natRaiseToAlg

public export
natPow : MuNatO -> MuNatO -> MuNatO
natPow = flip natRaiseTo

--------------------------------------------------------
---- Bounded natural numbers from directed colimits ----
--------------------------------------------------------

public export
NatPreAlgC : NatOAlgC Type
NatPreAlgC = (Void, NatOF)

-- The type of natural numbers strictly less than the given natural number.
public export
NatPre : MuNatO -> Type
NatPre = natOCataC NatPreAlgC

public export
NatPreAlg : Type -> Type
NatPreAlg x = MuNatO -> NatOAlgC x

public export
natPreCata : {0 x : Type} -> NatPreAlg x -> {n : MuNatO} -> NatPre n -> x
natPreCata {x} alg {n=(InFreeM $ InTF $ Left v)} m = void v
natPreCata {x} alg {n=(InFreeM $ InTF $ Right $ Left ())} m = void m
natPreCata {x} alg {n=(InFreeM $ InTF $ Right $ Right n)} m =
  let (z, s) = alg n in
  case m of
    (Left ()) => z
    (Right m') => s $ natPreCata {x} alg {n} m'

{-
public export
NatPreAlgAlg : Type -> Type
NatPreAlgAlg x = NatPreAlgAlg_hole

public export
natPreAlgAlgToAlg : {0 x : Type} -> NatPreAlgAlg x -> NatPreAlg x
natPreAlgAlgToAlg {x} algalg = natPreAlgAlgToAlg_hole

public export
natPreAlgCata : {0 x : Type} -> NatPreAlgAlg x -> {n : MuNatO} -> NatPre n -> x
natPreAlgCata {x} algalg = natPreCata {x} (natPreAlgAlgToAlg {x} algalg)
-}

public export
NatPreMeta : Nat -> Type
NatPreMeta = NatPre . natToMu

public export
preToMetaAlg : NatPreAlg Nat
preToMetaAlg = const muToNatAlg

public export
preToMeta : {n : Nat} -> NatPreMeta n -> Nat
preToMeta {n} = natPreCata {x=Nat} preToMetaAlg {n=(natToMu n)}

public export
metaToPre : (m : Nat) -> (0 n : Nat) -> {auto 0 lt : LT m n} -> NatPreMeta n
metaToPre Z (S n) {lt=(LTESucc _)} = Left ()
metaToPre (S m) (S n) {lt=(LTESucc lt')} = Right $ metaToPre m {n} {lt=lt'}

public export
InitPre : (m : Nat) -> (0 n : Nat) -> {auto 0 lt : IsYesTrue (isLT m n)} ->
  NatPreMeta n
InitPre m n {lt} = metaToPre m n {lt=(fromIsYes lt)}

public export
showPreMeta : (n : Nat) -> NatPreMeta n -> String
showPreMeta n m = show (preToMeta m) ++ "/" ++ show n

--------------------------
---- Tuples and lists ----
--------------------------

public export
TupleAlgC : Type -> NatOAlgC Type
TupleAlgC x = ((), Pair x)

-- The type of tuples of the given length.
public export
Tuple : Type -> MuNatO -> Type
Tuple = natOCataC . TupleAlgC

public export
ListNAlgC : Type -> NatOAlgC Type
ListNAlgC x = ((), CoproductF Prelude.id (Pair x))

-- The type of tuples of less than or equal to the given length.
public export
ListN : Type -> MuNatO -> Type
ListN = natOCataC . ListNAlgC

----------------------------------
---- Trees of natural numbers ----
----------------------------------

public export
MuNatOT : Type
MuNatOT = MuF NatOPairF

public export
natOTCata : FromInitialFAlg NatOPairF
natOTCata x alg (InFreeM $ InTF $ Left v) = void v
natOTCata x alg (InFreeM $ InTF $ Right c) = alg $ case c of
  (Left (), Left ()) => (Left (), Left ())
  (Left (), Right n) => (Left (), Right $ natOTCata x alg n)
  (Right n, Left ()) => (Right $ natOTCata x alg n, Left ())
  (Right m, Right n) => (Right $ natOTCata x alg m, Right $ natOTCata x alg n)

--------------------------------------------------
--------------------------------------------------
---- Natural number induction and coinduction ----
--------------------------------------------------
--------------------------------------------------

-------------------------------------------------------
---- Dependent (slice) category of natural numbers ----
-------------------------------------------------------

public export
NatSliceObj : Type
NatSliceObj = SliceObj Nat

public export
NatPi : NatSliceObj -> Type
NatPi = Pi {a=Nat}

public export
NatSigma : NatSliceObj -> Type
NatSigma = Sigma {a=Nat}

-- If we view a slice object as a functor from the discrete category of
-- natural numbers to the category `Type`, then this type can be viewed as
-- a natural transformation.
public export
NatSliceNatTrans : NatSliceObj -> NatSliceObj -> Type
NatSliceNatTrans p q = (n : Nat) -> p n -> q n

public export
NatSliceMorphism : NatSliceObj -> (Nat -> Nat) -> Type
NatSliceMorphism p f = NatSliceNatTrans p (p . f)

public export
NatDepAlgebra : NatSliceObj -> Type
NatDepAlgebra p = (p Z, NatSliceMorphism p S)

public export
natDepCata : {0 p : NatSliceObj} ->
  NatDepAlgebra p -> NatPi p
natDepCata (z, s) Z = z
natDepCata dalg@(z, s) (S n) = s n (natDepCata dalg n)

public export
NatDepCoalgebra : NatSliceObj -> Type
NatDepCoalgebra p = NatSliceNatTrans p (Maybe . p . S)

public export
natDepAna : {0 p : NatSliceObj} ->
  NatDepCoalgebra p -> NatSigma p -> Inf (Maybe (NatSigma p))
natDepAna coalg (n ** x) with (coalg n x)
  natDepAna coalg (n ** x) | Nothing = Nothing
  natDepAna coalg (n ** x) | Just x' = Delay (natDepAna coalg (S n ** x'))

public export
natGenIndStrengthened : {0 p : NatSliceObj} ->
  (p 0) ->
  ((n : Nat) -> ((m : Nat) -> LTE m n -> p m) -> p (S n)) ->
  (x : Nat) -> (y : Nat) -> LTE y x -> p y
natGenIndStrengthened {p} p0 pS =
  natDepCata
    {p=(\x => (y : Nat) -> LTE y x -> p y)}
    (\n, lte => replace {p} (lteZeroIsZero lte) p0,
     \n, hyp, y, lteySn => case lteSuccEitherEqLte lteySn of
      Left eq => replace {p} (sym eq) $ pS n hyp
      Right lteyn => hyp y lteyn)

public export
natGenInd : {0 p : NatSliceObj} ->
  (p 0) ->
  ((n : Nat) -> ((m : Nat) -> LTE m n -> p m) -> p (S n)) ->
  (k : Nat) -> p k
natGenInd p0 pS k = natGenIndStrengthened p0 pS k k reflexive

-----------------------
---- Non-dependent ----
-----------------------

public export
NatAlgebra : Type -> Type
NatAlgebra a = (a, Nat -> a -> a)

public export
natCata : {0 a : Type} -> NatAlgebra a -> Nat -> a
natCata = natDepCata {p=(const a)}

public export
NatCoalgebra : Type -> Type
NatCoalgebra a = Nat -> a -> Maybe a

public export
natAna : {0 a : Type} -> NatCoalgebra a -> (Nat, a) -> Inf (Maybe (Nat, a))
natAna coalg nx =
  map {f=Maybe} SigmaToPair $ natDepAna {p=(const a)} coalg $ PairToSigma nx

---------------------
---- Polynomials ----
---------------------

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

public export
Polynomial : Type
Polynomial = Refinement {a=PolyShape} validPoly

public export
ValidPoly : PolyShape -> Type
ValidPoly = Satisfies validPoly

public export
MkPolynomial :
  (shape : PolyShape) -> {auto 0 valid : validPoly shape = True} -> Polynomial
MkPolynomial shape {valid} = MkRefinement {a=PolyShape} shape {satisfies=valid}

public export
headPow : PolyShape -> Nat
headPow (t :: ts) = ptPow t
headPow [] = 0

public export
degree : Polynomial -> Nat
degree = headPow . shape

public export
accumPTCoeff : Nat -> PolyShape -> Nat
accumPTCoeff = foldl ((|>) ptCoeff . (+))

public export
sumPTCoeff : PolyShape -> Nat
sumPTCoeff = accumPTCoeff 0

public export
sumCoeff : Polynomial -> Nat
sumCoeff = sumPTCoeff . shape

public export
psIdx : PolyShape -> Nat -> Nat
psIdx [] _ = 0
psIdx ((_, Z) :: ts) n = psIdx ts n
psIdx ((p, S c) :: ts) Z = p
psIdx ((p, S c) :: ts) (S n) = psIdx ((p, c) :: ts) n

public export
pIdx : Polynomial -> Nat -> Nat
pIdx = psIdx . shape

public export
psPosFoldStartingAt : {0 x : Type} ->
  ((pos, pow : Nat) -> x -> x) -> x -> (pos : Nat) -> PolyShape -> x
psPosFoldStartingAt f acc pos [] = acc
psPosFoldStartingAt f acc pos ((pow, c) :: ts) =
  psPosFoldStartingAt f (repeatIdx (flip f pow) c pos acc) (pos + c) ts

public export
psPosFold : {0 x : Type} -> ((pos, pow : Nat) -> x -> x) -> x -> PolyShape -> x
psPosFold f acc = psPosFoldStartingAt f acc 0

public export
psIdxShow : PolyShape -> String
psIdxShow =
  psPosFold
    (\pos, pow, str =>
      let pre = if (pos == 0) then "" else str ++ "; " in
      pre ++ "pos[" ++ show pos ++ "] = " ++ show pow)
    ""

public export
pIdxFold : {0 x : Type} -> ((pos, pow : Nat) -> x -> x) -> x -> Polynomial -> x
pIdxFold f acc = psPosFold f acc . shape

public export
sumPSDir : PolyShape -> Nat
sumPSDir = psPosFold (const (+)) 0

public export
sumPolyDir : Polynomial -> Nat
sumPolyDir = sumPSDir . shape

public export
numTerms : Polynomial -> Nat
numTerms = length . shape

-- Parameters: (accumulator, power, input).
-- Performs exponentiation by breaking it down into individual multiplications.
public export
ptInterpNatAccum : Nat -> Nat -> Nat -> Nat
ptInterpNatAccum acc (S p) n = ptInterpNatAccum (n * acc) p n
ptInterpNatAccum acc Z n = acc

public export
ptInterpNatByMults : PolyTerm -> Nat -> Nat
ptInterpNatByMults t = ptInterpNatAccum (ptCoeff t) (ptPow t) -- acc == coeff

-- Performs exponentiation using built-in power function.
public export
ptInterpNat : PolyTerm -> Nat -> Nat
ptInterpNat t n = (ptCoeff t) * power n (ptPow t)

public export
psInterpNatAccum : Nat -> PolyShape -> Nat -> Nat
psInterpNatAccum acc (t :: ts) n = psInterpNatAccum (ptInterpNat t n + acc) ts n
psInterpNatAccum acc [] n = acc

public export
psInterpNat : PolyShape -> Nat -> Nat
psInterpNat = psInterpNatAccum 0

public export
psMin : PolyShape -> Nat
psMin = flip psInterpNat 0

public export
psMax : PolyShape -> Nat -> Nat
psMax = psInterpNat

public export
polyInterpNat : Polynomial -> Nat -> Nat
polyInterpNat = psInterpNat . shape

public export
polyMin : Polynomial -> Nat
polyMin = psMin . shape

public export
polyMax : Polynomial -> Nat -> Nat
polyMax = psMax . shape

-- XXX arenas w/bijections

-- XXX lenses / natural transformations w/bijections

-- XXX horizontal & vertical composition of NTs

-- XXX eval (i.e. for exponential)

-- XXX equalizer

-- XXX coequalizer

-- XXX eval for parallel product

-- XXX derivative (as one-hole context)

-- XXX plugging in (to one-hole context)

-- XXX p-p0, and iteration of it

-----------------------------------
---- Arithmetic on polynomials ----
-----------------------------------

public export
initialPolyShape : PolyShape
initialPolyShape = []

public export
initialPoly : Polynomial
initialPoly = MkPolynomial initialPolyShape

public export
terminalPolyShape : PolyShape
terminalPolyShape = [(0, 1)]

public export
terminalPoly : Polynomial
terminalPoly = MkPolynomial terminalPolyShape

public export
idPolyShape : PolyShape
idPolyShape = [(1, 1)]

public export
idPoly : Polynomial
idPoly = MkPolynomial idPolyShape

public export
homNPolyShape : Nat -> PolyShape
homNPolyShape n = [(n, 1)]

public export
homNPoly : Nat -> Polynomial
homNPoly n = Element0 (homNPolyShape n) Refl

public export
constPolyShape : Nat -> PolyShape
constPolyShape Z = []
constPolyShape n@(S _) = [(0, n)]

public export
constPoly : Nat -> Polynomial
constPoly n = Element0 (constPolyShape n) ?constPolyCorrect_hole

public export
prodIdPolyShape : Nat -> PolyShape
prodIdPolyShape Z = []
prodIdPolyShape n@(S _) = [(1, n)]

public export
prodIdPoly : Nat -> Polynomial
prodIdPoly n = Element0 (prodIdPolyShape n) ?prodIdPolyCorrect_hole

-- Multiply by a monomial.
public export
scaleMonPolyRevAcc : PolyTerm -> PolyShape -> PolyShape -> PolyShape
scaleMonPolyRevAcc (_, Z) acc _ = []
scaleMonPolyRevAcc (pm, n@(S _)) acc [] = acc
scaleMonPolyRevAcc (pm, n@(S _)) acc ((p, c) :: ts) =
  scaleMonPolyRevAcc (pm, n) ((pm + p, n * c) :: acc) ts

public export
scaleMonPolyRev : PolyTerm -> PolyShape -> PolyShape
scaleMonPolyRev pt = scaleMonPolyRevAcc pt []

public export
scaleMonPolyShape : PolyTerm -> PolyShape -> PolyShape
scaleMonPolyShape pt = reverse . scaleMonPolyRev pt

public export
scalePreservesValid : {0 pt : PolyTerm} -> {0 poly : PolyShape} ->
  ValidPoly poly -> ValidPoly (scaleMonPolyShape pt poly)
scalePreservesValid {pt} {poly} valid = ?scaleMonPolyShapeCorrect_hole

public export
scaleMonPoly : PolyTerm -> Polynomial -> Polynomial
scaleMonPoly pt (Element0 poly valid) =
  Element0 (scaleMonPolyShape pt poly) (scalePreservesValid valid)

public export
scaleNatPolyShape : Nat -> PolyShape -> PolyShape
scaleNatPolyShape n = scaleMonPolyShape (0, n)

public export
scaleNatPoly : Nat -> Polynomial -> Polynomial
scaleNatPoly n = scaleMonPoly (0, n)

public export
parProdMonPolyRevAcc : PolyTerm -> PolyShape -> PolyShape -> PolyShape
parProdMonPolyRevAcc (_, Z) acc _ = []
parProdMonPolyRevAcc (pm, n@(S _)) acc [] = acc
parProdMonPolyRevAcc (pm, n@(S _)) acc ((p, c) :: ts) =
  parProdMonPolyRevAcc (pm, n) ((pm * p, n * c) :: acc) ts

public export
parProdMonPolyRev : PolyTerm -> PolyShape -> PolyShape
parProdMonPolyRev pt = parProdMonPolyRevAcc pt []

public export
parProdMonPolyShape : PolyTerm -> PolyShape -> PolyShape
parProdMonPolyShape (Z, c) poly = [(0, c * sumPTCoeff poly)]
parProdMonPolyShape pt@(S _, _) poly = reverse (parProdMonPolyRev pt poly)

public export
parProdMonPreservesValid : {0 pt : PolyTerm} -> {0 poly : PolyShape} ->
  ValidPoly poly -> ValidPoly (parProdMonPolyShape pt poly)
parProdMonPreservesValid {pt} {poly} valid = ?parProdMonPolyShapeCorrect_hole

public export
parProdMonPoly : PolyTerm -> Polynomial -> Polynomial
parProdMonPoly pt (Element0 poly valid) =
  Element0 (parProdMonPolyShape pt poly) (parProdMonPreservesValid valid)

public export
polyShapeBinOpRevAccN :
  (rOnly, lOnly : PolyTerm -> Maybe PolyTerm) ->
  (rGTl, lGTr : PolyTerm -> PolyTerm -> Maybe PolyTerm) ->
  (rEQl : (pow, coeffL, coeffR : Nat) -> Maybe PolyTerm) ->
  Nat -> PolyShape -> PolyShape -> PolyShape -> PolyShape
polyShapeBinOpRevAccN rOnly lOnly rGTl lGTr rEQl n acc polyL polyR =
  polyShapeBinOpRevAccNInternal n acc polyL polyR where
    polyShapeBinOpRevAccNInternal :
      Nat -> PolyShape -> PolyShape -> PolyShape -> PolyShape
    polyShapeBinOpRevAccNInternal Z acc _ _ = acc
    polyShapeBinOpRevAccNInternal (S n) acc [] [] = acc
    polyShapeBinOpRevAccNInternal (S n) acc [] (t@(p, c) :: ts) =
      case rOnly t of
        Just rt => polyShapeBinOpRevAccNInternal n (rt :: acc) [] ts
        Nothing => polyShapeBinOpRevAccNInternal n acc [] ts
    polyShapeBinOpRevAccNInternal (S n) acc (t@(p, c) :: ts) [] =
      case lOnly t of
        Just lt => polyShapeBinOpRevAccNInternal n (lt :: acc) ts []
        Nothing => polyShapeBinOpRevAccNInternal n acc ts []
    polyShapeBinOpRevAccNInternal (S n) acc
      q@(t@(p, c) :: ts) r@(t'@(p', c') :: ts') =
        case compare p p' of
          EQ =>
            case rEQl p c c' of
              Just eqt => polyShapeBinOpRevAccNInternal n (eqt :: acc) ts ts'
              Nothing => polyShapeBinOpRevAccNInternal n acc ts ts'
          LT =>
            case rGTl t t' of
              Just rt => polyShapeBinOpRevAccNInternal n (rt :: acc) q ts'
              Nothing => polyShapeBinOpRevAccNInternal n acc q ts'
          GT =>
            case lGTr t t' of
              Just lt => polyShapeBinOpRevAccNInternal n (lt :: acc) ts r
              Nothing => polyShapeBinOpRevAccNInternal n acc ts r

public export
polyShapeBinOpRevAcc :
  (rOnly, lOnly : PolyTerm -> Maybe PolyTerm) ->
  (rGTl, lGTr : PolyTerm -> PolyTerm -> Maybe PolyTerm) ->
  (rEQl : (pow, coeffL, coeffR : Nat) -> Maybe PolyTerm) ->
  PolyShape -> PolyShape -> PolyShape -> PolyShape
polyShapeBinOpRevAcc rOnly lOnly rGTl lGTr rEQl acc p q =
  polyShapeBinOpRevAccN rOnly lOnly rGTl lGTr rEQl (length p + length q) acc p q

public export
addPolyShapeRevAcc : PolyShape -> PolyShape -> PolyShape -> PolyShape
addPolyShapeRevAcc =
  polyShapeBinOpRevAcc
    Just
    Just
    (\t, t' => Just t')
    (\t, t' => Just t)
    (\p, c, c' => Just (p, c + c'))

public export
addPolyShapeRev : PolyShape -> PolyShape -> PolyShape
addPolyShapeRev = addPolyShapeRevAcc []

public export
addPolyShape : PolyShape -> PolyShape -> PolyShape
addPolyShape p q = reverse (addPolyShapeRev p q)

public export
addPreservesValid : {0 p, q : PolyShape} ->
  ValidPoly p -> ValidPoly q -> ValidPoly (addPolyShape p q)
addPreservesValid {p} {q} pvalid qvalid = ?addPolyShapeCorrect_hole

public export
addPoly : Polynomial -> Polynomial -> Polynomial
addPoly (Element0 p pvalid) (Element0 q qvalid) =
  Element0 (addPolyShape p q) (addPreservesValid pvalid qvalid)

public export
addPolyShapeList : List PolyShape -> PolyShape
addPolyShapeList = foldr addPolyShape initialPolyShape

public export
mulPolyShape : PolyShape -> PolyShape -> PolyShape
mulPolyShape p q = addPolyShapeList $ map (flip scaleMonPolyShape q) p

public export
mulPreservesValid : {0 p, q : PolyShape} ->
  ValidPoly p -> ValidPoly q -> ValidPoly (mulPolyShape p q)
mulPreservesValid {p} {q} pvalid qvalid = ?mulPolyShapeCorrect_hole

public export
mulPoly : Polynomial -> Polynomial -> Polynomial
mulPoly (Element0 p pvalid) (Element0 q qvalid) =
  Element0 (mulPolyShape p q) (mulPreservesValid pvalid qvalid)

public export
mulPolyShapeList : List PolyShape -> PolyShape
mulPolyShapeList = foldr mulPolyShape terminalPolyShape

public export
parProdPolyShape : PolyShape -> PolyShape -> PolyShape
parProdPolyShape p q = addPolyShapeList $ map (flip parProdMonPolyShape q) p

public export
parProdPreservesValid : {0 p, q : PolyShape} ->
  ValidPoly p -> ValidPoly q -> ValidPoly (parProdPolyShape p q)
parProdPreservesValid {p} {q} pvalid qvalid = ?parProdPolyShapeCorrect_hole

public export
parProdPoly : Polynomial -> Polynomial -> Polynomial
parProdPoly (Element0 p pvalid) (Element0 q qvalid) =
  Element0 (parProdPolyShape p q) (parProdPreservesValid pvalid qvalid)

public export
parProdPolyShapeList : List PolyShape -> PolyShape
parProdPolyShapeList = foldr parProdPolyShape idPolyShape

public export
expNPolyShape : Nat -> PolyShape -> PolyShape
expNPolyShape Z _ = terminalPolyShape
expNPolyShape (S n) p = mulPolyShape p (expNPolyShape n p)

public export
expNPreservesValid : {0 n : Nat} -> {0 poly : PolyShape} ->
  ValidPoly poly -> ValidPoly (expNPolyShape n poly)
expNPreservesValid {n} {poly} valid = ?expNPolyShapeCorrect_hole

public export
expNPoly : Nat -> Polynomial -> Polynomial
expNPoly n (Element0 poly valid) =
  Element0 (expNPolyShape n poly) (expNPreservesValid valid)

public export
composeMonPoly : PolyTerm -> PolyShape -> PolyShape
composeMonPoly (p, c) poly = scaleNatPolyShape c $ expNPolyShape p poly

public export
composePolyShape : PolyShape -> PolyShape -> PolyShape
composePolyShape q p = addPolyShapeList $ map (flip composeMonPoly p) q

public export
composePreservesValid : {0 p, q : PolyShape} ->
  ValidPoly q -> ValidPoly p -> ValidPoly (composePolyShape q p)
composePreservesValid {p} {q} pvalid qvalid = ?composePolyShapeCorrect_hole

public export
composePoly : Polynomial -> Polynomial -> Polynomial
composePoly (Element0 q qvalid) (Element0 p pvalid) =
  Element0 (composePolyShape q p) (composePreservesValid qvalid pvalid)

infixr 1 <|
public export
(<|) : Polynomial -> Polynomial -> Polynomial
(<|) = composePoly

infixr 1 |>
public export
(|>) : Polynomial -> Polynomial -> Polynomial
(|>) = flip (<|)

public export
iterNPolyShape : Nat -> PolyShape -> PolyShape
iterNPolyShape Z _ = idPolyShape
iterNPolyShape (S n) p = composePolyShape p (iterNPolyShape n p)

public export
iterNPreservesValid : {0 n : Nat} -> {0 poly : PolyShape} ->
  ValidPoly poly -> ValidPoly (iterNPolyShape n poly)
iterNPreservesValid {n} {poly} valid = ?iterNPolyShapeCorrect_hole

public export
iterNPoly : Nat -> Polynomial -> Polynomial
iterNPoly n (Element0 poly valid) =
  Element0 (iterNPolyShape n poly) (iterNPreservesValid valid)

public export
psSumOverIdx : (Nat -> PolyShape) -> PolyShape -> PolyShape
psSumOverIdx f = psPosFold (const $ addPolyShape . f) initialPolyShape

public export
psProductOverIdx : (Nat -> PolyShape) -> PolyShape -> PolyShape
psProductOverIdx f = psPosFold (const $ mulPolyShape . f) terminalPolyShape

public export
polyShapeClosure :
  (PolyShape -> PolyShape -> PolyShape) -> PolyShape -> PolyShape -> PolyShape
polyShapeClosure f q r =
  psProductOverIdx (composePolyShape r . f idPolyShape . constPolyShape) q

public export
polyShapeHomObj : PolyShape -> PolyShape -> PolyShape
polyShapeHomObj = polyShapeClosure addPolyShape

public export
polyShapeExponential : PolyShape -> PolyShape -> PolyShape
polyShapeExponential = flip polyShapeHomObj

public export
parProdClosureShape : PolyShape -> PolyShape -> PolyShape
parProdClosureShape = polyShapeClosure mulPolyShape

public export
leftCoclosureShape : PolyShape -> PolyShape -> PolyShape
leftCoclosureShape r p = psSumOverIdx (homNPolyShape . psInterpNat r) p

--------------------------
--------------------------
---- Polynomial types ----
--------------------------
--------------------------

public export
NatRange : Type
NatRange = (Nat, Nat)

public export
validRange : DecPred NatRange
validRange (m, n) = m <= n

public export
betweenPred : Nat -> Nat -> DecPred Nat
betweenPred min max n = (min <= n) && (n <= max)

public export
BetweenTrue : Nat -> Nat -> Nat -> Type
BetweenTrue min max n = IsTrue (betweenPred min max n)

-- All natural numbers between `min` and `max` inclusive.
public export
RangedNat : Nat -> Nat -> Type
RangedNat min max = Refinement (betweenPred min max)

public export
MkRangedNat : {0 min, max : Nat} ->
  (m : Nat) -> {auto 0 between : BetweenTrue min max m} -> RangedNat min max
MkRangedNat m {between} = MkRefinement m {satisfies=between}

public export
psInterpRange : PolyShape -> NatRange -> NatRange
psInterpRange = mapHom {f=Pair} . psInterpNat

public export
polyInterpRange : Polynomial -> NatRange -> NatRange
polyInterpRange = psInterpRange . shape

public export
idPSCorrect : (0 range : NatRange) ->
  psInterpRange PolyCat.idPolyShape range = range
idPSCorrect (min, max) = ?idPsCorrect_hole

--------------------------------
---- Morphisms on RangedNat ----
--------------------------------

public export
data RangedNatMorphF : Type -> Type where
  RNMPolyF : {0 carrier : Type} ->
    NatRange -> PolyShape -> RangedNatMorphF carrier
  RNMSwitchF : {0 carrier : Type} ->
    Nat -> carrier -> carrier -> RangedNatMorphF carrier
  RNMDivF : {0 carrier : Type} ->
    NatRange -> Nat -> RangedNatMorphF carrier
  RNMModF : {0 carrier : Type} ->
    NatRange -> Nat -> RangedNatMorphF carrier
  RNMExtendLF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier
  RNMExtendRF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier

public export
Functor RangedNatMorphF where
  map m (RNMPolyF dom ps) = RNMPolyF dom ps
  map m (RNMSwitchF n l r) = RNMSwitchF n (m l) (m r)
  map m (RNMDivF dom n) = RNMDivF dom n
  map m (RNMModF dom n) = RNMModF dom n
  map m (RNMExtendLF f n) = RNMExtendLF (m f) n
  map m (RNMExtendRF f n) = RNMExtendRF (m f) n

public export
RNMSig : Type
RNMSig = (NatRange, NatRange)

public export
RNMAlg : Type -> Type
RNMAlg = FAlg RangedNatMorphF

public export
RNMPairAlg : Type -> Type
RNMPairAlg = PairFAlg RangedNatMorphF

public export
rnmShowAlg : RNMAlg String
rnmShowAlg (RNMPolyF dom ps) =
  show ps ++ " : (" ++ show dom ++ " -> " ++ show (psInterpRange ps dom) ++ ")"
rnmShowAlg (RNMSwitchF n left right) =
  left ++ " | < " ++ show n ++ "<= | " ++ right
rnmShowAlg (RNMDivF range n) = show range ++ " / " ++ show n
rnmShowAlg (RNMModF range n) = show range ++ " % " ++ show n
rnmShowAlg (RNMExtendLF rnm n) = rnm ++ " < " ++ show n
rnmShowAlg (RNMExtendRF rnm n) = rnm ++ " > " ++ show n

public export
showRNMF : {0 x : Type} -> (shx : x -> String) -> RangedNatMorphF x -> String
showRNMF = (.) rnmShowAlg . map

public export
Show carrier => Show (RangedNatMorphF carrier) where
  show = showRNMF show

public export
MuRNM : Type
MuRNM = MuF RangedNatMorphF

public export
rnmCata : FromInitialFAlg RangedNatMorphF
rnmCata x alg (InFreeM $ InTF $ Left v) = void v
rnmCata x alg (InFreeM $ InTF $ Right c) = alg $ case c of
  RNMPolyF dom ps => RNMPolyF dom ps
  RNMSwitchF n l r => RNMSwitchF n (rnmCata x alg l) (rnmCata x alg r)
  RNMDivF dom n => RNMDivF dom n
  RNMModF dom n => RNMModF dom n
  RNMExtendLF f n => RNMExtendLF (rnmCata x alg f) n
  RNMExtendRF f n => RNMExtendRF (rnmCata x alg f) n

public export
rnmPairCata : FromInitialPairFAlg RangedNatMorphF
rnmPairCata = muPairCata rnmCata

public export
rnmCheckAlg : RNMAlg (Maybe RNMSig)
rnmCheckAlg (RNMPolyF dom ps) =
  if validRange dom && validPoly ps then
    Just $ (dom, psInterpRange ps dom)
  else
    Nothing
rnmCheckAlg (RNMSwitchF n left right) = case (left, right) of
  (Just ((domLeftMin, domLeftMax), codLeft),
   Just ((domRightMin, domRightMax), codRight)) =>
    if (S domLeftMax == n) && (domRightMin == n) && (codLeft == codRight) then
      Just ((domLeftMin, domRightMax), codLeft)
    else
      Nothing
  _ => Nothing
rnmCheckAlg (RNMDivF dom@(min, max) n) =
  case (validRange dom, divMaybe min n, divMaybe max n) of
    (True, Just min', Just max') =>
      Just (dom, (min', max'))
    _ => Nothing
rnmCheckAlg (RNMModF dom@(min, max) n) =
  if (validRange dom) && (n /= 0) && (n < max) then
    Just (dom, (0, pred n))
  else
    Nothing
rnmCheckAlg (RNMExtendLF f n) = case f of
  Just (dom, (min, max)) => if n < min then Just (dom, (n, max)) else Nothing
  Nothing => Nothing
rnmCheckAlg (RNMExtendRF f n) = case f of
  Just (dom, (min, max)) => if max < n then Just (dom, (min, n)) else Nothing
  Nothing => Nothing

public export
rnmCheck : MuRNM -> Maybe RNMSig
rnmCheck = rnmCata _ rnmCheckAlg

public export
Show MuRNM where
  show = rnmCata _ rnmShowAlg

public export
validRNM : DecPred MuRNM
validRNM = isJust . rnmCheck

public export
ValidRNM : MuRNM -> Type
ValidRNM = IsTrue . validRNM

public export
RefRNM : Type
RefRNM = Refinement validRNM

public export
MkRefRNM : (rnm : MuRNM) -> {auto 0 valid : ValidRNM rnm} -> RefRNM
MkRefRNM rnm {valid} = MkRefinement rnm {satisfies=valid}

public export
rnmRange : RefRNM -> RNMSig
rnmRange (Element0 rnm valid) with (rnmCheck rnm)
  rnmRange (Element0 rnm Refl) | Just range = range
  rnmRange (Element0 rnm Refl) | Nothing impossible

public export
RNMPoly : NatRange -> PolyShape -> MuRNM
RNMPoly = InFCom .* RNMPolyF

public export
RNMSwitch : Nat -> MuRNM -> MuRNM -> MuRNM
RNMSwitch = InFCom .** RNMSwitchF

public export
RNMDiv : NatRange -> Nat -> MuRNM
RNMDiv = InFCom .* RNMDivF

public export
RNMMod : NatRange -> Nat -> MuRNM
RNMMod = InFCom .* RNMModF

public export
RNMExtendL : MuRNM -> Nat -> MuRNM
RNMExtendL = InFCom .* RNMExtendLF

public export
RNMExtendR : MuRNM -> Nat -> MuRNM
RNMExtendR = InFCom .* RNMExtendRF

public export
rnmId : NatRange -> MuRNM
rnmId range = RNMPoly range idPolyShape

public export
interpRNMAlg : RNMAlg (Nat -> Nat)
interpRNMAlg (RNMPolyF dom ps) = psInterpNat ps
interpRNMAlg (RNMSwitchF n left right) = \m => if m < n then left m else right m
interpRNMAlg (RNMDivF dom n) =
  \m => case divMaybe m n of
    Just p => p
    Nothing => 0
interpRNMAlg (RNMModF dom n) =
  \m => case modMaybe m n of
    Just p => p
    Nothing => 0
interpRNMAlg (RNMExtendLF f n) = f
interpRNMAlg (RNMExtendRF f n) = f

public export
interpRNM : MuRNM -> Nat -> Nat
interpRNM = rnmCata _ interpRNMAlg

-------------------------------------
-------------------------------------
---- Bounded (finite) data types ----
-------------------------------------
-------------------------------------

---------------------------------
---- Bounded natural numbers ----
---------------------------------

public export
ltTrue : Nat -> Nat -> Type
ltTrue m n = (m < n) = True

public export
lteTrue : Nat -> Nat -> Type
lteTrue m n = (m <= n) = True

public export
gtTrue : Nat -> Nat -> Type
gtTrue m n = (m > n) = True

public export
gteTrue : Nat -> Nat -> Type
gteTrue m n = (m >= n) = True

-- All natural numbers less than or equal to `n`.
public export
BoundedNat : Nat -> Type
BoundedNat = Refinement {a=Nat} . (>=)

public export
MkBoundedNat : {0 n : Nat} ->
  (m : Nat) -> {auto 0 gte : gteTrue n m} -> BoundedNat n
MkBoundedNat m {gte} = MkRefinement m {satisfies=gte}

----------------------------------------
---- Tuples (fixed-length products) ----
----------------------------------------

public export
NTuple : Type -> Nat -> Type
NTuple a n = Refinement {a=(List a)} ((==) n . length)

public export
MkNTuple : {0 a : Type} -> (l : List a) -> NTuple a (length l)
MkNTuple l = MkRefinement l {satisfies=(equalNatCorrect {m=(length l)})}

--------------------------------------------
---- Fixed-width binary natural numbers ----
--------------------------------------------

public export
FixedNat : Nat -> Type
FixedNat = NTuple Digit

public export
toNat : {0 bits : Nat} -> FixedNat bits -> Nat
toNat = toNat . shape

-----------------------
---- Bounded lists ----
-----------------------

public export
BoundedList : Type -> Nat -> Type
BoundedList a n = Refinement {a=(List a)} ((>=) n . length)

public export
MkBoundedList : {0 a : Type} -> {0 n : Nat} ->
  (l : List a) -> {auto 0 gte : gteTrue n (length l)} -> BoundedList a n
MkBoundedList l {gte} = MkRefinement l {satisfies=gte}

-------------------------------------------
---- Natural transformations in `Poly` ----
-------------------------------------------

public export
record PolyShapeNT (p, q : PolyShape) where
  constructor MkPSNT

public export
PolyNT : Polynomial -> Polynomial -> Type
PolyNT p q = PolyShapeNT (shape p) (shape q)

public export
applyPSNT : {p, q : PolyShape} ->
  PolyShapeNT p q -> (range : NatRange) -> PolyShape
applyPSNT {p} {q} alpha range = ?applyPSNT_hole

public export
applyPolyNT : {p, q : Polynomial} ->
  PolyNT p q -> (range : NatRange) -> Polynomial
applyPolyNT {p} {q} alpha range = ?applyPolyNT_hole

public export
interpPSNT : {p, q : PolyShape} -> PolyShapeNT p q ->
  (min, max : Nat) ->
  RangedNat (psInterpNat p min) (psInterpNat p max) ->
  RangedNat (psInterpNat q min) (psInterpNat q max)
interpPSNT {p} {q} alpha min max n = ?interpPSNT_hole

public export
interpPolyNT : {p, q : Polynomial} -> PolyNT p q ->
  (min, max : Nat) ->
  RangedNat (polyInterpNat p min) (polyInterpNat p max) ->
  RangedNat (polyInterpNat q min) (polyInterpNat q max)
interpPolyNT {p} {q} alpha min max n =
  interpPSNT {p=(shape p)} {q=(shape q)} alpha min max n

---------------------------------------------------------
---------------------------------------------------------
---- Compilation target category (simplified VampIR) ----
---------------------------------------------------------
---------------------------------------------------------

public export
CircuitObj : Type
CircuitObj = NatRange

public export
interpCircuitObj : CircuitObj -> Type
interpCircuitObj (min, max) = RangedNat min max

public export
data CircuitMorphism : CircuitObj -> CircuitObj -> Type where
  CMPoly :
    {dom : CircuitObj} -> (poly : Polynomial) ->
    CircuitMorphism dom (polyInterpRange poly dom)

public export
cmDomain : {dom : CircuitObj} -> {0 cod : CircuitObj} ->
  CircuitMorphism dom cod -> CircuitObj
cmDomain {dom} {cod} _ = dom

public export
cmCodomain : {0 dom : CircuitObj} -> {cod : CircuitObj} ->
  CircuitMorphism dom cod -> CircuitObj
cmCodomain {dom} {cod} _ = cod

public export
cmPoly : {0 dom, cod : CircuitObj} -> CircuitMorphism dom cod -> Polynomial
cmPoly (CMPoly poly) = poly

public export
MkCircuitPolyMorphism :
  {dom : CircuitObj} -> (ps : PolyShape) -> {auto 0 valid : ValidPoly ps} ->
  CircuitMorphism dom (psInterpRange ps dom)
MkCircuitPolyMorphism {dom} ps {valid} =
  CMPoly {dom} $ MkPolynomial ps {valid}

public export
cmShow : {dom, cod : CircuitObj} -> CircuitMorphism dom cod -> String
cmShow {dom} {cod} poly =
  "[" ++ show (cmDomain poly) ++ " -> " ++ show (cmCodomain poly) ++ "]: " ++
  show (cmPoly poly)

public export
interpCircuitMorphism :
  {dom, cod : CircuitObj} -> CircuitMorphism dom cod -> NatRange -> NatRange
interpCircuitMorphism (CMPoly poly) = polyInterpRange poly

{-
public export
(dom : CircuitObj) => (cod : CircuitObj) => Show (CircuitMorphism dom cod) where
  show {dom} {cod} poly = cmShow {dom} {cod} poly
  -}

-------------------------------------------------------------------
-------------------------------------------------------------------
---- Compilation source category (with user-defined datatypes) ----
-------------------------------------------------------------------
-------------------------------------------------------------------

public export
UserObj : Type
UserObj = Polynomial

public export
compileUserObj : UserObj -> CircuitObj -> CircuitObj
compileUserObj = polyInterpRange

public export
UserMorphism : UserObj -> UserObj -> Type
UserMorphism = PolyNT

public export
interpUserMorphism :
  {dom, cod : UserObj} ->
  UserMorphism dom cod ->
  (range : NatRange) ->
  interpCircuitObj (compileUserObj dom range) ->
  interpCircuitObj (compileUserObj cod range)
interpUserMorphism {dom} {cod} alpha range = ?interpUserMorphism_hole

public export
compileUserMorphism :
  {dom, cod : UserObj} ->
  (morphism : UserMorphism dom cod) ->
  (concreteType : CircuitObj) ->
  CircuitMorphism
    (compileUserObj dom concreteType)
    (compileUserObj cod concreteType)
compileUserMorphism {dom} {cod} morph concreteType = ?compileUserMorphism_hole
