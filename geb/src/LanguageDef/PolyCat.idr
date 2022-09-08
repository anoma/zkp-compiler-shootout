module LanguageDef.PolyCat

import Library.IdrisUtils
import Library.IdrisCategories

%default total

---------------------------------------
---------------------------------------
---- Dependent types, categorially ----
---------------------------------------
---------------------------------------

public export
SliceObj : Type -> Type
SliceObj a = a -> Type

public export
SliceFunctor : Type -> Type -> Type
SliceFunctor a b = SliceObj a -> SliceObj b

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

-- If we view `a` as a discrete category, and slice objects of it as
-- functors from `a` to `Type`, then this type can also be viewed as
-- a natural transformation.
public export
SliceMorphism : {a : Type} -> SliceObj a -> SliceObj a -> Type
SliceMorphism {a} s s' = (e : a) -> s e -> s' e

public export
SliceFMorphism : {a : Type} -> SliceObj a -> (a -> a) -> Type
SliceFMorphism s f = SliceMorphism s (s . f)

public export
ArrowObj : Type
ArrowObj = (sig : (Type, Type) ** (fst sig -> snd sig))

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

public export
NatSliceMorphism : NatSliceObj -> NatSliceObj -> Type
NatSliceMorphism = SliceMorphism {a=Nat}

public export
NatSliceFMorphism : NatSliceObj -> (Nat -> Nat) -> Type
NatSliceFMorphism = SliceFMorphism {a=Nat}

public export
NatDepAlgebra : NatSliceObj -> Type
NatDepAlgebra p = (p Z, NatSliceFMorphism p S)

public export
natNonTailRecursiveIter : {0 p : Nat -> Type} ->
  NatSliceFMorphism p S -> (n, i : Nat) -> p i -> p (n + i)
natNonTailRecursiveIter {p} op Z i acc = acc
natNonTailRecursiveIter {p} op (S n) i acc =
  op (n + i) $ natNonTailRecursiveIter op n i acc

public export
natNonTailRecursiveCata : {0 p : NatSliceObj} ->
  NatDepAlgebra p -> NatPi p
natNonTailRecursiveCata (z, s) n = replace {p} (plusZeroRightNeutral n) $
  natNonTailRecursiveIter {p} s n 0 z

public export
natDepFoldIdx : {0 p : Nat -> Type} ->
  NatSliceFMorphism p S -> (n, i : Nat) -> p i -> p (n + i)
natDepFoldIdx op Z i acc = acc
natDepFoldIdx op (S n) i acc = replace {p} (sym (plusSuccRightSucc n i)) $
  natDepFoldIdx op n (S i) (op i acc)

public export
natDepCata : {0 p : NatSliceObj} ->
  NatDepAlgebra p -> NatPi p
natDepCata (z, s) n = replace {p} (plusZeroRightNeutral n) $
  natDepFoldIdx s n 0 z

public export
natDepCataZ : {0 p : NatSliceObj} ->
  {0 alg : NatDepAlgebra p} ->
  natDepCata {p} alg Z = fst alg
natDepCataZ {p} {alg=(_, _)} = Refl

public export
NatDepCoalgebra : NatSliceObj -> Type
NatDepCoalgebra p = NatSliceMorphism p (Maybe . p . S)

public export
natDepAna : {0 p : NatSliceObj} ->
  NatDepCoalgebra p -> NatSigma p -> Inf (Maybe (NatSigma p))
natDepAna coalg (n ** x) with (coalg n x)
  natDepAna coalg (n ** x) | Nothing = Nothing
  natDepAna coalg (n ** x) | Just x' = Delay (natDepAna coalg (S n ** x'))

public export
NatDepGenAlgebra : NatSliceObj -> Type
NatDepGenAlgebra p =
  (p Z, (n : Nat) -> ((m : Nat) -> LTE m n -> p m) -> p (S n))

public export
natDepGenIndStrengthened : {0 p : NatSliceObj} ->
  NatDepGenAlgebra p ->
  (x : Nat) -> (y : Nat) -> LTE y x -> p y
natDepGenIndStrengthened {p} (p0, pS) =
  natDepCata
    {p=(\x => (y : Nat) -> LTE y x -> p y)}
    (\n, lte => replace {p} (lteZeroIsZero lte) p0,
     \n, hyp, y, lteySn => case lteSuccEitherEqLte lteySn of
      Left eq => replace {p} (sym eq) $ pS n hyp
      Right lteyn => hyp y lteyn)

public export
natDepGenInd : {0 p : NatSliceObj} ->
  NatDepGenAlgebra p ->
  NatPi p
natDepGenInd alg k = natDepGenIndStrengthened alg k k reflexive

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

public export
NatGenAlgebra : Type -> Type
NatGenAlgebra a = (a, (n : Nat) -> ((m : Nat) -> LTE m n -> a) -> a)

public export
natGenInd : {0 a : Type} -> NatGenAlgebra a -> Nat -> a
natGenInd = natDepGenInd {p=(const a)}

-----------------------------
-----------------------------
---- Polynomial functors ----
-----------------------------
-----------------------------

-----------------------------------------------------
---- Polynomial functors as dependent sets/types ----
-----------------------------------------------------

-- A polynomial endofunctor may be viewed as a dependent type,
-- with a type family of directions dependent on a set of positions.
public export
PolyFuncDir : Type -> Type
PolyFuncDir pos = pos -> Type

public export
PolyFunc : Type
PolyFunc = DPair Type PolyFuncDir

public export
pfPos : PolyFunc -> Type
pfPos (pos ** dir) = pos

public export
pfDir : {p : PolyFunc} -> pfPos p -> Type
pfDir {p=(pos ** dir)} i = dir i

public export
InterpPolyFunc : PolyFunc -> Type -> Type
InterpPolyFunc (pos ** dir) x = (i : pos ** (dir i -> x))

public export
InterpPFMap : (p : PolyFunc) -> {0 a, b : Type} ->
  (a -> b) -> InterpPolyFunc p a -> InterpPolyFunc p b
InterpPFMap (_ ** _) m (i ** d) = (i ** m . d)

public export
(p : PolyFunc) => Functor (InterpPolyFunc p) where
  map {p} = InterpPFMap p

-- A polynomial functor may also be viewed as a slice object
-- (in the slice category of its type of positions).
-- (Similarly, it may also be viewed as an object of the
-- arrow category.)
public export
PolyFuncToSlice : (p : PolyFunc) -> SliceObj (pfPos p)
PolyFuncToSlice (pos ** dir) = dir

public export
SliceToPolyFunc : {a : Type} -> SliceObj a -> PolyFunc
SliceToPolyFunc {a} sl = (a ** sl)

--------------------------------------------------------
---- Polynomial functors with finite direction-sets ----
--------------------------------------------------------

-- A version of PolyFunc where all direction-sets are finite.
public export
PolyFuncNDir : Type -> Type
PolyFuncNDir pos = pos -> Nat

public export
PolyFuncDirFromN : {0 pos : Type} -> PolyFuncNDir pos -> PolyFuncDir pos
PolyFuncDirFromN dir = Fin . dir

public export
PolyFuncN : Type
PolyFuncN = DPair Type PolyFuncNDir

public export
pfnPos : PolyFuncN -> Type
pfnPos = fst

public export
pfnDir : (p : PolyFuncN) -> pfnPos p -> Nat
pfnDir = snd

public export
pfnDirFromN : (p : PolyFuncN) -> pfnPos p -> Type
pfnDirFromN p = PolyFuncDirFromN $ pfnDir p

public export
pfnFunc : PolyFuncN -> PolyFunc
pfnFunc p = (pfnPos p ** pfnDirFromN p)

------------------------------------------------------------
---- Natural transformations on polynomial endofunctors ----
------------------------------------------------------------

public export
PolyNatTrans : PolyFunc -> PolyFunc -> Type
PolyNatTrans (ppos ** pdir) (qpos ** qdir) =
  (onPos : ppos -> qpos ** SliceMorphism (qdir . onPos) pdir)

public export
pntOnPos : {0 p, q : PolyFunc} -> PolyNatTrans p q ->
  pfPos p -> pfPos q
pntOnPos {p=(_ ** _)} {q=(_ ** _)} (onPos ** onDir) = onPos

public export
pntOnDir : {0 p, q : PolyFunc} -> (alpha : PolyNatTrans p q) ->
  (i : pfPos p) -> pfDir {p=q} (pntOnPos {p} {q} alpha i) -> pfDir {p} i
pntOnDir {p=(_ ** _)} {q=(_ ** _)} (onPos ** onDir) = onDir

public export
InterpPolyNT : {0 p, q : PolyFunc} -> PolyNatTrans p q ->
  SliceMorphism (InterpPolyFunc p) (InterpPolyFunc q)
InterpPolyNT {p=(_ ** _)} {q=(_ ** _)} (onPos ** onDir) a (pi ** pd) =
  (onPos pi ** (pd . onDir pi))

-- A slice morphism can be viewed as a special case of a natural transformation
-- between the polynomial endofunctors as which the codomain and domain slices
-- may be viewed.  (The special case is that the on-positions function is the
-- identity.)

public export
SliceMorphismToPolyNatTrans : {0 a : Type} -> {0 s, s' : SliceObj a} ->
  SliceMorphism s s' -> PolyNatTrans (SliceToPolyFunc s') (SliceToPolyFunc s)
SliceMorphismToPolyNatTrans {a} m = (id {a} ** m)

public export
PolyNatTransToSliceMorphism : {0 p, q : PolyFunc} ->
  {eqpos : pfPos p = pfPos q} ->
  (alpha : PolyNatTrans p q) ->
  ((i : pfPos p) -> pntOnPos {p} {q} alpha i = replace {p=(\t => t)} eqpos i) ->
  SliceMorphism
    {a=(pfPos p)}
    (replace {p=(\type => type -> Type)} (sym eqpos) (PolyFuncToSlice q))
    (PolyFuncToSlice p)
PolyNatTransToSliceMorphism {p=(_ ** _)} {q=(_ ** qdir)}
  (_ ** ondir) onPosId i sp = ondir i $ replace {p=qdir} (sym (onPosId i)) sp

------------------------------------
------------------------------------
---- Polynomial-functor algebra ----
------------------------------------
------------------------------------

-----------------------------------------
---- Algebras of polynomial functors ----
-----------------------------------------

public export
PFAlg : PolyFunc -> Type -> Type
PFAlg (pos ** dir) a = (i : pos) -> (dir i -> a) -> a

public export
PFNAlg : PolyFuncN -> Type -> Type
PFNAlg (pos ** dir) a = (i : pos) -> Vect (dir i) a -> a

public export
PFAlgFromN : {0 a : Type} -> {p : PolyFuncN} ->
  PFNAlg p a -> PFAlg (pfnFunc p) a
PFAlgFromN {a} {p=(pos ** dir)} alg i = alg i . finFToVect

-------------------------------------------------
---- Initial algebras of polynomial functors ----
-------------------------------------------------

public export
data PolyFuncMu : PolyFunc -> Type where
  InPFM : {0 p : PolyFunc} ->
    (i : pfPos p) -> (pfDir {p} i -> PolyFuncMu p) -> PolyFuncMu p

public export
PolyFuncNMu : PolyFuncN -> Type
PolyFuncNMu p = PolyFuncMu (pfnFunc p)

public export
InPFMN : {0 p : PolyFuncN} ->
  (i : pfnPos p) -> Vect (pfnDir p i) (PolyFuncNMu p) -> PolyFuncNMu p
InPFMN {p=(pos ** dir)} i = InPFM i . flip index

----------------------------------------------
---- Catamorphisms of polynomial functors ----
----------------------------------------------

public export
pfCata : {0 p : PolyFunc} -> {0 a : Type} -> PFAlg p a -> PolyFuncMu p -> a
pfCata {p=p@(pos ** dir)} {a} alg (InPFM i da) =
  alg i $ \d : dir i => pfCata {p} alg $ da d

public export
pfnCata : {p : PolyFuncN} -> {0 a : Type} -> PFNAlg p a -> PolyFuncNMu p -> a
pfnCata = pfCata . PFAlgFromN

public export
partial
pfnFold : {p : PolyFuncN} -> {0 a : Type} -> PFNAlg p a -> PolyFuncNMu p -> a
pfnFold {p=p@(pos ** dir)} {a} alg = pfnFold' id where
  mutual
    pfnFold' : (a -> a) -> PolyFuncNMu p -> a
    pfnFold' cont (InPFM i da) with (dir i) proof ndir
      pfnFold' cont (InPFM i da) | pdi =
        pfnFoldMap pdi (\v => cont $ alg i $ rewrite ndir in v) $ finFToVect da

    pfnFoldMap : (n : Nat) -> (Vect n a -> a) -> Vect n (PolyFuncNMu p) -> a
    pfnFoldMap Z cont [] = cont []
    pfnFoldMap (S n) cont (e :: v) =
      pfnFoldMap n (\v' => cont $ (pfnFold' id e) :: v') v

----------------------------------
---- Polynomial (free) monads ----
----------------------------------

public export
data PFTranslatePos : PolyFunc -> Type -> Type where
  PFVar : {0 p : PolyFunc} -> {0 a : Type} -> a -> PFTranslatePos p a
  PFCom : {0 p : PolyFunc} -> {0 a : Type} -> pfPos p -> PFTranslatePos p a

public export
PFTranslateDir : (p : PolyFunc) -> (a : Type) -> PFTranslatePos p a -> Type
PFTranslateDir (pos ** dir) a (PFVar ea) = Void
PFTranslateDir (pos ** dir) a (PFCom i) = dir i

public export
PFTranslate : PolyFunc -> Type -> PolyFunc
PFTranslate p a = (PFTranslatePos p a ** PFTranslateDir p a)

public export
PolyFuncFreeMFromTranslate : PolyFunc -> Type -> Type
PolyFuncFreeMFromTranslate = PolyFuncMu .* PFTranslate

public export
PolyFuncFreeMPos : PolyFunc -> Type
PolyFuncFreeMPos p = PolyFuncFreeMFromTranslate p ()

public export
PolyFuncFreeMDirAlg : (p : PolyFunc) -> PFAlg (PFTranslate p ()) Type
PolyFuncFreeMDirAlg (pos ** dir) (PFVar ()) d = ()
PolyFuncFreeMDirAlg (pos ** dir) (PFCom i) d = DPair (dir i) d

public export
PolyFuncFreeMDir : (p : PolyFunc) -> PolyFuncFreeMPos p -> Type
PolyFuncFreeMDir p = pfCata $ PolyFuncFreeMDirAlg p

public export
PolyFuncFreeM : PolyFunc -> PolyFunc
PolyFuncFreeM p = (PolyFuncFreeMPos p ** PolyFuncFreeMDir p)

public export
InterpPolyFuncFreeM : PolyFunc -> Type -> Type
InterpPolyFuncFreeM = InterpPolyFunc . PolyFuncFreeM

public export
PolyFMInterpToTranslateCurried : (p : PolyFunc) -> (a : Type) ->
  (mpos : PolyFuncFreeMPos p) -> (PolyFuncFreeMDir p mpos -> a) ->
  PolyFuncFreeMFromTranslate p a
PolyFMInterpToTranslateCurried (pos ** dir) a (InPFM (PFVar ()) f) dircat =
  InPFM (PFVar $ dircat ()) (voidF _)
PolyFMInterpToTranslateCurried (pos ** dir) a (InPFM (PFCom i) f) dircat =
  InPFM (PFCom i) $
    \di : dir i =>
      PolyFMInterpToTranslateCurried (pos ** dir) a (f di) $
        (\d => dircat (di ** d))

public export
PolyFMInterpToTranslate : (p : PolyFunc) -> (a : Type) ->
  InterpPolyFuncFreeM p a -> PolyFuncFreeMFromTranslate p a
PolyFMInterpToTranslate p a (em ** d) = PolyFMInterpToTranslateCurried p a em d

public export
PolyFMTranslateToInterpAlg : (p : PolyFunc) -> (a : Type) ->
  (i : PFTranslatePos p a) ->
  (PFTranslateDir p a i -> InterpPolyFuncFreeM p a) ->
  InterpPolyFuncFreeM p a
PolyFMTranslateToInterpAlg (pos ** dir) a (PFVar ea) hyp =
  (InPFM (PFVar ()) (voidF _) ** const ea)
PolyFMTranslateToInterpAlg (pos ** dir) a (PFCom i) hyp =
  (InPFM (PFCom i) (fst . hyp) ** \dp => case dp of (d ** c) => snd (hyp d) c)

public export
PolyFMTranslateToInterp : (p : PolyFunc) -> (a : Type) ->
  PolyFuncFreeMFromTranslate p a -> InterpPolyFuncFreeM p a
PolyFMTranslateToInterp p a = pfCata $ PolyFMTranslateToInterpAlg p a

--------------------------------------
--------------------------------------
---- Polynomial-functor coalgebra ----
--------------------------------------
--------------------------------------

-------------------------------------------
---- Coalgebras of polynomial functors ----
-------------------------------------------

public export
PFCoalg : PolyFunc -> Type -> Type
PFCoalg (pos ** dir) a = a -> (i : pos ** (dir i -> a))

----------------------------------------------------
---- Terminal coalgebras of polynomial functors ----
----------------------------------------------------

public export
data PolyFuncNu : PolyFunc -> Type where
  InPFN : {0 p : PolyFunc} ->
    (i : pfPos p) -> (pfDir {p} i -> Inf (PolyFuncNu p)) -> PolyFuncNu p

---------------------------------------------
---- Anamorphisms of polynomial functors ----
---------------------------------------------

public export
pfAna : {0 p : PolyFunc} -> {0 a : Type} -> PFCoalg p a -> a -> PolyFuncNu p
pfAna {p=p@(pos ** dir)} {a} coalg e = case coalg e of
  (i ** da) => InPFN i $ \d : dir i => pfAna coalg $ da d

--------------------------------------
---- Polynomial (cofree) comonads ----
--------------------------------------

public export
data PFScalePos : PolyFunc -> Type -> Type where
  PFNode : {0 p : PolyFunc} -> {0 a : Type} -> a -> pfPos p -> PFScalePos p a

public export
PFScaleDir : (p : PolyFunc) -> (a : Type) -> PFScalePos p a -> Type
PFScaleDir (pos ** dir) a (PFNode _ i) = dir i

public export
PFScale : PolyFunc -> Type -> PolyFunc
PFScale p a = (PFScalePos p a ** PFScaleDir p a)

public export
PolyFuncCofreeCMFromScale : PolyFunc -> Type -> Type
PolyFuncCofreeCMFromScale = PolyFuncNu .* PFScale

-----------------------
-----------------------
---- Refined types ----
-----------------------
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
Refinement : {a : Type} -> (0 pred : DecPred a) -> Type
Refinement {a} p = Subset0 a (Satisfies p)

public export
refinementFstEq : {0 a : Type} -> {0 pred : DecPred a} ->
  {r, r' : Refinement pred} -> fst0 r = fst0 r' -> r = r'
refinementFstEq {r=(Element0 _ s)} {r'=(Element0 _ s')} Refl =
  rewrite uip {eq=s} {eq'=s'} in Refl

public export
TrueRefinement : Type -> Type
TrueRefinement a = Refinement (TruePred a)

public export
FalseRefinement : Type -> Type
FalseRefinement a = Refinement (FalsePred a)

public export
NotRefinement : {a : Type} -> DecPred a -> Type
NotRefinement p = Refinement (NotPred p)

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
shape = fst0

public export
VoidRefinement : DecPred Void
VoidRefinement = voidF Bool

public export
Refined : Type
Refined = Subset0 Type DecPred

public export
ErasedType : Refined -> Type
ErasedType (Element0 a _) = a

public export
0 RefinedPred : (r : Refined) -> DecPred (ErasedType r)
RefinedPred (Element0 _ p) = p

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
DecPredPair : Type -> Type
DecPredPair = ProductMonad . DecPred

public export
CoeqPred : Type -> Type
CoeqPred = DecPredPair

public export
0 coeqBase : {0 a : Type} -> (0 pred : CoeqPred a) -> DecPred a
coeqBase (pred, _) = pred

public export
0 coeqNormalized : {0 a : Type} -> (0 pred : CoeqPred a) -> DecPred a
coeqNormalized (_, norm) = norm

public export
CoeqPredF : (Type -> Type) -> Type
CoeqPredF f = (DecPredF f, DecPredF f)

public export
0 coeqFBase : {0 f : Type -> Type} -> (0 pred : CoeqPredF f) -> DecPredF f
coeqFBase (pred, _) = pred

public export
0 coeqFNormalized : {0 f : Type -> Type} -> (0 pred : CoeqPredF f) -> DecPredF f
coeqFNormalized (_, norm) = norm

public export
coeqPredF : {0 f : Type -> Type} -> {x : Type} ->
  CoeqPredF f -> CoeqPred x -> CoeqPred (f x)
coeqPredF {f} {x} (predf, normf) (pred, norm) = (predf x pred, normf x norm)

public export
0 normalized : {0 a : Type} -> (0 pred : CoeqPred a) -> DecPred a
normalized (pred, norm) = AndPred pred norm

public export
Normalized : {a : Type} -> (0 pred : CoeqPred a) -> Type
Normalized pred = Refinement (normalized pred)

public export
0 nonNormalized : {0 a : Type} -> (0 pred : CoeqPred a) -> DecPred a
nonNormalized (pred, norm) = AndNotPred pred norm

public export
NonNormalized : {a : Type} -> (0 pred : CoeqPred a) -> Type
NonNormalized pred = Refinement (nonNormalized pred)

public export
Normalizer : {a : Type} -> (0 pred : CoeqPred a) -> Type
Normalizer pred = NonNormalized pred -> Normalized pred

public export
Coequalizable : Type
Coequalizable = Subset0 Type CoeqPred

public export
coRefBase : Coequalizable -> Type
coRefBase (Element0 a _) = a

public export
0 coRefPred : (cr : Coequalizable) -> CoeqPred (coRefBase cr)
coRefPred (Element0 _ p) = p

public export
CoeqNormalizer : Coequalizable -> Type
CoeqNormalizer cr = Normalizer (coRefPred cr)

public export
Coequalized : Type
Coequalized = DPair Coequalizable CoeqNormalizer

public export
normalizedCompose :
  {0 a, b, c : Type} ->
  {pred : CoeqPred b} ->
  {fn : Normalizer pred} ->
  (g : Normalized {a=b} pred -> c) ->
  (f : a -> Refinement {a=b} (coeqBase pred)) ->
  a -> c
normalizedCompose {pred=(_, norm)} {fn} g f x = g $ case f x of
  Element0 x' satisfies => case decEq (norm x') True of
    Yes normalized => Element0 x' $ rewrite satisfies in normalized
    No nonNormalized => fn $ Element0 x' $
      rewrite satisfies in rewrite notTrueIsFalse nonNormalized in Refl

public export
coeqInject : {0 a : Type} -> {0 pred : CoeqPred b} ->
  Refinement (normalized pred) -> Refinement (coeqBase pred)
coeqInject {a} {pred=(pred, _)} (Element0 e n) = (Element0 e $ andLeft n)

public export
coeqForgetfulCompose :
  {0 a, b, c : Type} ->
  {pred : CoeqPred b} ->
  {fn : Normalizer pred} ->
  (g : Refinement {a=b} (coeqBase pred) -> c) ->
  (f : a -> Normalized {a=b} pred) ->
  a -> c
coeqForgetfulCompose g f = g . coeqInject {a=b} {pred} . f

public export
CoequalizableF : {f : Type -> Type} -> (0 _ : CoeqPredF f) ->
  Coequalizable -> Coequalizable
CoequalizableF {f} predf (Element0 x pred) =
  (Element0 (f x) $ coeqPredF {f} {x} predf pred)

public export
NormalizerF : {f : Type -> Type} -> (0 predf : CoeqPredF f) -> Type
NormalizerF predf = (a : Coequalizable) ->
  CoeqNormalizer a -> CoeqNormalizer (CoequalizableF {f} predf a)

public export
CoequalizedF :
  {f : Type -> Type} ->
  {predf : CoeqPredF f} ->
  (normalizerf : NormalizerF {f} predf) ->
  Coequalized -> Coequalized
CoequalizedF {f} {predf} normalizerf (a ** fn) =
  (CoequalizableF {f} predf a ** normalizerf a fn)

--------------------------------------
---- Algebras of refined functors ----
--------------------------------------

public export
0 PreservesRefinement : {a, b : Type} ->
  (0 pa : DecPred a) -> (0 pb : DecPred b) -> (a -> b) -> Type
PreservesRefinement {a} {b} pa pb m =
  (e : a) -> (0 satisfies : Satisfies pa e) -> Satisfies pb (m e)

public export
RefinedMorphism : Refined -> Refined -> Type
RefinedMorphism (Element0 a pa) (Element0 b pb) =
  Subset0 (a -> b) (PreservesRefinement pa pb)

public export
0 IsRefinedFunctor :
  {0 f : Type -> Type} -> {0 isF : Functor f} -> (0 pf : DecPredF f) -> Type
IsRefinedFunctor {f} {isF} pf =
  (0 a, b : Type) -> (0 pa : DecPred a) -> (0 pb : DecPred b) ->
  (0 m : a -> b) -> (0 _ : PreservesRefinement pa pb m) ->
  PreservesRefinement (pf a pa) (pf b pb) (map {f} m)

public export
RefinedFMap : {0 f : Type -> Type} -> {isF : Functor f} ->
  (0 pf : DecPredF f) ->
  {auto 0 isRF : IsRefinedFunctor {f} {isF} pf} ->
  {0 a, b : Refined} ->
  RefinedMorphism a b ->
  RefinedMorphism (RefinedF pf a) (RefinedF pf b)
RefinedFMap
  {f} {isF} {isRF} pf {a=(Element0 a pa)} {b=(Element0 b pb)} (Element0 m pr) =
    (Element0 (map {f} m) $ isRF a b pa pb m pr)

public export
RefinedAlg : {f : Type -> Type} -> DecPredF f -> Refined -> Type
RefinedAlg {f} pf x = RefinedMorphism (RefinedF pf x) x

public export
RefinedCoalg : {f : Type -> Type} -> DecPredF f -> Refined -> Type
RefinedCoalg {f} pf x = RefinedMorphism x (RefinedF pf x)

public export
CoequalizableMorphism : Coequalizable -> Coequalizable -> Type
CoequalizableMorphism (Element0 a apred) (Element0 b bpred) =
  Subset0 (a -> b) (PreservesRefinement (coeqNormalized apred) (coeqBase bpred))

public export
CoequalizedMorphism : Coequalized -> Coequalized -> Type
CoequalizedMorphism (a ** _) (b ** _) = CoequalizableMorphism a b

public export
0 PreservesCoeqPred : {a, b : Type} ->
  (0 pa : CoeqPred a) -> (0 pb : CoeqPred b) ->
  (a -> b) -> Type
PreservesCoeqPred pa pb = PreservesRefinement (coeqNormalized pa) (coeqBase pb)

public export
0 PreservesNormalization : {a : Type} ->
  (0 pa : CoeqPred a) -> (a -> a) -> Type
PreservesNormalization {a} pa =
  PreservesRefinement (coeqNormalized pa) (coeqNormalized pa)

public export
0 IsCoequalizedFunctor :
  {0 f : Type -> Type} -> {0 isF : Functor f} ->
  (0 predf : CoeqPredF f) -> Type
IsCoequalizedFunctor {f} {isF} predf =
  ((0 a, b : Type) -> (0 pa : CoeqPred a) -> (0 pb : CoeqPred b) ->
   (0 m : a -> b) -> (0 _ : PreservesCoeqPred pa pb m) ->
    PreservesCoeqPred (coeqPredF predf pa) (coeqPredF predf pb) (map {f} m),
   (0 a : Type) -> (0 pa : CoeqPred a) ->
   (0 m : a -> a) -> (0 _ : PreservesNormalization pa m) ->
    PreservesNormalization (coeqPredF predf pa) (map {f} m))

public export
CoequalizableFMap : {0 f : Type -> Type} ->
  {auto isF : Functor f} ->
  (0 predf : CoeqPredF f) ->
  {auto 0 isCF : IsCoequalizedFunctor {f} {isF} predf} ->
  {0 a, b : Coequalizable} ->
  CoeqNormalizer a ->
  CoequalizableMorphism a b ->
  CoequalizableMorphism (CoequalizableF predf a) (CoequalizableF predf b)
CoequalizableFMap
  {f} {isF} {isCF} predf {a=(Element0 a pa)} {b=(Element0 b pb)} fn m =
    (Element0 (map {f} (fst0 m)) $ fst isCF a b pa pb (fst0 m) (snd0 m))

public export
CoequalizedFMap : {0 f : Type -> Type} ->
  {auto isF : Functor f} ->
  {0 predf : CoeqPredF f} ->
  {auto 0 isCF : IsCoequalizedFunctor {f} {isF} predf} ->
  (nf : NormalizerF predf) ->
  {a, b : Coequalized} ->
  CoequalizedMorphism a b ->
  CoequalizedMorphism (CoequalizedF {predf} nf a) (CoequalizedF {predf} nf b)
CoequalizedFMap
  {f} {isF} {isCF} {predf} nf {a=(a ** na)} {b=(b ** nb)} =
    CoequalizableFMap {f} {isF} predf {isCF} {a} {b} na

public export
CoeqAlg : {f : Type -> Type} -> {pf : CoeqPredF f} ->
  NormalizerF pf -> Coequalized -> Type
CoeqAlg nf x = CoequalizedMorphism (CoequalizedF nf x) x

public export
CoeqCoalg : {f : Type -> Type} -> {pf : CoeqPredF f} ->
  NormalizerF pf -> Coequalized -> Type
CoeqCoalg nf x = CoequalizedMorphism x (CoequalizedF nf x)

---------------------------------------
---------------------------------------
---- Dependent polynomial functors ----
---------------------------------------
---------------------------------------

--------------------------------------------------------------------
---- Dependent polynomials as functors between slice categories ----
--------------------------------------------------------------------

public export
SliceIdx : PolyFunc -> Type -> Type -> Type
SliceIdx p a b = (i : pfPos p) -> (pfDir {p} i -> a) -> b

public export
SlicePolyFunc : Type -> Type -> Type
SlicePolyFunc a b = (p : PolyFunc ** SliceIdx p a b)

public export
spfFunc : {0 a, b : Type} -> SlicePolyFunc a b -> PolyFunc
spfFunc = DPair.fst

public export
spfPos : {0 a, b : Type} -> SlicePolyFunc a b -> Type
spfPos = pfPos . spfFunc

public export
spfDir : {0 a, b : Type} -> {spf : SlicePolyFunc a b} -> spfPos spf -> Type
spfDir {spf} = pfDir {p=(spfFunc spf)}

public export
spfIdx : {0 a, b : Type} ->
  {spf : SlicePolyFunc a b} -> SliceIdx (spfFunc spf) a b
spfIdx {spf} = DPair.snd spf

public export
InterpSPFunc : {a, b : Type} -> SlicePolyFunc a b -> SliceObj a -> SliceObj b
InterpSPFunc {a} {b} ((pos ** dir) ** idx) sa eb =
  (i : pos **
   param : dir i -> a **
   (FunExt -> idx i param = eb,
    (d : dir i) -> sa $ param d))

public export
InterpSPFMap : {0 a, b : Type} -> (spf : SlicePolyFunc a b) ->
  {0 sa, sa' : SliceObj a} ->
  SliceMorphism sa sa' ->
  SliceMorphism (InterpSPFunc spf sa) (InterpSPFunc spf sa')
InterpSPFMap ((_ ** dir) ** _) m _ (i ** param ** (eqidx, da)) =
  (i ** param ** (eqidx, \d : dir i => m (param d) (da d)))

public export
SlicePolyEndoF : Type -> Type
SlicePolyEndoF a = SlicePolyFunc a a

-----------------------------------------------------------------------
---- Natural transformations on dependent polynomial endofunctors ----
-----------------------------------------------------------------------

public export
SPNatTransOnIdx : {x, y : Type} -> (p, q : SlicePolyFunc x y) ->
  PolyNatTrans (spfFunc p) (spfFunc q) -> Type
SPNatTransOnIdx {x} p q pnt =
  (pi : spfPos p) -> (pparam : spfDir {spf=p} pi -> x) ->
  spfIdx {spf=q} (pntOnPos pnt pi) (pparam . pntOnDir pnt pi) =
  spfIdx {spf=p} pi pparam

public export
SPNatTrans : {x, y : Type} -> SlicePolyFunc x y -> SlicePolyFunc x y -> Type
SPNatTrans {x} p q =
  (pnt : PolyNatTrans (spfFunc p) (spfFunc q) ** SPNatTransOnIdx p q pnt)

public export
spntPnt : {0 x, y : Type} -> {0 p, q : SlicePolyFunc x y} ->
  SPNatTrans p q -> PolyNatTrans (spfFunc p) (spfFunc q)
spntPnt = DPair.fst

public export
spntOnPos : {0 x, y : Type} -> {0 p, q : SlicePolyFunc x y} -> SPNatTrans p q ->
  spfPos p -> spfPos q
spntOnPos = pntOnPos . spntPnt

public export
spntOnDir : {0 x, y : Type} -> {0 p, q : SlicePolyFunc x y} ->
  (alpha : SPNatTrans p q) ->
  SliceMorphism (spfDir {spf=q} . spntOnPos {p} {q} alpha) (spfDir {spf=p})
spntOnDir alpha i = pntOnDir (spntPnt alpha) i

public export
spntOnIdx : {0 x, y : Type} -> {0 p, q : SlicePolyFunc x y} ->
  (alpha : SPNatTrans p q) -> SPNatTransOnIdx p q (spntPnt {p} {q} alpha)
spntOnIdx = DPair.snd

public export
InterpSPNT : {0 x, y : Type} -> {p, q : SlicePolyFunc x y} ->
  SPNatTrans p q -> {0 sx : SliceObj x} ->
  SliceMorphism {a=y} (InterpSPFunc p sx) (InterpSPFunc q sx)
InterpSPNT {x} {y} {p=((ppos ** pdir) ** pidx)} {q=((qpos ** qdir) ** qidx)}
  ((onPos ** onDir) ** onIdx) {sx} ey (pi ** pparam ** (extEq, pda)) =
    (onPos pi **
     pparam . onDir pi **
     (\funext => trans (onIdx pi pparam) (extEq funext),
      \qd : qdir (onPos pi) => pda $ onDir pi qd))

-----------------------------------------------
-----------------------------------------------
---- Dependent-polynomial-functors algebra ----
-----------------------------------------------
-----------------------------------------------

---------------------------------------------------
---- Algebras of dependent polynomial functors ----
---------------------------------------------------

public export
SPFAlg : {a : Type} -> SlicePolyEndoF a -> SliceObj a -> Type
SPFAlg spf sa = SliceMorphism (InterpSPFunc spf sa) sa

---------------------------------------------------
---- Initial algebras of dependent polynomials ----
---------------------------------------------------

public export
spfMu : {0 a : Type} -> SlicePolyEndoF a -> Type
spfMu = PolyFuncMu . spfFunc

public export
spfMuIdx : {0 a : Type} -> (spf : SlicePolyEndoF a) -> spfMu spf -> a
spfMuIdx (p@(pos ** dir) ** sli) = pfCata {p} sli

public export
SPFMu : {0 a : Type} -> SlicePolyEndoF a -> SliceObj a
SPFMu {a} spf@(p ** sli) ea =
  (em : PolyFuncMu p ** FunExt -> spfMuIdx spf em = ea)

public export
InSPFM : {0 a : Type} -> {spf : SlicePolyEndoF a} ->
  (i : spfPos spf) ->
  (param : spfDir {spf} i -> a) ->
  ((di : spfDir {spf} i) -> SPFMu {a} spf (param di)) ->
  SPFMu {a} spf (spfIdx {spf} i param)
InSPFM {a} {spf=spf@((pos ** dir) ** slidx)} i param sli =
  (InPFM i (\di => fst (sli di)) **
   (\funext => cong (slidx i) $ funExt $ \di => snd (sli di) funext))

--------------------------------------------------------
---- Catamorphisms of dependent polynomial functors ----
--------------------------------------------------------

public export
spfCataCurried : {0 a : Type} -> {spf : SlicePolyEndoF a} ->
  {0 sa : SliceObj a} -> {funext : FunExt} -> SPFAlg spf sa ->
  (ea : a) ->
  (em : PolyFuncMu (spfFunc spf)) ->
  (FunExt -> spfMuIdx {a} spf em = ea) ->
  sa ea
spfCataCurried
  {spf=((pos ** dir) ** idx)} {funext} alg ea (InPFM i param) slieq =
    case slieq funext of
      Refl =>
        alg
          ea
          (i **
          pfCata {p=(pos ** dir)} idx . param **
          (slieq,
            \di : dir i =>
              spfCataCurried {spf=((pos ** dir) ** idx)} {funext} alg
                (pfCata idx (param di)) (param di) (\_ => Refl)))

public export
spfCata : {0 a : Type} -> {spf : SlicePolyEndoF a} -> {0 sa : SliceObj a} ->
  {funext : FunExt} -> SPFAlg spf sa -> (ea : a) -> SPFMu spf ea -> sa ea
spfCata {a} {spf=spf@((_ ** _) ** _)} {sa} {funext} alg ea (em ** slieq) =
  spfCataCurried {a} {spf} {funext} alg ea em slieq

--------------------------------------------
---- Dependent polynomial (free) monads ----
--------------------------------------------

public export
SPFTranslatePos : {0 x, y : Type} -> SlicePolyFunc x y -> Type -> Type
SPFTranslatePos = PFTranslatePos . spfFunc

public export
SPFTranslateDir : {x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  SPFTranslatePos spf a -> Type
SPFTranslateDir spf a = PFTranslateDir (spfFunc spf) a

public export
SPFTranslateFunc : {x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  PolyFunc
SPFTranslateFunc spf a = (SPFTranslatePos spf a ** SPFTranslateDir spf a)

public export
SPFTranslateIdx : {0 x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  (a -> y) -> SliceIdx (SPFTranslateFunc spf a) x y
SPFTranslateIdx ((pos ** dir) ** idx) a f (PFVar v) di = f v
SPFTranslateIdx ((pos ** dir) ** idx) a f (PFCom i) di = idx i di

public export
SPFTranslate : {x, y : Type} -> SlicePolyFunc x y -> (a : Type) ->
  (a -> y) -> SlicePolyFunc x y
SPFTranslate spf a f = (SPFTranslateFunc spf a ** SPFTranslateIdx spf a f)

public export
SPFFreeMFromMu : {x : Type} -> SlicePolyEndoF x -> SliceObj x -> SliceObj x
SPFFreeMFromMu spf sx =
  SPFMu {a=x} (SPFTranslate {x} {y=x} spf (Sigma sx) DPair.fst)

-------------------------------------------------
-------------------------------------------------
---- Dependent-polynomial-functors coalgebra ----
-------------------------------------------------
-------------------------------------------------

-----------------------------------------------------
---- Coalgebras of dependent polynomial functors ----
-----------------------------------------------------

public export
SPFCoalg : {a : Type} -> SlicePolyEndoF a -> SliceObj a -> Type
SPFCoalg spf sa = SliceMorphism sa (InterpSPFunc spf sa)

------------------------------------------------------
---- Terminal coalgebras of dependent polynomials ----
------------------------------------------------------

public export
data SPFNu : {0 a : Type} -> SlicePolyEndoF a -> SliceObj a where
  InSPFN : {0 a : Type} -> {0 spf : SlicePolyEndoF a} ->
    (i : spfPos spf) ->
    (param : spfDir {spf} i -> a) ->
    ((di : spfDir {spf} i) -> Inf (SPFNu {a} spf (param di))) ->
    SPFNu {a} spf (spfIdx {spf} i param)

-------------------------------------------------------
---- Anamorphisms of dependent polynomial functors ----
-------------------------------------------------------

public export
spfAna : {0 a : Type} -> {spf : SlicePolyEndoF a} -> {0 sa : SliceObj a} ->
  {funext : FunExt} -> SPFCoalg spf sa -> (ea : a) -> sa ea -> SPFNu spf ea
spfAna {a} {spf=((pos ** dir) ** idx)} {sa} {funext} coalg ea esa =
  case coalg ea esa of
    (i ** param ** (extEq, da)) => case (extEq funext) of
      Refl =>
        InSPFN {spf=((pos ** dir) ** idx)} i param $
          \di : dir i => spfAna {funext} coalg (param di) (da di)

------------------------------------------------
---- Dependent polynomial (cofree) comonads ----
------------------------------------------------

public export
SPFScalePos : {0 x, y : Type} -> SlicePolyFunc x y -> Type -> Type
SPFScalePos = PFScalePos . spfFunc

public export
SPFScaleDir : {x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  SPFScalePos spf a -> Type
SPFScaleDir spf a = PFScaleDir (spfFunc spf) a

public export
SPFScaleFunc : {x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  PolyFunc
SPFScaleFunc spf a = (SPFScalePos spf a ** SPFScaleDir spf a)

public export
SPFScaleIdx : {0 x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  (a -> y -> y) -> SliceIdx (SPFScaleFunc spf a) x y
SPFScaleIdx {x} {y} ((pos ** dir) ** idx) a f (PFNode l i) di = f l (idx i di)

public export
SPFScale : {x, y : Type} -> SlicePolyFunc x y -> (a : Type) ->
  (a -> y -> y) -> SlicePolyFunc x y
SPFScale spf a f = (SPFScaleFunc spf a ** SPFScaleIdx spf a f)

public export
SPFCofreeCMFromNu : {x : Type} -> SlicePolyEndoF x -> SliceObj x -> SliceObj x
SPFCofreeCMFromNu spf sx =
  SPFNu {a=x} (SPFScale {x} {y=x} spf (Sigma sx) (const id))

----------------------------------------------------------------
----------------------------------------------------------------
---- Polynomial types with functors separated for iteration ----
----------------------------------------------------------------
----------------------------------------------------------------

-- The positions (constructors with parameters) of the polynomial endofunctor
-- which generates finite object-language types.
public export
data FinTPos : Type where
  FTPInitial : FinTPos
  FTPTerminal : FinTPos
  FTPCoproduct : FinTPos
  FTPProduct : FinTPos

-- The directions (or powers, or recursive fields) of the constructors of the
-- polynomial endofunctor which generates finite object-language types.
public export
data FinTDir : FinTPos -> Type where
  FTDLeft : FinTDir FTPCoproduct
  FTDRight : FinTDir FTPCoproduct
  FTDFst : FinTDir FTPProduct
  FTDSnd : FinTDir FTPProduct

public export
FTDirInitial : {0 a : FinTDir FTPInitial -> Type} ->
  (d : FinTDir FTPInitial) -> a d
FTDirInitial _ impossible

public export
FTDirTerminal : {0 a : FinTDir FTPTerminal -> Type} ->
  (d : FinTDir FTPTerminal) -> a d
FTDirTerminal _ impossible

public export
FTDirCoproduct : {0 a : FinTDir FTPCoproduct -> Type} ->
  a FTDLeft -> a FTDRight -> (d : FinTDir FTPCoproduct) -> a d
FTDirCoproduct l r FTDLeft = l
FTDirCoproduct l r FTDRight = r

public export
FTDirProduct : {0 a : FinTDir FTPProduct -> Type} ->
  a FTDFst -> a FTDSnd -> (d : FinTDir FTPProduct) -> a d
FTDirProduct f s FTDFst = f
FTDirProduct f s FTDSnd = s

-- The polynomial endofunctor which generates finite object-language types.
public export
FinTPolyF : PolyFunc
FinTPolyF = (FinTPos ** FinTDir)

-- The metalanguage form of the above functor.
public export
FinTObjF : Type -> Type
FinTObjF = InterpPolyFunc FinTPolyF

-- The type of finite object-language types, generated as a fixed point
-- of `FinTObjF`.
public export
FinTObj : Type
FinTObj = PolyFuncMu FinTPolyF

-- Compute the depth index of a type generated by `FinTPolyF`.
public export
FinTPolyIdx : SliceIdx FinTPolyF Nat Nat
FinTPolyIdx FTPInitial di = 1
FinTPolyIdx FTPTerminal di = 1
FinTPolyIdx FTPCoproduct di = smax (di FTDLeft) (di FTDRight)
FinTPolyIdx FTPProduct di = smax (di FTDFst) (di FTDSnd)

-- The dependent (indexed) polynomial endofunctor (on the slice category of
-- `Type` over `Nat`) which generates depth-indexed finite object-language
-- types.
public export
FinTSPF : SlicePolyFunc Nat Nat
FinTSPF = (FinTPolyF ** FinTPolyIdx)

-- The metalanguage form of the above functor.
public export
FinTObjSF : SliceFunctor Nat Nat
FinTObjSF = InterpSPFunc FinTSPF

-- The type of depth-indexed finite object-language types, generated as a
-- fixed point of `FinTObjSF`.
public export
FinTFNew : SliceObj Nat
FinTFNew = SPFMu FinTSPF

-- Utility functions for producing terms of type `FinTFNew`.
public export
FTFNInitial : FinTFNew 1
FTFNInitial = (InPFM FTPInitial FTDirInitial ** \_ => Refl)

public export
FTFNTerminal : FinTFNew 1
FTFNTerminal = (InPFM FTPTerminal FTDirTerminal ** \_ => Refl)

public export
FTFNCoproduct : {m, n : Nat} ->
  FinTFNew m -> FinTFNew n -> FinTFNew (smax m n)
FTFNCoproduct {m} {n} (x ** xeq) (y ** yeq) =
  (InPFM FTPCoproduct (FTDirCoproduct x y) **
   \funext => cong S $ rewrite xeq funext in rewrite yeq funext in Refl)

public export
FTFNProduct : {m, n : Nat} ->
  FinTFNew m -> FinTFNew n -> FinTFNew (smax m n)
FTFNProduct {m} {n} (x ** xeq) (y ** yeq) =
  (InPFM FTPProduct (FTDirProduct x y) **
   \funext => cong S $ rewrite xeq funext in rewrite yeq funext in Refl)

-- The type of types generated by any of up to `N` iterations of
-- the object-language-type-generating metalanguage functor.
public export
FinTFDepth : Nat -> Type
FinTFDepth n = (m : Nat ** (LTE m n, FinTFNew m))

public export
minDepth : {0 n : Nat} -> FinTFDepth n -> Nat
minDepth (m ** _) = m

public export
depthLTE : {0 n : Nat} -> (type : FinTFDepth n) -> LTE (minDepth type) n
depthLTE (_ ** (lte, _)) = lte

public export
FinType : {0 n : Nat} -> (type : FinTFDepth n) -> FinTFNew (minDepth type)
FinType (_ ** (_, type)) = type

-- A type that can be generated at a given depth can also be generated
-- at any greater depth.
public export
FinTFPromote : {n, m : Nat} -> FinTFDepth n -> LTE n m -> FinTFDepth m
FinTFPromote {n} {m} (m' ** (ltem'n, type)) ltenm =
  (m' ** (transitive ltem'n ltenm, type))

public export
FinTFPromoteMax : {n, m : Nat} -> FinTFDepth n -> FinTFDepth (maximum n m)
FinTFPromoteMax {n} {m} dtype =
  FinTFPromote {n} {m=(maximum n m)} dtype $ maxLTELeft n m

public export
FinPromoteLeft : {m, n : Nat} -> FinTFNew m -> FinTFDepth (maximum m n)
FinPromoteLeft type = (m ** (maxLTELeft m n, type))

public export
FinPromoteRight : {m, n : Nat} -> FinTFNew n -> FinTFDepth (maximum m n)
FinPromoteRight type = (n ** (maxLTERight m n, type))

public export
depthNotZero : {0 n : Nat} -> {funext : FunExt} -> FinTFNew n -> Not (n = 0)
depthNotZero {n} {funext} ((InPFM FTPInitial f) ** sleq) =
  \eq => case sleq funext of Refl => case eq of Refl impossible
depthNotZero {n} {funext} ((InPFM FTPTerminal f) ** sleq) =
  \eq => case sleq funext of Refl => case eq of Refl impossible
depthNotZero {n} {funext} ((InPFM FTPCoproduct f) ** sleq) =
  \eq => case sleq funext of Refl => case eq of Refl impossible
depthNotZero {n} {funext} ((InPFM FTPProduct f) ** sleq) =
  \eq => case sleq funext of Refl => case eq of Refl impossible

public export
depth0Void : {funext : FunExt} -> FinTFNew 0 -> Void
depth0Void {funext} em = depthNotZero {funext} em Refl

public export
depth0ExFalso : {funext : FunExt} -> {0 a : Type} -> FinTFNew 0 -> a
depth0ExFalso {funext} type = void (depth0Void {funext} type)

-- The signature of the induction principle for `FinTFNew`.
public export
FinTFNewIndAlg : ((n : Nat) -> FinTFNew n -> Type) -> Type
FinTFNewIndAlg a =
  (n : Nat) ->
  ((type : FinTFDepth n) -> a (minDepth type) (FinType type)) ->
  (type : FinTFNew (S n)) ->
  a (S n) type

public export
FinTFNewIndAlgStrengthened :
  {0 a : (n : Nat) -> FinTFNew n -> Type} ->
  FinTFNewIndAlg a ->
  (n : Nat) ->
  ((m : Nat) -> LTE m n -> (type : FinTFNew m) -> a m type) ->
  (type : FinTFNew (S n)) ->
  a (S n) type
FinTFNewIndAlgStrengthened alg n hyp =
  alg n $ \dtype => hyp (minDepth dtype) (depthLTE dtype) (FinType dtype)

-- Induction on `FinTFNew`.
public export
finTFNewInd : {funext : FunExt} -> {0 a : (n : Nat) -> FinTFNew n -> Type} ->
  FinTFNewIndAlg a -> (n : Nat) -> (type : FinTFNew n) -> a n type
finTFNewInd {funext} {a} alg =
  natDepGenInd
    (\type => depth0ExFalso {funext} type, FinTFNewIndAlgStrengthened alg)

-- The directed colimit of the metalanguage functor that generates
-- depth-indexed object-language types.  (The directed colimit is also known
-- as the initial algebra.)
public export
MuFinTF : Type
MuFinTF = DPair Nat FinTFNew

-- Every `FinTFDepth` is a `MuFinTF`.
public export
TFDepthToMu : {n : Nat} -> FinTFDepth n -> MuFinTF
TFDepthToMu {n} (m ** (lte, type)) = (m ** type)

-- Morphisms from the terminal object to a given object.  This
-- hom-set is isomorphic to the object itself.  From the perspective
-- of (dependent) types, these are the terms of the object/type.
public export
data FinTFNewTermAlg : FinTFNewIndAlg (\_, _ => Type) where
  FTTUnit :
    {0 hyp : FinTFDepth Z -> Type} ->
    FinTFNewTermAlg Z hyp FTFNTerminal
  FTTLeft :
    {0 m, n : Nat} -> {0 hyp : FinTFDepth (maximum m n) -> Type} ->
    {0 x : FinTFNew m} -> {0 y : FinTFNew n} ->
    hyp (FinPromoteLeft {n} x) ->
    FinTFNewTermAlg (maximum m n) hyp (FTFNCoproduct x y)
  FTTRight :
    {0 m, n : Nat} -> {0 hyp : FinTFDepth (maximum m n) -> Type} ->
    {0 x : FinTFNew m} -> {0 y : FinTFNew n} ->
    hyp (FinPromoteRight {m} y) ->
    FinTFNewTermAlg (maximum m n) hyp (FTFNCoproduct x y)
  FTTPair :
    {0 m, n : Nat} -> {0 hyp : FinTFDepth (maximum m n) -> Type} ->
    {0 x : FinTFNew m} -> {0 y : FinTFNew n} ->
    hyp (FinPromoteLeft {n} x) ->
    hyp (FinPromoteRight {m} y) ->
    FinTFNewTermAlg (maximum m n) hyp (FTFNProduct x y)

public export
FinTFNewTerm : {funext : FunExt} -> (n : Nat) -> FinTFNew n -> Type
FinTFNewTerm {funext} = finTFNewInd {funext} FinTFNewTermAlg

-- Generate the exponential object of a pair of finite unrefined objects.
public export
FinExpObjF : (n : Nat) ->
  (FinTFDepth n -> MuFinTF -> MuFinTF) -> FinTFNew (S n) -> MuFinTF -> MuFinTF
FinExpObjF n morph type cod = ?FinExpObjF_hole

public export
FinNewExpObj : {funext : FunExt} ->
  {m, n : Nat} -> FinTFNew m -> FinTFNew n -> MuFinTF
FinNewExpObj {funext} {m} {n} tm tn =
  finTFNewInd
    {funext} {a=(\_, _ => MuFinTF -> MuFinTF)} FinExpObjF m tm (n ** tn)

public export
FinDepthExpObj : {funext : FunExt} ->
  {m, n : Nat} -> FinTFDepth m -> FinTFDepth n -> MuFinTF
FinDepthExpObj {funext} (m ** (_, tm)) (n ** (_, tn)) =
  FinNewExpObj {funext} tm tn

public export
MuFinExpObj : {funext : FunExt} -> MuFinTF -> MuFinTF -> MuFinTF
MuFinExpObj {funext} (m ** tm) (n ** tn) = FinNewExpObj {funext} tm tn

-- Generate the morphisms out of a given finite unrefined type of
-- a given depth, given the morphisms out of all unrefined types of
-- lesser depths.
public export
FinNewMorphF : (n : Nat) ->
  (FinTFDepth n -> MuFinTF -> Type) -> FinTFNew (S n) -> MuFinTF -> Type
FinNewMorphF n morph type cod = ?FinNewMorphF_hole

public export
FinNewMorph : {funext : FunExt} ->
  {m, n : Nat} -> FinTFNew m -> FinTFNew n -> Type
FinNewMorph {funext} {m} {n} tm tn =
  finTFNewInd
    {funext} {a=(\_, _ => MuFinTF -> Type)} FinNewMorphF m tm (n ** tn)

public export
FinDepthMorph : {funext : FunExt} ->
  {m, n : Nat} -> FinTFDepth m -> FinTFDepth n -> Type
FinDepthMorph {funext} (m ** (_, tm)) (n ** (_, tn)) =
  FinNewMorph {funext} tm tn

public export
MuFinMorph : {funext : FunExt} -> MuFinTF -> MuFinTF -> Type
MuFinMorph {funext} (m ** tm) (n ** tn) = FinNewMorph {funext} tm tn

------------------------
------------------------
---- F-(co)algebras ----
------------------------
------------------------

public export
data TranslateF : (0 f : Type -> Type) -> (0 a, x : Type) -> Type where
  InVar : {0 f : Type -> Type} -> {0 a, x : Type} ->
    a -> TranslateF f a x
  InCom : {0 f : Type -> Type} -> {0 a, x : Type} ->
    f x -> TranslateF f a x

public export
data LinearF : (0 f : Type -> Type) -> (0 a, x : Type) -> Type where
  InNode : {0 f : Type -> Type} -> {0 a, x : Type} ->
    a -> f x -> LinearF f a x

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
InCFNode ex efx = InCofreeCM $ InNode ex efx

public export
MuF : (0 f : Type -> Type) -> Type
MuF f = FreeM f Void

public export
NuF : (0 f : Type -> Type) -> Type
NuF f = CofreeCM f Unit

public export
FAlg : (Type -> Type) -> Type -> Type
FAlg f a = f a -> a

public export
FCoalg : (Type -> Type) -> Type -> Type
FCoalg f a = a -> f a

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

--------------------------
---- Product algebras ----
--------------------------

public export
PairFAlg : (Type -> Type) -> (Type -> Type) -> Type -> Type
PairFAlg f g x = FAlg f (FAlg g x)

public export
DiagFAlg : (Type -> Type) -> Type -> Type
DiagFAlg f = PairFAlg f f

public export
MuPairCata : (Type -> Type) -> (Type -> Type) -> Type -> Type
MuPairCata f g x = PairFAlg f g x -> MuF f -> MuF g -> x

public export
MuDiagCata : (Type -> Type) -> Type -> Type
MuDiagCata f = MuPairCata f f

public export
FromInitialPairFAlg : (Type -> Type) -> (Type -> Type) -> Type
FromInitialPairFAlg f g = (x : Type) -> MuPairCata f g x

public export
FromInitialDiagFAlg : (Type -> Type) -> Type
FromInitialDiagFAlg f = FromInitialPairFAlg f f

public export
muPairCata : {f, g : Type -> Type} ->
  FromInitialFAlg f -> FromInitialFAlg g -> FromInitialPairFAlg f g
muPairCata {f} {g} cataf catag x alg ef eg =
  catag x (cataf (FAlg g x) alg ef) eg

public export
muDiagCata : {f : Type -> Type} -> FromInitialFAlg f -> FromInitialDiagFAlg f
muDiagCata {f} cata = muPairCata {f} {g=f} cata cata

----------------------------
---- Coproduct algebras ----
----------------------------

public export
EitherFAlg : (Type -> Type) -> (Type -> Type) -> Type -> Type
EitherFAlg f g x = (FAlg f x, FAlg g x)

public export
MuEitherCata : (Type -> Type) -> (Type -> Type) -> Type -> Type
MuEitherCata f g x = EitherFAlg f g x -> Either (MuF f) (MuF g) -> x

public export
FromInitialEitherFAlg : (Type -> Type) -> (Type -> Type) -> Type
FromInitialEitherFAlg f g = (x : Type) -> MuEitherCata f g x

public export
muEitherCata : {f, g : Type -> Type} ->
  FromInitialFAlg f -> FromInitialFAlg g -> FromInitialEitherFAlg f g
muEitherCata {f} {g} cataf catag x (algf, _) (Left ef) = cataf x algf ef
muEitherCata {f} {g} cataf catag x (_, algg) (Right eg) = catag x algg eg

-------------------------------------
---- Types dependent on algebras ----
-------------------------------------

-- A slice of a `MuF` type over some type `x` for which we have a
-- catamorphism and an algebra.
public export
MuSlice : {0 f : Type -> Type} -> {0 x : Type} ->
  MuCata f x -> FAlg f x -> x -> Type
MuSlice {f} {x} cata alg elemX = Subset0 (MuF f) (Equal elemX . cata alg)

public export
MuSlicePred : {0 f : Type -> Type} -> {x : Type} ->
  (cata : MuCata f x) -> (alg : FAlg f x) -> Type
MuSlicePred {f} {x} cata alg =
  (ex : x) -> MuSlice {f} {x} cata alg ex -> Type

-------------------------------
-------------------------------
---- Substitution category ----
-------------------------------
-------------------------------

--------------------------------------------------------------------
---- Inhabited types from fixed point of (metalanguage) functor ----
--------------------------------------------------------------------

-- Inhabited types only
public export
ISubstObjF : Type -> Type
ISubstObjF =
  CoproductF
    -- const Unit
  (const Unit) $
  CoproductF
  -- Coproduct
  ProductMonad
  -- Product
  ProductMonad

public export
ISOTerminalF : {0 x : Type} -> ISubstObjF x
ISOTerminalF = Left ()

public export
ISOCoproductF : {0 x : Type} -> x -> x -> ISubstObjF x
ISOCoproductF t t' = Right $ Left (t, t')

public export
ISOProductF : {0 x : Type} -> x -> x -> ISubstObjF x
ISOProductF t t' = Right $ Right (t, t')

public export
ISubstOAlg : Type -> Type
ISubstOAlg = FAlg ISubstObjF

public export
ISubstODiagAlg : Type -> Type
ISubstODiagAlg = DiagFAlg ISubstObjF

public export
FreeISubstO : (0 _ : Type) -> Type
FreeISubstO = FreeM ISubstObjF

public export
MuISubstO : Type
MuISubstO = MuF ISubstObjF

public export
ISOTerminal : {0 x : Type} -> FreeISubstO x
ISOTerminal = InFCom $ ISOTerminalF

public export
ISOCoproduct : {0 x : Type} -> FreeISubstO x -> FreeISubstO x -> FreeISubstO x
ISOCoproduct = InFCom .* ISOCoproductF

public export
ISOProduct : {0 x : Type} -> FreeISubstO x -> FreeISubstO x -> FreeISubstO x
ISOProduct = InFCom .* ISOProductF

public export
isubstOCata : FromInitialFAlg ISubstObjF
isubstOCata x alg (InFreeM (InVar v)) = void v
isubstOCata x alg (InFreeM (InCom c)) = alg $ case c of
  Left () => Left ()
  Right t => Right $ case t of
    Left (y, z) => Left (isubstOCata x alg y, isubstOCata x alg z)
    Right (y, z) => Right (isubstOCata x alg y, isubstOCata x alg z)

public export
isubstODiagCata : FromInitialDiagFAlg ISubstObjF
isubstODiagCata = muDiagCata isubstOCata

public export
ISubstOSlice : {x : Type} -> ISubstOAlg x -> x -> Type
ISubstOSlice {x} = MuSlice (isubstOCata x)

public export
ISubstOSlicePred : {x : Type} -> ISubstOAlg x -> Type
ISubstOSlicePred {x} = MuSlicePred (isubstOCata x)

---------------------------------------------------------------
---- Substitution category including initial object (Void) ----
---------------------------------------------------------------

public export
SubstObj : Type
SubstObj =
  -- Void
  Either ()
  -- Inhabited type
  MuISubstO

public export
SOInitial : SubstObj
SOInitial = Left ()

public export
SOTerminal : SubstObj
SOTerminal = Right ISOTerminal

public export
SOCoproduct : SubstObj -> SubstObj -> SubstObj
SOCoproduct (Left ()) (Left ()) = Left ()
SOCoproduct (Left ()) (Right t) = Right t
SOCoproduct (Right t) (Left ()) = Right t
SOCoproduct (Right t) (Right t') = Right $ ISOCoproduct t t'

public export
SOProduct : SubstObj -> SubstObj -> SubstObj
SOProduct (Left ()) (Left ()) = Left ()
SOProduct (Left ()) (Right _) = Left ()
SOProduct (Right _) (Left ()) = Left ()
SOProduct (Right t) (Right t') = Right $ ISOProduct t t'

---------------------------------------------
---- Properties of substitution category ----
---------------------------------------------

public export
isubstOShowAlg : ISubstOAlg String
isubstOShowAlg (Left ()) = show 1
isubstOShowAlg (Right (Left (m, n))) = "(" ++ m ++ " + " ++ n ++ ")"
isubstOShowAlg (Right (Right (m, n))) = "(" ++ m ++ " * " ++ n ++ ")"

public export
Show MuISubstO where
  show = isubstOCata String isubstOShowAlg

-- Depths of inhabited types begin at 1 -- depth 0 is the initial
-- object, before any iterations of SubstObjF have been applied,
-- and the initial object is uninhabited (it's Void).
public export
isubstODepthAlg : ISubstOAlg Nat
isubstODepthAlg (Left ()) = 1
isubstODepthAlg (Right (Left (m, n))) = S $ max m n
isubstODepthAlg (Right (Right (m, n))) = S $ max m n

public export
isubstODepth : MuISubstO -> Nat
isubstODepth = isubstOCata Nat isubstODepthAlg

public export
substODepth : SubstObj -> Nat
substODepth = eitherElim (const 1) isubstODepth

public export
isubstOCardAlg : ISubstOAlg Nat
isubstOCardAlg (Left ()) = 1
isubstOCardAlg (Right (Left (m, n))) = m + n
isubstOCardAlg (Right (Right (m, n))) = m * n

public export
isubstOCard : MuISubstO -> Nat
isubstOCard = isubstOCata Nat isubstOCardAlg

public export
substOCard : SubstObj -> Nat
substOCard = eitherElim (const 0) isubstOCard

-------------------------------------------------
---- Interpretation of substitution category ----
-------------------------------------------------

public export
isubstOToMetaAlg : ISubstOAlg Type
isubstOToMetaAlg (Left ()) = ()
isubstOToMetaAlg (Right (Left (x, y))) = Either x y
isubstOToMetaAlg (Right (Right (x, y))) = Pair x y

public export
isubstOToMeta : MuISubstO -> Type
isubstOToMeta = isubstOCata Type isubstOToMetaAlg

public export
substOToMeta : SubstObj -> Type
substOToMeta (Left ()) = Void
substOToMeta (Right t) = isubstOToMeta t

-----------------------------------------------
---- Exponentials in substitution category ----
-----------------------------------------------

public export
isubstOHomObjAlg : ISubstODiagAlg MuISubstO
-- 1 -> x == x
isubstOHomObjAlg (Left ()) x = InFCom x
-- (x + y) -> z == (x -> z) * (y -> z)
isubstOHomObjAlg (Right (Left (x, y))) z = ISOProduct (x z) (y z)
-- (x * y) -> z == x -> y -> z
isubstOHomObjAlg (Right (Right (x, y))) z with (y z)
  isubstOHomObjAlg (Right (Right (x, y))) z | InFreeM (InVar v) = void v
  isubstOHomObjAlg (Right (Right (x, y))) z | InFreeM (InCom yz) = x yz

public export
isubstOHomObj : MuISubstO -> MuISubstO -> MuISubstO
isubstOHomObj = isubstODiagCata MuISubstO isubstOHomObjAlg

public export
substOHomObj : SubstObj -> SubstObj -> SubstObj
-- 0 -> x == 1
substOHomObj (Left ()) _ = SOTerminal
-- x /= 0 => x -> 0 == 0
substOHomObj (Right _) (Left ()) = SOInitial
-- x /= 0, y /= 0
substOHomObj (Right x) (Right y) = Right $ isubstOHomObj x y

--------------------------------------------
---- Morphisms in substitution category ----
--------------------------------------------

public export
isubstOMorphism : MuISubstO -> MuISubstO -> Type
isubstOMorphism = isubstOToMeta .* isubstOHomObj

public export
isubstOEval : (x, y : MuISubstO) ->
  isubstOMorphism (ISOProduct (isubstOHomObj x y) x) y
isubstOEval x y = ?isubstOEval_hole

public export
isubstOCurry : {x, y, z : MuISubstO} ->
  isubstOMorphism (ISOProduct x y) z -> isubstOMorphism x (isubstOHomObj y z)
isubstOCurry {x} {y} {z} f = ?isubstOCurry_hole

--------------------------------------------------------------------
---- Interpretation of substitution endofunctors as polynomials ----
--------------------------------------------------------------------

public export
ISubstEndoFunctorF : Type -> Type
ISubstEndoFunctorF x =
  -- Identity
  Either () $
  -- Composition
  Either (x, x) $
  -- const unit, coproduct, product
  ISubstObjF x

public export
ISOEFIdF : {0 x : Type} -> ISubstEndoFunctorF x
ISOEFIdF = Left ()

public export
ISOEFComposeF : {0 x : Type} -> x -> x -> ISubstEndoFunctorF x
ISOEFComposeF = Right . Left .* MkPair

public export
ISOEFTerminalF : {0 x : Type} -> ISubstEndoFunctorF x
ISOEFTerminalF = Right $ Right $ ISOTerminalF

public export
ISOEFCoproductF : {0 x : Type} -> x -> x -> ISubstEndoFunctorF x
ISOEFCoproductF = Right . Right .* ISOCoproductF

public export
ISOEFProductF : {0 x : Type} -> x -> x -> ISubstEndoFunctorF x
ISOEFProductF = Right . Right .* ISOProductF

public export
ISOEFAlg : Type -> Type
ISOEFAlg = FAlg ISubstEndoFunctorF

public export
ISOEFDiagAlg : Type -> Type
ISOEFDiagAlg = DiagFAlg ISubstEndoFunctorF

public export
FreeISOEF : (0 _ : Type) -> Type
FreeISOEF = FreeM ISubstEndoFunctorF

public export
ISubstEndo : Type
ISubstEndo = MuF ISubstEndoFunctorF

public export
ISOEFId : {0 x : Type} -> FreeISOEF x
ISOEFId = InFCom $ ISOEFIdF

public export
ISOEFCompose : {0 x : Type} -> FreeISOEF x -> FreeISOEF x -> FreeISOEF x
ISOEFCompose = InFCom .* ISOEFComposeF

public export
ISOEFTerminal : {0 x : Type} -> FreeISOEF x
ISOEFTerminal = InFCom $ ISOEFTerminalF

public export
ISOEFCoproduct : {0 x : Type} -> FreeISOEF x -> FreeISOEF x -> FreeISOEF x
ISOEFCoproduct = InFCom .* ISOEFCoproductF

public export
ISOEFProduct : {0 x : Type} -> FreeISOEF x -> FreeISOEF x -> FreeISOEF x
ISOEFProduct = InFCom .* ISOEFProductF

public export
isubstEndoCata : FromInitialFAlg ISubstEndoFunctorF
isubstEndoCata x alg (InFreeM (InVar v)) = void v
isubstEndoCata x alg (InFreeM (InCom c)) = alg $ case c of
  Left () => Left ()
  Right c' => Right $ case c' of
    Left (l, r) => Left (isubstEndoCata x alg l, isubstEndoCata x alg r)
    Right c'' => Right $ case c'' of
      Left () => Left ()
      Right c''' => Right $ case c''' of
        Left (l, r) => Left (isubstEndoCata x alg l, isubstEndoCata x alg r)
        Right (l, r) => Right (isubstEndoCata x alg l, isubstEndoCata x alg r)

public export
iSubstEndoDiagCata : FromInitialDiagFAlg ISubstEndoFunctorF
iSubstEndoDiagCata = muDiagCata isubstEndoCata

public export
isoFunctorAlg : ISOEFAlg (Type -> Type)
isoFunctorAlg (Left ()) = id
isoFunctorAlg (Right (Left (g, f))) = g . f
isoFunctorAlg (Right (Right (Left ()))) = const Unit
isoFunctorAlg (Right (Right (Right (Left (f, g))))) = CoproductF f g
isoFunctorAlg (Right (Right (Right (Right (f, g))))) = ProductF f g

public export
isoFunctor : ISubstEndo -> Type -> Type
isoFunctor = isubstEndoCata (Type -> Type) isoFunctorAlg

-- Computes the endofunctor which results from pre-composing the
-- endofunctor `Const Void` with the given endofunctor.  If the
-- result is `Const Void`, it returns `Nothing`, since `FreeISOEF` does
-- not contain `Const Void` (it contains only the non-zero polynomials).
-- (Viewing an endofunctor `f` as a polynomial `p`, this computes
-- `p(0)` and then interprets the resulting polynomial as an endofunctor --
-- which must be constant.)
public export
isoAppVoidAlg : {0 x : Type} -> ISOEFAlg $ Maybe $ FreeISOEF x
-- 1 . 0 = Void
isoAppVoidAlg (Left ()) = Nothing
-- 0 . f = 0
isoAppVoidAlg (Right (Left (Nothing, _))) = Nothing
-- f(0) . 0 = f(0)
isoAppVoidAlg (Right (Left ((Just g), Nothing))) = Just g
-- g(0) . f(0) = (g + f)(0)
isoAppVoidAlg (Right (Left ((Just g), (Just f)))) = Just $ ISOEFCoproduct g f
-- 1(1) = 1
isoAppVoidAlg (Right (Right (Left ()))) = Just ISOEFTerminal
-- 0 + f(0) = f(0)
isoAppVoidAlg (Right (Right (Right (Left (Nothing, f))))) = f
-- f(0) + 0 = f(0)
isoAppVoidAlg (Right (Right (Right (Left (f, Nothing))))) = f
-- f(0) + g(0) = (f + g)(0)
isoAppVoidAlg (Right (Right (Right (Left ((Just f), (Just g)))))) =
  Just $ ISOEFCoproduct g f
-- 0 * g(0) = 0
isoAppVoidAlg (Right (Right (Right (Right (Nothing, g))))) = Nothing
-- f(0) * 0 = 0
isoAppVoidAlg (Right (Right (Right (Right ((Just f), Nothing))))) = Nothing
-- f(0) * g(0) = (f * g)(0)
isoAppVoidAlg (Right (Right (Right (Right ((Just f), (Just g)))))) =
  Just $ ISOEFProduct g f

public export
isoAppVoid : ISubstEndo -> Maybe ISubstEndo
isoAppVoid = isubstEndoCata _ isoAppVoidAlg

public export
ISOEFCoproductM : ISubstEndo -> ISubstEndo -> ISubstEndo
ISOEFCoproductM f g = ISOEFCoproduct f g

public export
ISOEFCodiag : ISubstEndo
ISOEFCodiag = ISOEFCoproductM ISOEFId ISOEFId

public export
ISOEFProductM : ISubstEndo -> ISubstEndo -> ISubstEndo
ISOEFProductM f g = ISOEFProduct f g

public export
ISOEFDiag : ISubstEndo
ISOEFDiag = ISOEFProductM ISOEFId ISOEFId

public export
repISubstObjF : ISubstEndo
repISubstObjF =
  ISOEFCoproduct ISOEFTerminal (ISOEFCoproduct ISOEFCodiag ISOEFCodiag)

public export
FreeSubstEndo : Type -> Type
FreeSubstEndo x =
  -- const Void
  Either ()
  -- Non-void endofunctor (which takes all inhabited types to inhabited types)
  (FreeISOEF x)

public export
SubstEndo : Type
SubstEndo = FreeSubstEndo Void

public export
SOEFInitial : {0 x : Type} -> FreeSubstEndo x
SOEFInitial = Left ()

public export
SOEFTerminal : {0 x : Type} -> FreeSubstEndo x
SOEFTerminal = Right ISOEFTerminal

public export
SOEFId : {0 x : Type} -> FreeSubstEndo x
SOEFId = Right ISOEFId

public export
isoAppVoidSO : ISubstEndo -> SubstEndo
isoAppVoidSO f = case isoAppVoid f of
  Just f' => Right f'
  Nothing => Left ()

public export
soAppVoid : SubstEndo -> SubstEndo
soAppVoid (Left ()) = Left ()
soAppVoid (Right f) = isoAppVoidSO f

public export
SOEFCompose : SubstEndo -> SubstEndo -> SubstEndo
SOEFCompose (Left ()) _ = Left ()
SOEFCompose (Right f) (Left ()) = isoAppVoidSO f
SOEFCompose (Right f) (Right g) = Right $ ISOEFCompose f g

public export
SOEFCoproduct : SubstEndo -> SubstEndo -> SubstEndo
SOEFCoproduct (Left ()) (Left ()) = Left ()
SOEFCoproduct (Left ()) (Right g) = Right g
SOEFCoproduct (Right f) (Left ()) = Right f
SOEFCoproduct (Right f) (Right g) = Right $ ISOEFCoproduct f g

public export
SOEFProduct : SubstEndo -> SubstEndo -> SubstEndo
SOEFProduct (Left ()) (Left ()) = Left ()
SOEFProduct (Left ()) (Right _) = Left ()
SOEFProduct (Right _) (Left ()) = Left ()
SOEFProduct (Right f) (Right g) = Right $ ISOEFProduct f g

public export
soFunctor : SubstEndo -> Type -> Type
soFunctor (Left ()) = const Void
soFunctor (Right f) = isoFunctor f

---------------------------------------------
---------------------------------------------
---- Natural numbers as directed colimit ----
---------------------------------------------
---------------------------------------------

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
natOFoldFreeIdx : {0 x, v : Type} ->
  (v -> x) -> (FreeNatO v -> x -> x) -> FreeNatO v -> x -> FreeNatO v -> x
natOFoldFreeIdx subst op idx e (InFreeM $ InVar var) =
  subst var
natOFoldFreeIdx subst op idx e (InFreeM $ InCom $ Left ()) =
  e
natOFoldFreeIdx subst op idx e (InFreeM $ InCom $ Right n) =
  natOFoldFreeIdx subst op (NatOS idx) (op idx e) n

public export
natOFoldFree : {0 x, v : Type} ->
  (v -> x) -> (FreeNatO v -> x -> x) -> x -> FreeNatO v -> x
natOFoldFree subst op = natOFoldFreeIdx subst op NatO0

public export
natOFoldIdx : {0 x : Type} -> (MuNatO -> x -> x) -> MuNatO -> x -> MuNatO -> x
natOFoldIdx {x} = natOFoldFreeIdx {x} {v=Void} (voidF x)

public export
natOFold : {0 x : Type} -> (MuNatO -> x -> x) -> x -> MuNatO -> x
natOFold {x} = natOFoldFree {x} {v=Void} (voidF x)

public export
natOCata : FromInitialFAlg NatOF
natOCata x alg (InFreeM $ InVar v) = void v
natOCata x alg (InFreeM $ InCom c) = alg $ case c of
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
natOAna x coalg e = InCofreeCM $ InNode () $ case coalg e of
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
natMulAlg = (const NatO0, (\alg, n => natSum (alg n) n))

public export
natMul : MuNatO -> MuNatO -> MuNatO
natMul = natOCataC natMulAlg

public export
natHomObjAlg : NatOAlgC (MuNatO -> MuNatO)
natHomObjAlg = (const NatO1, (\alg, n => natMul (alg n) n))

public export
natHomObj : MuNatO -> MuNatO -> MuNatO
natHomObj = natOCataC natHomObjAlg

public export
natPow : MuNatO -> MuNatO -> MuNatO
natPow = flip natHomObj

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
natPreCata {x} alg {n=(InFreeM $ InVar v)} m = void v
natPreCata {x} alg {n=(InFreeM $ InCom $ Left ())} m = void m
natPreCata {x} alg {n=(InFreeM $ InCom $ Right n)} m =
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
natOTCata x alg (InFreeM $ InVar v) = void v
natOTCata x alg (InFreeM $ InCom c) = alg $ case c of
  (Left (), Left ()) => (Left (), Left ())
  (Left (), Right n) => (Left (), Right $ natOTCata x alg n)
  (Right n, Left ()) => (Right $ natOTCata x alg n, Left ())
  (Right m, Right n) => (Right $ natOTCata x alg m, Right $ natOTCata x alg n)

----------------------------------------------------
----------------------------------------------------
---- Idris representation of polynomial circuit ----
----------------------------------------------------
----------------------------------------------------

------------------------------------------------------
------------------------------------------------------
---- Zeroth-order unrefined substitutive category ----
------------------------------------------------------
------------------------------------------------------

public export
data S0ObjF : Type -> Type where
  S0InitialF : {0 carrier : Type} -> S0ObjF carrier
  S0TerminalF : {0 carrier : Type} -> S0ObjF carrier
  S0CoproductF : {0 carrier : Type} -> carrier -> carrier -> S0ObjF carrier
  S0ProductF : {0 carrier : Type} -> carrier -> carrier -> S0ObjF carrier

public export
FreeS0Obj : (0 _ : Type) -> Type
FreeS0Obj = FreeM S0ObjF

public export
CofreeS0Obj : (0 _ : Type) -> Type
CofreeS0Obj = CofreeCM S0ObjF

public export
S0Obj : Type
S0Obj = MuF S0ObjF

public export
InfS0Obj : Type
InfS0Obj = NuF S0ObjF

public export
S0ObjInitial : {0 carrier : Type} -> FreeS0Obj carrier
S0ObjInitial = InFCom S0InitialF

public export
S0ObjTerminal : {0 carrier : Type} -> FreeS0Obj carrier
S0ObjTerminal = InFCom S0TerminalF

public export
S0ObjCoproduct : {0 carrier : Type} ->
  FreeS0Obj carrier -> FreeS0Obj carrier -> FreeS0Obj carrier
S0ObjCoproduct = InFCom .* S0CoproductF

public export
S0ObjProduct : {0 carrier : Type} ->
  FreeS0Obj carrier -> FreeS0Obj carrier -> FreeS0Obj carrier
S0ObjProduct = InFCom .* S0ProductF

public export
record S0ObjAlg (a : Type) where
  constructor MkS0ObjAlg
  soAlgInitial : a
  soAlgTerminal : a
  soAlgCoproduct : a -> a -> a
  soAlgProduct : a -> a -> a

public export
S0ObjDiagAlg : Type -> Type
S0ObjDiagAlg a = S0ObjAlg (S0ObjAlg a)

-- The slice category of `FreeS0Obj v` within `Type`.
public export
FreeS0Slice : (0 _ : Type) -> Type
FreeS0Slice v = FreeS0Obj v -> Type

-- The slice category of `(FreeS0Obj v) x (FreeS0Obj v)` within `Type`.
public export
FreeS0PairSlice : (0 _, _ : Type) -> Type
FreeS0PairSlice v v' = FreeS0Obj v -> FreeS0Obj v' -> Type

public export
FreeS0SliceAlg : Type
FreeS0SliceAlg = S0ObjAlg Type

public export
s0ObjFreeCata : {0 v, a : Type} ->
  S0ObjAlg a -> (v -> a) -> FreeS0Obj v -> a
s0ObjFreeCata alg subst (InFreeM e) = case e of
  InVar var => subst var
  InCom S0InitialF => soAlgInitial alg
  InCom S0TerminalF => soAlgTerminal alg
  InCom (S0CoproductF x y) =>
    soAlgCoproduct alg
      (s0ObjFreeCata alg subst x)
      (s0ObjFreeCata alg subst y)
  InCom (S0ProductF x y) =>
    soAlgProduct alg
      (s0ObjFreeCata alg subst x)
      (s0ObjFreeCata alg subst y)

public export
s0ObjFreeDiagCata : {0 algv, v, a : Type} ->
  S0ObjDiagAlg a -> (algv -> S0ObjAlg a) -> (v -> a) ->
  FreeS0Obj algv -> FreeS0Obj v -> a
s0ObjFreeDiagCata {v} {a} alg algsubst subst x y =
  s0ObjFreeCata (s0ObjFreeCata alg algsubst x) subst y

public export
s0ObjCata : {0 a : Type} -> S0ObjAlg a -> S0Obj -> a
s0ObjCata {a} alg = s0ObjFreeCata {a} {v=Void} alg (voidF a)

public export
s0ObjDiagCata : {0 a : Type} -> S0ObjDiagAlg a -> S0Obj -> S0Obj -> a
s0ObjDiagCata {a} alg =
  s0ObjFreeDiagCata {a} {v=Void} {algv=Void} alg (voidF (S0ObjAlg a)) (voidF a)

-- Generate a type family indexed by the type of objects of the
-- zeroth-order substitution category -- in other words, an object
-- of the slice category of the zeroth-order substitution category
-- within `Type`.
--
-- It might be more fruitful and analogous to dependent type theory,
-- however, to view it categorially instead as a functor from the
-- term category of `FreeS0Obj v` to `Type`.
public export
s0slice : FreeS0SliceAlg -> {0 v : Type} -> (v -> Type) -> FreeS0Slice v
s0slice alg = s0ObjFreeCata {a=Type} alg

public export
s0ObjDepthAlg : S0ObjAlg Nat
s0ObjDepthAlg = MkS0ObjAlg Z Z (S .* max) (S .* max)

public export
s0ObjDepth : {0 v : Type} -> (v -> Nat) -> FreeS0Obj v -> Nat
s0ObjDepth = s0ObjFreeCata s0ObjDepthAlg

public export
s0ObjCardAlg : S0ObjAlg Nat
s0ObjCardAlg = MkS0ObjAlg Z (S Z) (+) (*)

public export
s0ObjCard : {0 v : Type} -> (v -> Nat) -> FreeS0Obj v -> Nat
s0ObjCard = s0ObjFreeCata s0ObjCardAlg

-- Interpret `FreeS0Obj v` into `Type`.  In other words, generate a type
-- family indexed by terms of `FreeS0Obj v` where the type at each index
-- is an inpretation within `Type` of the index (which is a term of
-- `FreeS0Obj v`).
public export
s0ObjTermAlg : FreeS0SliceAlg
s0ObjTermAlg = MkS0ObjAlg Void Unit Either Pair

public export
s0ObjTerm : {0 v : Type} -> (v -> Type) -> FreeS0Slice v
s0ObjTerm = s0slice s0ObjTermAlg

-- For any object `x` of the zeroth-order substitution category, a
-- `FreeS0DepSet x` is a type which depends on `x`.  In dependent
-- type theory, it's a function which takes terms of `x` to types -- that
-- is, a term of the type of functions from `x` to `Type`.  In category
-- theory, it's an object of the slice category of `x` -- category theory
-- turns the dependent-type view backwards, by viewing the whole type
-- family as a single object, with a morphism from that object to `x`
-- which can be viewed as indicating, for each term of the whole type
-- family, which term of `x` that particular term's type came from.
--
-- The term-category view is that `FreeS0DepSet x` is a functor from the
-- term category of our interpretation of `x` into `Type` to `Type` itself.
public export
FreeS0DepSet : {0 v : Type} -> (v -> Type) -> FreeS0Slice v
FreeS0DepSet {v} subst x = s0ObjTerm {v} subst x -> Type

-- For any objects `x` and `y` of the zeroth-order substitution category, a
-- `FreeS0PairDepSet x y` is a type which depends on `x` and `y`.  In dependent
-- type theory, it's a function which takes terms of `(x, y)` to types -- that
-- is, a term of the type of functions from `(x, y)` to `Type`.  In category
-- theory, it's an object of the slice category of `(x, y)`, or, in the
-- term-category interpretation, a functor from the term category of
-- our interpretation of `(x, y)` to `Type`.  Our interpretation of `(x, y)`
-- is simply the product of our interpretations of `x` and `y`, so the term
-- category of our interpretation of `(x, y)` is just the term category of
-- the product of the term categories of our interpretations.
public export
FreeS0PairDepSet : {0 v, v' : Type} ->
  (v -> Type) -> (v' -> Type) -> FreeS0PairSlice v v'
FreeS0PairDepSet {v} {v'} subst subst' x y =
  s0ObjTerm {v} subst x -> s0ObjTerm {v=v'} subst' y -> Type

-- An algebra which produces a `FreeS0DepSet` for every object of
-- the zeroth-order substitution category.
--
-- This algebra can therefore be viewed as a generator of a
-- dependent functor -- a functor which takes each object `x` of
-- the zero-order substitution category not to an object of just
-- one other given category but to an object of the slice category
-- of that particular `x`.  (We will specifically use it to generate
-- dependent _polynomial_ functors.)
--
-- In the term-category view, this algebra generates a dependent functor
-- which takes an object of the zeroth-order substitution category to the
-- category of functors from that object's term category to `Type`.
-- A dependent functor may in turn be viewed as a dependent product in a
-- higher category.
public export
record FreeS0DepAlg where
  constructor MkFreeS0DepAlg
  fs0unit : Type
  fs0left : Type -> Type
  fs0right : Type -> Type
  fs0pair : Type -> Type -> Type

-- Returns a `FreeDep0Set x` for every object `x` of the zeroth-order
-- substitution category.
--
-- See the comment to `FreeS0DepAlg` for an interpretation of this function.
public export
freeS0DepSet : FreeS0DepAlg ->
  {0 v : Type} -> (subst : v -> Type) ->
  (depsubst : (var : v) -> subst var -> Type) ->
  (x : FreeS0Obj v) -> FreeS0DepSet subst x
freeS0DepSet alg subst depsubst (InFreeM (InVar var)) =
  depsubst var
freeS0DepSet alg subst depsubst (InFreeM (InCom S0InitialF)) =
  voidF Type
freeS0DepSet alg subst depsubst (InFreeM (InCom S0TerminalF)) =
  \u => case u of () => fs0unit alg
freeS0DepSet alg subst depsubst (InFreeM (InCom (S0CoproductF x y))) =
  \e => case e of
    Left l => fs0left alg (freeS0DepSet alg subst depsubst x l)
    Right r => fs0right alg (freeS0DepSet alg subst depsubst y r)
freeS0DepSet alg subst depsubst (InFreeM (InCom (S0ProductF x y))) =
  \p => case p of
    (l, r) =>
      fs0pair alg
        (freeS0DepSet alg subst depsubst x l)
        (freeS0DepSet alg subst depsubst y r)

------------------------
------------------------
---- List utilities ----
------------------------
------------------------

public export
listFoldCont : {0 a, b : Type} -> (b -> b) -> (a -> b -> b) -> b -> List a -> b
listFoldCont cont f z [] = cont z
listFoldCont cont f z (x :: xs) = listFoldCont (cont . f x) f z xs

public export
listFoldCPS : {0 a, b : Type} -> (a -> b -> b) -> b -> List a -> b
listFoldCPS {a} {b} = listFoldCont {a} {b} id

---------------------
---------------------
---- Polynomials ----
---------------------
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

-- For each position, show the number of directions at that position
-- (that is, the power).
public export
psPosShow : PolyShape -> String
psPosShow =
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

-- XXX arenas w/bijections (unless I can implement all formulas without this)

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
addPolyShapeList = listFoldCPS addPolyShape initialPolyShape

public export
addMapPolyShapeList :
  (PolyTerm -> PolyShape -> PolyShape) -> PolyShape -> PolyShape -> PolyShape
addMapPolyShapeList op p =
  listFoldCPS (addPolyShape . flip op p) initialPolyShape

public export
mulPolyShape : PolyShape -> PolyShape -> PolyShape
mulPolyShape = addMapPolyShapeList scaleMonPolyShape

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
mulPolyShapeList = listFoldCPS mulPolyShape terminalPolyShape

public export
parProdPolyShape : PolyShape -> PolyShape -> PolyShape
parProdPolyShape = addMapPolyShapeList parProdMonPolyShape

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
parProdPolyShapeList = listFoldCPS parProdPolyShape idPolyShape

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
composePolyShape = flip (addMapPolyShapeList composeMonPoly)

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
iterNPolyShape n p = foldrNat (composePolyShape p) terminalPolyShape n

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

public export
Functor RangedNatMorphF where
  map m (RNMComposeF g f) = RNMComposeF (m g) (m f)
  map m (RNMPolyF dom ps) = RNMPolyF dom ps
  map m (RNMSwitchF n l r) = RNMSwitchF n (m l) (m r)
  map m (RNMDivF dom n) = RNMDivF dom n
  map m (RNMModF dom n) = RNMModF dom n
  map m (RNMExtendCodBelowF f n) = RNMExtendCodBelowF (m f) n
  map m (RNMExtendCodAboveF f n) = RNMExtendCodAboveF (m f) n
  map m (RNMRestrictDomBelowF f n) = RNMRestrictDomBelowF (m f) n
  map m (RNMRestrictDomAboveF f n) = RNMRestrictDomAboveF (m f) n

public export
RNMSig : Type
RNMSig = (NatRange, NatRange)

public export
RNMAlg : Type -> Type
RNMAlg = FAlg RangedNatMorphF

public export
RNMDiagAlg : Type -> Type
RNMDiagAlg = DiagFAlg RangedNatMorphF

public export
rnmShowAlg : RNMAlg String
rnmShowAlg (RNMComposeF g f) = "(" ++ g ++ " . " ++ f ++ ")"
rnmShowAlg (RNMPolyF dom ps) =
  show ps ++ " : (" ++ show dom ++ " -> " ++ show (psInterpRange ps dom) ++ ")"
rnmShowAlg (RNMSwitchF n left right) =
  left ++ " | < " ++ show n ++ "<= | " ++ right
rnmShowAlg (RNMDivF range n) = show range ++ " / " ++ show n
rnmShowAlg (RNMModF range n) = show range ++ " % " ++ show n
rnmShowAlg (RNMExtendCodBelowF rnm n) = rnm ++ " < " ++ show n
rnmShowAlg (RNMExtendCodAboveF rnm n) = rnm ++ " > " ++ show n
rnmShowAlg (RNMRestrictDomBelowF rnm n) = show n ++ " > " ++ rnm
rnmShowAlg (RNMRestrictDomAboveF rnm n) = show n ++ " < " ++ rnm

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
rnmCata x alg (InFreeM $ InVar v) = void v
rnmCata x alg (InFreeM $ InCom c) = alg $ case c of
  RNMComposeF g f => RNMComposeF (rnmCata x alg g) (rnmCata x alg f)
  RNMPolyF dom ps => RNMPolyF dom ps
  RNMSwitchF n l r => RNMSwitchF n (rnmCata x alg l) (rnmCata x alg r)
  RNMDivF dom n => RNMDivF dom n
  RNMModF dom n => RNMModF dom n
  RNMExtendCodBelowF f n => RNMExtendCodBelowF (rnmCata x alg f) n
  RNMExtendCodAboveF f n => RNMExtendCodAboveF (rnmCata x alg f) n
  RNMRestrictDomBelowF f n => RNMRestrictDomBelowF (rnmCata x alg f) n
  RNMRestrictDomAboveF f n => RNMRestrictDomAboveF (rnmCata x alg f) n

public export
rnmDiagCata : FromInitialDiagFAlg RangedNatMorphF
rnmDiagCata = muDiagCata rnmCata

public export
rnmCheckAlg : RNMAlg (Maybe RNMSig)
rnmCheckAlg (RNMComposeF g f) = case (g, f) of
  (Just (domg, codg), Just (domf, codf)) =>
    if codf == domg then
      Just (domf, codg)
    else
      Nothing
  _ => Nothing
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
rnmCheckAlg (RNMExtendCodBelowF f n) = case f of
  Just (dom, (min, max)) => if n < min then Just (dom, (n, max)) else Nothing
  Nothing => Nothing
rnmCheckAlg (RNMExtendCodAboveF f n) = case f of
  Just (dom, (min, max)) => if max < n then Just (dom, (min, n)) else Nothing
  Nothing => Nothing
rnmCheckAlg (RNMRestrictDomBelowF f n) = case f of
  Just ((min, max), cod) =>
    if (min < n) && (n < max) then Just ((n, max), cod) else Nothing
  Nothing => Nothing
rnmCheckAlg (RNMRestrictDomAboveF f n) = case f of
  Just ((min, max), cod) =>
    if (min < n) && (n < max) then Just ((min, n), cod) else Nothing
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
RNMCompose : MuRNM -> MuRNM -> MuRNM
RNMCompose = InFCom .* RNMComposeF

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
RNMExtendCodBelow : MuRNM -> Nat -> MuRNM
RNMExtendCodBelow = InFCom .* RNMExtendCodBelowF

public export
RNMExtendCodAbove : MuRNM -> Nat -> MuRNM
RNMExtendCodAbove = InFCom .* RNMExtendCodAboveF

public export
RNMRestrictDomBelow : MuRNM -> Nat -> MuRNM
RNMRestrictDomBelow = InFCom .* RNMRestrictDomBelowF

public export
RNMRestrictDomAbove : MuRNM -> Nat -> MuRNM
RNMRestrictDomAbove = InFCom .* RNMRestrictDomAboveF

public export
rnmId : NatRange -> MuRNM
rnmId range = RNMPoly range idPolyShape

public export
interpRNMAlg : RNMAlg (Nat -> Nat)
interpRNMAlg (RNMComposeF g f) = g . f
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
interpRNMAlg (RNMExtendCodBelowF f n) = f
interpRNMAlg (RNMExtendCodAboveF f n) = f
interpRNMAlg (RNMRestrictDomBelowF f n) = f
interpRNMAlg (RNMRestrictDomAboveF f n) = f

public export
interpRNM : MuRNM -> Nat -> Nat
interpRNM = rnmCata _ interpRNMAlg

---------------------------------------------
---- Possibly-empty ("augmented") ranges ----
---------------------------------------------

-- `Nothing` means an empty range (Void).
public export
AugNatRange : Type
AugNatRange = Maybe NatRange

-- `Left` means the unique morphism from Void to the given (augmented) range.
public export
AugRNM : Type
AugRNM = Either AugNatRange MuRNM

public export
AugRNMSig : Type
AugRNMSig = (AugNatRange, AugNatRange)

public export
arnmCheck : AugRNM -> Maybe AugRNMSig
arnmCheck (Left range) = Just (Nothing, range)
arnmCheck (Right rnm) = map {f=Maybe} (mapHom {f=Pair} Just) (rnmCheck rnm)

public export
arnmId : AugNatRange -> AugRNM
arnmId Nothing = Left Nothing
arnmId (Just range) = Right (rnmId range)

public export
arnmUnvalidatedCompose : AugRNM -> AugRNM -> AugRNM
arnmUnvalidatedCompose (Left r) _ = Left r -- right morphism must be id on Void
arnmUnvalidatedCompose (Right g) (Left r) = case rnmCheck g of
  Just (domg, codg) => Left $ Just codg
  Nothing => Left Nothing
arnmUnvalidatedCompose (Right g) (Right f) = Right $ RNMCompose g f

-- This function witnesses that a polynomial may be viewed as a functor
-- in the category whose objects are augmented ranges (terms of `AugNatRange`)
-- and whose morphisms are augmented range morphisms (terms of `AugRNM`).
public export
psApplyAugRange : PolyShape -> AugNatRange -> AugNatRange
psApplyAugRange = map {f=Maybe} . psInterpRange

-- This is the morphism map for the functor represented by a polynomial
-- (whose object map is given by `psApplyARNM` above).
public export
psApplyARNM : PolyShape -> AugRNM -> AugRNM
psApplyARNM ps rnm =
  case arnmCheck rnm of
    Just (Nothing, cod) =>
      Left $ psApplyAugRange ps cod
    Just (Just r, _) =>
      arnmUnvalidatedCompose (Right (RNMPoly r ps)) rnm
    Nothing =>
      Left Nothing

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
BoundedNat n = Refinement {a=Nat} ((>=) n)

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
psCoeffSet : PolyShape -> AugNatRange
psCoeffSet ps with (sumPTCoeff ps)
  psCoeffSet ps | Z = Nothing
  psCoeffSet ps | (S n) = Just (0, n)

public export
pCoeffSet : Polynomial -> AugNatRange
pCoeffSet = psCoeffSet . shape

public export
record PolyNTShape where
  constructor MkPNT
  psOnPos : AugRNM

public export
validPNTS : Polynomial -> Polynomial -> DecPred PolyNTShape
validPNTS p q nt = ?validate_PNTS_is_correct_hole

public export
PolyNT : Polynomial -> Polynomial -> Type
PolyNT p q = Refinement {a=PolyNTShape} (validPNTS p q)

-- Polynomials may be viewed as endofunctors in the category of ranges of
-- natural numbers, or of augmented ranges of natural numbers.  A
-- natural transformation between polynomials `p` and `q` therefore has one
-- component `m` for each augmented range `r`, where that `m` is a morphism --
-- hence a term of `AugRNM` -- from `p(r)` to `q(r)`.  (`p(r)` and `q(r)` are
-- the ranges computed by `psApplyAugRange`.)
public export
pntsComponent : PolyShape -> PolyShape -> PolyNTShape -> AugNatRange -> AugRNM
pntsComponent p q alpha range = ?pntsComponent_hole

--------------------------------------
--------------------------------------
---- Natural-number-indexed types ----
--------------------------------------
--------------------------------------

-----------------
---- Aliases ----
-----------------

-- Endomorphisms on a given object in the category `Type`.
public export
EndoM : Type -> Type
EndoM a = a -> a

-- Endomorphisms on `Nat` (within the category `Type`).
public export
NatEM : Type
NatEM = EndoM Nat

-- The identity on `Nat`.
public export
NatId : NatEM
NatId = Prelude.id {a=Nat}

-- Endomorphisms on `NatPair` (within the category `Type`).
public export
NPEM : Type
NPEM = EndoM NatPair

-- The identity on `NatPair`.
public export
NPId : NPEM
NPId = Prelude.id {a=NatPair}

--------------------------------------------------
---- Category of natural-number-indexed types ----
--------------------------------------------------

-- Objects of the category of natural-number-indexed types.
-- The index is erased -- it's used only for compiling proofs in
-- the metalanguage (which in this case is Idris-2).
public export
NITObj : Type
NITObj = CExists0 Nat Type

-- Morphisms of the category of natural-number-indexed types.
public export
NITMorph : Type
NITMorph = EndoM NITObj

-------------------------------------------
-------------------------------------------
---- Bounded-natural-number operations ----
-------------------------------------------
-------------------------------------------

-- The operations that form single-variable polynomials.
public export
data PolyOpF : Type -> Type where
  PolyIdF : PolyOpF carrier
  PolyConstF : Nat -> PolyOpF carrier
  PolyAddF : carrier -> carrier -> PolyOpF carrier
  PolyMulF : carrier -> carrier -> PolyOpF carrier

public export
Functor PolyOpF where
  map m PolyIdF = PolyIdF
  map m (PolyConstF n) = PolyConstF n
  map m (PolyAddF p q) = PolyAddF (m p) (m q)
  map m (PolyMulF p q) = PolyMulF (m p) (m q)

public export
POShowAlg : Algebra PolyOpF String
POShowAlg PolyIdF = "id"
POShowAlg (PolyConstF n) = show n
POShowAlg (PolyAddF p q) = "(" ++ p ++ ") + (" ++ q ++ ")"
POShowAlg (PolyMulF p q) = "(" ++ p ++ ") * (" ++ q ++ ")"

public export
FreePolyOpN : NatObj -> Type -> Type
FreePolyOpN = OmegaChain PolyOpF

public export
FreePolyOp : Type -> Type
FreePolyOp = OmegaColimit PolyOpF

public export
PolyOp : Type
PolyOp = InitialColimit PolyOpF

--------------------------------------------------------------
--------------------------------------------------------------
---- Inductive definition of substitutive types (objects) ----
--------------------------------------------------------------
--------------------------------------------------------------

infixr 8 !!+
infixr 9 !!*

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

public export
Functor SubstObjF where
  map m SO0 = SO0
  map m SO1 = SO1
  map m (x !!+ y) = m x !!+ m y
  map m (x !!* y) = m x !!* m y

public export
MetaSOAlg : Type -> Type
MetaSOAlg x = SubstObjF x -> x

public export
MetaSOCoalg : Type -> Type
MetaSOCoalg x = x -> SubstObjF x

------------------------------------------------------------------------
---- Substitutive objects as least fixed point of generator functor ----
------------------------------------------------------------------------

public export
data SubstObjMu : Type where
  InSO : SubstObjF SubstObjMu -> SubstObjMu

infixr 8 !+
infixr 9 !*

public export
Subst0 : SubstObjMu
Subst0 = InSO SO0

public export
Subst1 : SubstObjMu
Subst1 = InSO SO1

public export
(!+) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!+) = InSO .* (!!+)

public export
(!*) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!*) = InSO .* (!!*)

public export
substObjCata : MetaSOAlg x -> SubstObjMu -> x
substObjCata alg = substObjFold id where
  mutual
    substObjCataCont : (x -> x -> SubstObjF x) ->
      (x -> x) -> SubstObjMu -> SubstObjMu -> x
    substObjCataCont op cont p q =
      substObjFold
        (\p' => substObjFold (\q' => cont $ alg $ op p' q') q) p

    substObjFold : (x -> x) -> SubstObjMu -> x
    substObjFold cont (InSO p) = case p of
      SO0 => cont (alg SO0)
      SO1 => cont (alg SO1)
      p !!+ q => substObjCataCont (!!+) cont p q
      p !!* q => substObjCataCont (!!*) cont p q

public export
data SubstObjNu : Type where
  InSOLabel : Inf (SubstObjF SubstObjNu) -> SubstObjNu

public export
substObjAna : MetaSOCoalg x -> x -> Inf SubstObjNu
substObjAna coalg = substObjUnfold id where
  mutual
    substObjAnaCont : (SubstObjNu -> SubstObjNu -> SubstObjF SubstObjNu) ->
      (SubstObjNu -> SubstObjNu) -> x -> x -> SubstObjNu
    substObjAnaCont op cont x y =
      substObjUnfold
        (\x' => substObjUnfold (\y' => cont $ InSOLabel $ op x' y') y) x

    substObjUnfold : (SubstObjNu -> SubstObjNu) -> x -> Inf SubstObjNu
    substObjUnfold cont t = case coalg t of
      SO0 => cont (InSOLabel SO0)
      SO1 => cont (InSOLabel SO1)
      p !!+ q => substObjAnaCont (!!+) cont p q
      p !!* q => substObjAnaCont (!!*) cont p q

public export
SubstObjPairAlg : Type -> Type
SubstObjPairAlg x = MetaSOAlg (SubstObjMu -> x)

public export
substObjPairCata : SubstObjPairAlg x -> SubstObjMu -> SubstObjMu -> x
substObjPairCata = substObjCata

-------------------
---- Utilities ----
-------------------

public export
SOSizeAlg : MetaSOAlg Nat
SOSizeAlg SO0 = 1
SOSizeAlg SO1 = 1
SOSizeAlg (p !!+ q) = p + q
SOSizeAlg (p !!* q) = p + q

public export
substObjSize : SubstObjMu -> Nat
substObjSize = substObjCata SOSizeAlg

public export
SODepthAlg : MetaSOAlg Nat
SODepthAlg SO0 = 0
SODepthAlg SO1 = 0
SODepthAlg (p !!+ q) = smax p q
SODepthAlg (p !!* q) = smax p q

public export
substObjDepth : SubstObjMu -> Nat
substObjDepth = substObjCata SODepthAlg

-- The cardinality of the type that would result from applying
-- the given substObjnomial to a type of the given cardinality.
public export
SOCardAlg : MetaSOAlg Nat
SOCardAlg SO0 = 0
SOCardAlg SO1 = 1
SOCardAlg (p !!+ q) = p + q
SOCardAlg (p !!* q) = p * q

public export
substObjCard : SubstObjMu -> Nat
substObjCard = substObjCata SOCardAlg

-----------------------------------------
---- Displaying substitutive objects ----
-----------------------------------------

public export
SOShowAlg : MetaSOAlg String
SOShowAlg SO0 = "0"
SOShowAlg SO1 = "1"
SOShowAlg (x !!+ y) = "(" ++ x ++ " + " ++ y ++ ")"
SOShowAlg (x !!* y) = x ++ " * " ++ y

public export
Show SubstObjMu where
  show = substObjCata SOShowAlg

------------------------------------------
---- Equality on substitutive objects ----
------------------------------------------

public export
SubstObjMuEqAlg : SubstObjPairAlg Bool
SubstObjMuEqAlg SO0 (InSO SO0) = True
SubstObjMuEqAlg SO0 _ = False
SubstObjMuEqAlg SO1 (InSO SO1) = True
SubstObjMuEqAlg SO1 _ = False
SubstObjMuEqAlg (p !!+ q) (InSO (r !!+ s)) = p r && q s
SubstObjMuEqAlg (p !!+ q) _ = False
SubstObjMuEqAlg (p !!* q) (InSO (r !!* s)) = p r && q s
SubstObjMuEqAlg (p !!* q) _ = False

public export
Eq SubstObjMu where
  (==) = substObjPairCata SubstObjMuEqAlg

-----------------------------------------------
---- Normalization of substitutive objects ----
-----------------------------------------------

public export
SORemoveZeroAlg : MetaSOAlg SubstObjMu
SORemoveZeroAlg SO0 = Subst0
SORemoveZeroAlg SO1 = Subst1
SORemoveZeroAlg (p !!+ q) = case p of
  InSO p' => case p' of
    SO0 => q
    _ => case q of
      InSO q' => case q' of
        SO0 => p
        _ => p !+ q
SORemoveZeroAlg (p !!* q) = case p of
  InSO p' => case p' of
    SO0 => Subst0
    _ => case q of
      InSO q' => case q' of
        SO0 => Subst0
        _ => p !* q

public export
substObjRemoveZero : SubstObjMu -> SubstObjMu
substObjRemoveZero = substObjCata SORemoveZeroAlg

public export
SORemoveOneAlg : MetaSOAlg SubstObjMu
SORemoveOneAlg SO0 = Subst0
SORemoveOneAlg SO1 = Subst1
SORemoveOneAlg (p !!+ q) = p !+ q
SORemoveOneAlg (p !!* q) = case p of
  InSO p' => case p' of
    SO1 => q
    _ => case q of
      InSO q' => case q' of
        SO1 => p
        _ => p !* q

public export
substObjRemoveOne : SubstObjMu -> SubstObjMu
substObjRemoveOne = substObjCata SORemoveOneAlg

public export
substObjNormalize : SubstObjMu -> SubstObjMu
substObjNormalize = substObjRemoveOne . substObjRemoveZero

-----------------------------------------------------
---- Multiplication by a constant (via addition) ----
-----------------------------------------------------

infix 10 !:*
public export
(!:*) : Nat -> SubstObjMu -> SubstObjMu
n !:* p = foldrNatNoUnit ((!+) p) Subst0 p n

---------------------------------------
---- Multiplicative exponentiation ----
---------------------------------------

infix 10 !*^
public export
(!*^) : SubstObjMu -> Nat -> SubstObjMu
p !*^ n = foldrNatNoUnit ((!*) p) Subst1 p n

--------------------------------------------
---- Morphisms of substitutive category ----
--------------------------------------------

public export
SubstTermAlg : MetaSOAlg Type
SubstTermAlg SO0 = Void
SubstTermAlg SO1 = ()
SubstTermAlg (x !!+ y) = Either x y
SubstTermAlg (x !!* y) = Pair x y

public export
SubstTerm : SubstObjMu -> Type
SubstTerm = substObjCata SubstTermAlg

public export
SubstContradictionAlg : MetaSOAlg Type
SubstContradictionAlg SO0 = ()
SubstContradictionAlg SO1 = Void
SubstContradictionAlg (x !!+ y) = Pair x y
SubstContradictionAlg (x !!* y) = Either x y

-- `SubstContradiction x` is inhabited if and only if `x` is uninhabited;
-- it is the dual of `SubstTerm x` (reflecting that a type is contradictory
-- if and only if it has no terms)
public export
SubstContradiction : SubstObjMu -> Type
SubstContradiction = substObjCata SubstContradictionAlg

infixr 1 <!
public export
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

public export
showSubstMorph : {x, y : SubstObjMu} -> SubstMorph x y -> String
showSubstMorph (SMId x) = "id{" ++ show x ++ "}"
showSubstMorph (g <! f) = showSubstMorph g ++ " . " ++ showSubstMorph f
showSubstMorph (SMFromInit x) = "{0 -> " ++ show x ++ "}"
showSubstMorph (SMToTerminal x) = "{" ++ show x ++ " -> 1}"
showSubstMorph (SMInjLeft x y) = "->Left<" ++ show x ++ " | " ++ show y ++ ">"
showSubstMorph (SMInjRight x y) = "->Right<" ++ show x ++ " | " ++ show y ++ ">"
showSubstMorph (SMCase f g) =
  "[" ++ showSubstMorph f ++ " | " ++ showSubstMorph g ++ "]"
showSubstMorph (SMPair f g) =
  "(" ++ showSubstMorph f ++ ", " ++ showSubstMorph g ++ ")"
showSubstMorph (SMProjLeft x y) = "<-Left<" ++ show x ++ ", " ++ show y ++ ">"
showSubstMorph (SMProjRight x y) = "<-Right<" ++ show x ++ ", " ++ show y ++ ">"
showSubstMorph (SMDistrib x y z) =
  "distrib{" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ "}"

public export
soProdCommutes : (x, y : SubstObjMu) -> SubstMorph (x !* y) (y !* x)
soProdCommutes x y = SMPair (SMProjRight x y) (SMProjLeft x y)

public export
soProdCommutesLeft : {x, y, z : SubstObjMu} ->
  SubstMorph (x !* y) z -> SubstMorph (y !* x) z
soProdCommutesLeft f = f <! soProdCommutes y x

public export
soProdCommutesRight : {x, y, z : SubstObjMu} ->
  SubstMorph x (y !* z) -> SubstMorph x (z !* y)
soProdCommutesRight f = soProdCommutes y z <! f

public export
soCopCommutes : (x, y : SubstObjMu) -> SubstMorph (x !+ y) (y !+ x)
soCopCommutes x y = SMCase (SMInjRight y x) (SMInjLeft y x)

public export
soCopCommutesLeft : {x, y, z : SubstObjMu} ->
  SubstMorph (x !+ y) z -> SubstMorph (y !+ x) z
soCopCommutesLeft f = f <! soCopCommutes y x

public export
soCopCommutesRight : {x, y, z : SubstObjMu} ->
  SubstMorph x (y !+ z) -> SubstMorph x (z !+ y)
soCopCommutesRight f = soCopCommutes y z <! f

public export
soLeft : {x, y, z : SubstObjMu} -> SubstMorph (x !+ y) z -> SubstMorph x z
soLeft {x} {y} f = f <! SMInjLeft x y

public export
soRight : {x, y, z : SubstObjMu} -> SubstMorph (x !+ y) z -> SubstMorph y z
soRight f {x} {y} = f <! SMInjRight x y

public export
soProdLeft : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph (x !* y) z
soProdLeft f = f <! SMProjRight _ _

public export
soProdRight : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph (y !* x) z
soProdRight f = f <! SMProjLeft _ _

public export
soForgetFirst : (x, y, z : SubstObjMu) -> SubstMorph ((x !* y) !* z) (y !* z)
soForgetFirst x y z =
  SMPair (SMProjRight _ _ <! SMProjLeft _ _) (SMProjRight _ _)

public export
soForgetMiddle : (x, y, z : SubstObjMu) -> SubstMorph ((x !* y) !* z) (x !* z)
soForgetMiddle x y z =
  SMPair (SMProjLeft _ _ <! SMProjLeft _ _) (SMProjRight _ _)

public export
soForgetRight : (x, y, z : SubstObjMu) -> SubstMorph (x !* (y !* z)) (x !* y)
soForgetRight x y z =
  SMPair (SMProjLeft _ _) (SMProjLeft _ _ <! SMProjRight _ _)

public export
soProd1LeftElim : {x, y : SubstObjMu} ->
  SubstMorph (Subst1 !* x) y -> SubstMorph x y
soProd1LeftElim {x} f = f <! SMPair (SMToTerminal x) (SMId x)

public export
soProdLeftIntro : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph (x !* y) z
soProdLeftIntro f = f <! SMProjRight _ _

public export
soProdLeftApply : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph (x !* y) (x !* z)
soProdLeftApply f = SMPair (SMProjLeft _ _) (soProdLeftIntro f)

public export
soProdLeftAssoc : {w, x, y, z : SubstObjMu} ->
  SubstMorph (w !* (x !* y)) z -> SubstMorph ((w !* x) !* y) z
soProdLeftAssoc {w} {x} {y} {z} f =
  f <!
    SMPair
      (SMProjLeft _ _ <! SMProjLeft _ _)
      (SMPair (SMProjRight _ _ <! SMProjLeft _ _) (SMProjRight _ _))

-- The inverse of SMDistrib.
public export
soGather : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !* y) !+ (x !* z)) (x !* (y !+ z))
soGather x y z =
  SMPair
    (SMCase (SMProjLeft _ _) (SMProjLeft _ _))
    (SMCase
      (SMInjLeft _ _ <! SMProjRight _ _)
      (SMInjRight _ _ <! SMProjRight _ _))

public export
SOTerm : SubstObjMu -> Type
SOTerm = SubstMorph Subst1

--------------------------------------------------------------
---- Exponentiation (hom-objects) of substitutive objects ----
--------------------------------------------------------------

public export
SubstHomObj : SubstObjMu -> SubstObjMu -> SubstObjMu
-- 0 -> y == 1
SubstHomObj (InSO SO0) _ = Subst1
-- 1 -> y == y
SubstHomObj (InSO SO1) y = y
-- (x + y) -> z == (x -> z) * (y -> z)
SubstHomObj (InSO (x !!+ y)) z = SubstHomObj x z !* SubstHomObj y z
-- (x * y) -> z == x -> y -> z
SubstHomObj (InSO (x !!* y)) z = SubstHomObj x (SubstHomObj y z)

infix 10 !->
public export
(!->) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!->) = SubstHomObj

infix 10 !^
public export
(!^) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!^) = flip SubstHomObj

public export
soEval : (x, y : SubstObjMu) ->
  SubstMorph ((x !-> y) !* x) y
soEval (InSO SO0) y = SMFromInit y <! SMProjRight Subst1 Subst0
soEval (InSO SO1) y = SMProjLeft y Subst1
soEval (InSO (x !!+ y)) z =
  SMCase (soEval x z) (soEval y z) <!
    SMCase
      (SMInjLeft _ _ <! soForgetMiddle _ _ _)
      (SMInjRight _ _ <! soForgetFirst _ _ _)
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

public export
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

public export
soUncurry : {x, y, z : SubstObjMu} ->
  SubstMorph x (y !-> z) -> SubstMorph (x !* y) z
soUncurry {x} {y} {z} f =
  soEval y z <! SMPair (f <! SMProjLeft x y) (SMProjRight x y)

public export
soPartialApp : {w, x, y, z : SubstObjMu} ->
  SubstMorph (x !* y) z -> SubstMorph w x -> SubstMorph (w !* y) z
soPartialApp g f = soUncurry $ soCurry g <! f

public export
soSubst : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph x y -> SubstMorph x z
soSubst (SMId y) f = f
soSubst g (SMId _) = g
soSubst (h <! g) f = h <! soSubst g f
soSubst h (g <! f) = soSubst h g <! f
soSubst {y=Subst0} {z} (SMFromInit _) (g <! f) = SMFromInit z <! soSubst g f
soSubst {z} (SMFromInit _) (SMCase f g) =
  SMCase (soSubst (SMFromInit z) f) (soSubst (SMFromInit z) g)
soSubst (SMFromInit _) (SMProjLeft _ _) = SMFromInit _ <! SMProjLeft _ _
soSubst (SMFromInit _) (SMProjRight _ _) = SMFromInit _ <! SMProjRight _ _
soSubst _ (SMFromInit _) = SMFromInit _
soSubst (SMToTerminal _) _ = SMToTerminal _
soSubst (SMInjLeft _ _) f = SMInjLeft _ _ <! f
soSubst (SMInjRight _ _) f = SMInjRight _ _ <! f
soSubst (SMCase g h) (SMInjLeft _ _) = g
soSubst (SMCase g h) (SMInjRight _ _) = h
soSubst (SMCase g h) (SMProjLeft _ _) = SMCase g h <! SMProjLeft _ _
soSubst (SMCase g h) (SMProjRight _ _) = SMCase g h <! SMProjRight _ _
soSubst (SMCase h j) (SMCase f g) =
  SMCase (soSubst (SMCase h j) f) (soSubst (SMCase h j) g)
soSubst (SMCase g h) (SMDistrib _ _ _) = SMCase g h <! SMDistrib _ _ _
soSubst (SMPair g h) f = SMPair (soSubst g f) (soSubst h f)
soSubst (SMProjLeft _ _) (SMProjLeft _ _) = SMProjLeft _ _ <! SMProjLeft _ _
soSubst (SMProjLeft _ _) (SMProjRight _ _) = SMProjLeft _ _ <! SMProjRight _ _
soSubst (SMProjLeft _ _) (SMCase f g) =
  SMCase (soSubst (SMProjLeft _ _) f) (soSubst (SMProjLeft _ _) g)
soSubst (SMProjLeft _ _) (SMPair f g) = f
soSubst (SMProjRight _ _) (SMProjLeft _ _) = SMProjRight _ _ <! SMProjLeft _ _
soSubst (SMProjRight _ _) (SMProjRight _ _) = SMProjRight _ _ <! SMProjRight _ _
soSubst (SMProjRight _ _) (SMCase f g) =
  SMCase (soSubst (SMProjRight _ _) f) (soSubst (SMProjRight _ _) g)
soSubst (SMProjRight _ _) (SMPair f g) = g
soSubst (SMDistrib _ _ _) (SMProjLeft _ _) = SMDistrib _ _ _ <! SMProjLeft _ _
soSubst (SMDistrib _ _ _) (SMProjRight _ _) = SMDistrib _ _ _ <! SMProjRight _ _
soSubst (SMDistrib _ _ _) (SMCase f g) = SMDistrib _ _ _ <! SMCase f g
soSubst (SMDistrib _ _ _) (SMPair f g) = SMDistrib _ _ _ <! SMPair f g

public export
soReduce : {x, y : SubstObjMu} -> SubstMorph x y -> SubstMorph x y
soReduce (SMId _) = SMId _
soReduce (g <! f) = soSubst (soReduce g) (soReduce f)
soReduce (SMFromInit _) = SMFromInit _
soReduce (SMToTerminal x) = SMToTerminal _
soReduce (SMInjLeft _ _) = SMInjLeft _ _
soReduce (SMInjRight _ _) = SMInjRight _ _
soReduce (SMCase f g) = SMCase (soReduce f) (soReduce g)
soReduce (SMPair f g) = SMPair (soReduce f) (soReduce g)
soReduce (SMProjLeft _ _) = SMProjLeft _ _
soReduce (SMProjRight _ _) = SMProjRight _ _
soReduce (SMDistrib _ _ _) = SMDistrib _ _ _

-------------------------------------------
---- Morphisms as terms of hom-objects ----
-------------------------------------------

public export
HomTerm : SubstObjMu -> SubstObjMu -> Type
HomTerm = SOTerm .* SubstHomObj

public export
TermAsMorph : {x, y : SubstObjMu} -> HomTerm x y -> SubstMorph x y
TermAsMorph {x} {y} t = soProd1LeftElim $ soUncurry {x=Subst1} {y=x} {z=y} t

public export
MorphAsTerm : {x, y : SubstObjMu} -> SubstMorph x y -> HomTerm x y
MorphAsTerm {x} {y} f = soCurry {x=Subst1} {y=x} {z=y} $ soProdLeftIntro f

public export
covarYonedaEmbed : {a, b : SubstObjMu} ->
  SubstMorph b a -> (x : SubstObjMu) -> SubstMorph (a !-> x) (b !-> x)
covarYonedaEmbed {a} {b} f x =
  soCurry (soEval a x <! SMPair (SMProjLeft _ _) (f <! SMProjRight _ _))

public export
contravarYonedaEmbed : {a, b : SubstObjMu} ->
  SubstMorph a b -> (x : SubstObjMu) -> SubstMorph (x !-> a) (x !-> b)
contravarYonedaEmbed {a} {b} f x =
  soCurry (f <! soEval x a)

----------------------------------------------------------------------------
---- Homoiconicity: SubstMorph reflected into the substitutive category ----
----------------------------------------------------------------------------

public export
IdTerm : (x : SubstObjMu) -> HomTerm x x
IdTerm x = MorphAsTerm (SMId x)

public export
soHigherEval : (x, y : SubstObjMu) -> HomTerm ((x !-> y) !* x) y
soHigherEval x y = MorphAsTerm $ SMId (x !-> y)

public export
soHigherCurry : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !* y) !-> z) (x !-> (y !-> z))
soHigherCurry x y z = SMId (x !-> (y !-> z))

public export
soHigherUncurry : (x, y, z : SubstObjMu) ->
  SubstMorph (x !-> (y !-> z)) ((x !* y) !-> z)
soHigherUncurry x y z = SMId (x !-> (y !-> z))

public export
soHigherCase : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !-> z) !* (y !-> z)) ((x !+ y) !-> z)
soHigherCase x y z = SMId (SubstHomObj x z !* SubstHomObj y z)

public export
soHigherPair : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !-> y) !* (x !-> z)) (x !-> (y !* z))
soHigherPair (InSO SO0) _ _ = SMToTerminal _
soHigherPair (InSO SO1) _ _ = SMId _
soHigherPair (InSO (w !!+ x)) y z =
  let
    wyz = soHigherPair w y z
    xyz = soHigherPair x y z
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
soHigherPair (InSO (w !!* x)) y z =
  let
    xyz = soHigherPair x y z
    wxyz = soHigherPair w (x !-> y) (x !-> z)
  in
  contravarYonedaEmbed xyz w <! wxyz

public export
soHigherCompose : (x, y, z : SubstObjMu) ->
  SubstMorph ((y !-> z) !* (x !-> y)) (x !-> z)
soHigherCompose (InSO SO0) y z = SMToTerminal _
soHigherCompose (InSO SO1) y z = soEval y z
soHigherCompose (InSO (w !!+ x)) y z =
  let
    cwyz = soHigherCompose w y z
    cxyz = soHigherCompose x y z
  in
  SMPair
    (cwyz <! SMPair (SMProjLeft _ _) (SMProjLeft _ _ <! SMProjRight _ _))
    (cxyz <! SMPair (SMProjLeft _ _) (SMProjRight _ _ <! SMProjRight _ _))
soHigherCompose (InSO (w !!* x)) y z =
  soCurry $ soCurry $
    soEval y z <! SMPair
      (SMProjLeft _ _ <! SMProjLeft _ _ <! SMProjLeft _ _)
      (soEval x y <! SMPair
        (soEval w (x !-> y) <! SMPair
          (SMProjRight _ _ <! SMProjLeft _ _ <! SMProjLeft _ _)
          (SMProjRight _ _ <! SMProjLeft _ _))
        (SMProjRight _ _))

public export
soHigherPartialApp : (w, x, y, z : SubstObjMu) ->
  SubstMorph (((x !* y) !-> z) !* (w !-> x)) ((w !* y) !-> z)
soHigherPartialApp w x y z =
  soHigherCurry w y z <! (soHigherCompose w x (y !-> z))

-------------------------------------------------------------------
---- Explicitly-polynomial-functor version of above definition ----
-------------------------------------------------------------------

public export
data SubstMorphADTPos : Type where
  SMAPFrom0 : SubstObjMu -> SubstMorphADTPos
  SMAPCopTo1 : SubstObjMu -> SubstObjMu -> SubstMorphADTPos
  SMAPProdTo1 : SubstObjMu -> SubstObjMu -> SubstMorphADTPos
  SMAPId1 : SubstMorphADTPos
  SMAPTermLeft : SubstObjMu -> SubstMorphADTPos
  SMAPTermRight : SubstObjMu -> SubstMorphADTPos
  SMAPTermPair : SubstMorphADTPos
  SMAPCase : SubstMorphADTPos
  SMAP0PLeft : SubstObjMu -> SubstObjMu -> SubstMorphADTPos
  SMAP1PLeft : SubstMorphADTPos
  SMAPDistrib : SubstObjMu -> SubstObjMu -> SubstObjMu -> SubstMorphADTPos
  SMAPAssoc : SubstObjMu -> SubstObjMu -> SubstObjMu -> SubstMorphADTPos

public export
SubstMorphADTNDir : SubstMorphADTPos -> Nat
SubstMorphADTNDir (SMAPFrom0 _) = 0
SubstMorphADTNDir (SMAPCopTo1 _ _) = 0
SubstMorphADTNDir (SMAPProdTo1 _ _) = 0
SubstMorphADTNDir SMAPId1 = 0
SubstMorphADTNDir (SMAPTermLeft _) = 1
SubstMorphADTNDir (SMAPTermRight _) = 1
SubstMorphADTNDir SMAPTermPair = 2
SubstMorphADTNDir SMAPCase = 2
SubstMorphADTNDir (SMAP0PLeft _ _) = 0
SubstMorphADTNDir SMAP1PLeft = 1
SubstMorphADTNDir (SMAPDistrib _ _ _) = 1
SubstMorphADTNDir (SMAPAssoc _ _ _) = 1

public export
SubstMorphADTDir : SubstMorphADTPos -> Type
SubstMorphADTDir = Fin . SubstMorphADTNDir

public export
SubstMorphADTPoly : PolyFunc
SubstMorphADTPoly = (SubstMorphADTPos ** SubstMorphADTDir)

public export
SubstMorphADTPFAlg : Type -> Type
SubstMorphADTPFAlg = PFAlg SubstMorphADTPoly

public export
SubstMorphADTSig : Type
SubstMorphADTSig = (SubstObjMu, SubstObjMu)

public export
SubstMorphADTPFAlgCheckSig : SubstMorphADTPFAlg (Maybe SubstMorphADTSig)
SubstMorphADTPFAlgCheckSig (SMAPFrom0 x) d = Just (Subst0, x)
SubstMorphADTPFAlgCheckSig SMAPId1 d = Just (Subst1, Subst1)
SubstMorphADTPFAlgCheckSig (SMAPCopTo1 x y) d = Just (x !+ y, Subst1)
SubstMorphADTPFAlgCheckSig (SMAPProdTo1 x y) d = Just (x !* y, Subst1)
SubstMorphADTPFAlgCheckSig (SMAPTermLeft x) d = case d FZ of
  Just (y, z) => if y == Subst1 then Just (Subst1, z !+ x) else Nothing
  Nothing => Nothing
SubstMorphADTPFAlgCheckSig (SMAPTermRight x) d = ?SubstMorphADTPFAlgCheckSig_hole_5
SubstMorphADTPFAlgCheckSig SMAPTermPair d = ?SubstMorphADTPFAlgCheckSig_hole_6
SubstMorphADTPFAlgCheckSig SMAPCase d = ?SubstMorphADTPFAlgCheckSig_hole_7
SubstMorphADTPFAlgCheckSig (SMAP0PLeft x y) d = ?SubstMorphADTPFAlgCheckSig_hole_8
SubstMorphADTPFAlgCheckSig SMAP1PLeft d = ?SubstMorphADTPFAlgCheckSig_hole_9
SubstMorphADTPFAlgCheckSig (SMAPDistrib x y z) d = ?SubstMorphADTPFAlgCheckSig_hole_10
SubstMorphADTPFAlgCheckSig (SMAPAssoc x y z) d = ?SubstMorphADTPFAlgCheckSig_hole_11

public export
data SubstMorphADTF : Type -> Type where
  SMAFrom0 : SubstObjMu -> SubstMorphADTF carrier
  SMACopTo1 : SubstObjMu -> SubstObjMu -> SubstMorphADTF carrier
  SMAProdTo1 : SubstObjMu -> SubstObjMu -> SubstMorphADTF carrier
  SMAId1 : SubstMorphADTF carrier
  SMATermLeft : carrier -> SubstObjMu -> SubstMorphADTF carrier
  SMATermRight : SubstObjMu -> carrier -> SubstMorphADTF carrier
  SMATermPair : carrier -> carrier -> SubstMorphADTF carrier
  SMACase : carrier -> carrier -> SubstMorphADTF carrier
  SMA0PLeft : SubstObjMu -> SubstObjMu -> SubstMorphADTF carrier
  SMA1PLeft : carrier -> SubstMorphADTF carrier
  SMADistrib : SubstObjMu -> SubstObjMu -> SubstObjMu ->
    carrier -> SubstMorphADTF carrier
  SMAAssoc : SubstObjMu -> SubstObjMu -> SubstObjMu ->
    carrier -> SubstMorphADTF carrier

public export
Functor SubstMorphADTF where
  map f (SMAFrom0 x) = SMAFrom0 x
  map f (SMACopTo1 x y) = SMACopTo1 x y
  map f (SMAProdTo1 x y) = SMAProdTo1 x y
  map f SMAId1 = SMAId1
  map f (SMATermLeft x y) = SMATermLeft (f x) y
  map f (SMATermRight x y) = SMATermRight x (f y)
  map f (SMATermPair x y) = SMATermPair (f x) (f y)
  map f (SMACase x y) = SMACase (f x) (f y)
  map f (SMA0PLeft x y) = SMA0PLeft x y
  map f (SMA1PLeft x) = SMA1PLeft (f x)
  map f (SMADistrib x y z w) = SMADistrib x y z (f w)
  map f (SMAAssoc x y z w) = SMAAssoc x y z (f w)

public export
data SubstMorphADT : Type where
  InSM : SubstMorphADTF SubstMorphADT -> SubstMorphADT

public export
SubstMorphADTAlg : Type -> Type
SubstMorphADTAlg x = SubstMorphADTF x -> Maybe x

public export
substMorphADTCata : SubstMorphADTAlg x -> SubstMorphADT -> Maybe x
substMorphADTCata alg (InSM x) = ?substMorphADTCata_hole

public export
SMADTCheckSigAlg :
  SubstMorphADTF (SubstObjMu, SubstObjMu) -> Maybe (SubstObjMu, SubstObjMu)
SMADTCheckSigAlg (SMAFrom0 x) = Just (Subst0, x)
SMADTCheckSigAlg SMAId1 = Just (Subst1, Subst1)
SMADTCheckSigAlg (SMACopTo1 x y) = Just (x !+ y, Subst1)
SMADTCheckSigAlg (SMAProdTo1 x y) = Just (x !* y, Subst1)
SMADTCheckSigAlg (SMATermLeft (d, c) y) =
  if d == Subst1 then Just (Subst1, c !+ y) else Nothing
SMADTCheckSigAlg (SMATermRight x (d, c)) =
  if d == Subst1 then Just (Subst1, x !+ c) else Nothing
SMADTCheckSigAlg (SMATermPair (d, c) (d', c')) =
  if d == Subst1 && d' == Subst1 then Just (Subst1, c !* c') else Nothing
SMADTCheckSigAlg (SMACase (d, c) (d', c')) =
  if c == c' then Just (d !+ d', c) else Nothing
SMADTCheckSigAlg (SMA0PLeft x y) = Just (Subst0 !* x, y)
SMADTCheckSigAlg (SMA1PLeft (d, c)) = Just (Subst1 !* d, c)
SMADTCheckSigAlg (SMADistrib x y z (d, c)) =
  if d == (x !+ y) !* z then Just ((x !* z) !+ (y !* z), c) else Nothing
SMADTCheckSigAlg (SMAAssoc x y z (d, c)) =
  if d == (x !* y) !* z then Just (x !* (y !* z), c) else Nothing

public export
smadtCheckSig : SubstMorphADT -> Maybe (SubstObjMu, SubstObjMu)
smadtCheckSig = substMorphADTCata SMADTCheckSigAlg

----------------------------------------------------------------------
---- Interpretation of substitutive objects as metalanguage types ----
----------------------------------------------------------------------

public export
MetaSOTypeAlg : MetaSOAlg Type
MetaSOTypeAlg SO0 = Void
MetaSOTypeAlg SO1 = Unit
MetaSOTypeAlg (p !!+ q) = Either p q
MetaSOTypeAlg (p !!* q) = Pair p q

public export
MetaSOType : SubstObjMu -> Type
MetaSOType = substObjCata MetaSOTypeAlg

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Inductive definition of substitutive polynomial endofunctors ----
----------------------------------------------------------------------
----------------------------------------------------------------------

-----------------------------------------------------
---- Functor which generates polynomial functors ----
-----------------------------------------------------

infixr 8 $$+
infixr 9 $$*

public export
data PolyF : Type -> Type where
  -- Identity
  PFI : PolyF carrier

  -- Initial
  PF0 : PolyF carrier

  -- Terminal
  PF1 : PolyF carrier

  -- Coproduct
  ($$+) : carrier -> carrier -> PolyF carrier

  -- Product
  ($$*) : carrier -> carrier -> PolyF carrier

public export
Functor PolyF where
  map m PFI = PFI
  map m PF0 = PF0
  map m PF1 = PF1
  map m (p $$+ q) = m p $$+ m q
  map m (p $$* q) = m p $$* m q

public export
MetaPolyAlg : Type -> Type
MetaPolyAlg x = PolyF x -> x

public export
MetaPolyCoalg : Type -> Type
MetaPolyCoalg x = x -> PolyF x

-----------------------------------------------------------------------
---- Polynomial functors as least fixed point of generator functor ----
-----------------------------------------------------------------------

public export
data PolyMu : Type where
  InPCom : PolyF PolyMu -> PolyMu

infixr 8 $+
infixr 9 $*

public export
PolyI : PolyMu
PolyI = InPCom PFI

public export
Poly0 : PolyMu
Poly0 = InPCom PF0

public export
Poly1 : PolyMu
Poly1 = InPCom PF1

public export
($+) : PolyMu -> PolyMu -> PolyMu
($+) = InPCom .* ($$+)

public export
($*) : PolyMu -> PolyMu -> PolyMu
($*) = InPCom .* ($$*)

public export
metaPolyCata : MetaPolyAlg x -> PolyMu -> x
metaPolyCata alg = metaPolyFold id where
  mutual
    metaPolyCataCont : (x -> x -> PolyF x) ->
      (x -> x) -> PolyMu -> PolyMu -> x
    metaPolyCataCont op cont p q =
      metaPolyFold
        (\p' => metaPolyFold (\q' => cont $ alg $ op p' q') q) p

    metaPolyFold : (x -> x) -> PolyMu -> x
    metaPolyFold cont (InPCom p) = case p of
      PFI => cont (alg PFI)
      PF0 => cont (alg PF0)
      PF1 => cont (alg PF1)
      p $$+ q => metaPolyCataCont ($$+) cont p q
      p $$* q => metaPolyCataCont ($$*) cont p q

public export
data PolyNu : Type where
  InPLabel : Inf (PolyF PolyNu) -> PolyNu

public export
metaPolyAna : MetaPolyCoalg x -> x -> Inf PolyNu
metaPolyAna coalg = metaPolyUnfold id where
  mutual
    metaPolyAnaCont : (PolyNu -> PolyNu -> PolyF PolyNu) ->
      (PolyNu -> PolyNu) -> x -> x -> PolyNu
    metaPolyAnaCont op cont x y =
      metaPolyUnfold
        (\x' => metaPolyUnfold (\y' => cont $ InPLabel $ op x' y') y) x

    metaPolyUnfold : (PolyNu -> PolyNu) -> x -> Inf PolyNu
    metaPolyUnfold cont t = case coalg t of
      PFI => cont (InPLabel PFI)
      PF0 => cont (InPLabel PF0)
      PF1 => cont (InPLabel PF1)
      p $$+ q => metaPolyAnaCont ($$+) cont p q
      p $$* q => metaPolyAnaCont ($$*) cont p q

public export
MetaPolyPairAlg : Type -> Type
MetaPolyPairAlg x = MetaPolyAlg (PolyMu -> x)

public export
metaPolyPairCata : MetaPolyPairAlg x -> PolyMu -> PolyMu -> x
metaPolyPairCata = metaPolyCata

-------------------
---- Utilities ----
-------------------

public export
PolySizeAlg : MetaPolyAlg Nat
PolySizeAlg PFI = 1
PolySizeAlg PF0 = 1
PolySizeAlg PF1 = 1
PolySizeAlg (p $$+ q) = p + q
PolySizeAlg (p $$* q) = p + q

public export
polySize : PolyMu -> Nat
polySize = metaPolyCata PolySizeAlg

public export
PolyDepthAlg : MetaPolyAlg Nat
PolyDepthAlg PFI = 0
PolyDepthAlg PF0 = 0
PolyDepthAlg PF1 = 0
PolyDepthAlg (p $$+ q) = smax p q
PolyDepthAlg (p $$* q) = smax p q

public export
polyDepth : PolyMu -> Nat
polyDepth = metaPolyCata PolyDepthAlg

-- The cardinality of the type that would result from applying
-- the given polynomial to a type of the given cardinality.
public export
PolyCardAlg : Nat -> MetaPolyAlg Nat
PolyCardAlg n PFI = n
PolyCardAlg n PF0 = 0
PolyCardAlg n PF1 = 1
PolyCardAlg n (p $$+ q) = p + q
PolyCardAlg n (p $$* q) = p * q

public export
polyCard : Nat -> PolyMu -> Nat
polyCard = metaPolyCata . PolyCardAlg

public export
polyTCard : PolyMu -> Nat
polyTCard = polyCard 0

--------------------------------------------
---- Displaying polynomial endofunctors ----
--------------------------------------------

public export
PolyShowAlg : MetaPolyAlg String
PolyShowAlg PFI = "id"
PolyShowAlg PF0 = "0"
PolyShowAlg PF1 = "1"
PolyShowAlg (x $$+ y) = "(" ++ x ++ " + " ++ y ++ ")"
PolyShowAlg (x $$* y) = x ++ " * " ++ y

public export
Show PolyMu where
  show = metaPolyCata PolyShowAlg

---------------------------------------------
---- Equality on polynomial endofunctors ----
---------------------------------------------

public export
PolyMuEqAlg : MetaPolyPairAlg Bool
PolyMuEqAlg PFI (InPCom PFI) = True
PolyMuEqAlg PFI _ = False
PolyMuEqAlg PF0 (InPCom PF0) = True
PolyMuEqAlg PF0 _ = False
PolyMuEqAlg PF1 (InPCom PF1) = True
PolyMuEqAlg PF1 _ = False
PolyMuEqAlg (p $$+ q) (InPCom (r $$+ s)) = p r && q s
PolyMuEqAlg (p $$+ q) _ = False
PolyMuEqAlg (p $$* q) (InPCom (r $$* s)) = p r && q s
PolyMuEqAlg (p $$* q) _ = False

public export
Eq PolyMu where
  (==) = metaPolyPairCata PolyMuEqAlg

--------------------------------------------------
---- Normalization of polynomial endofunctors ----
--------------------------------------------------

public export
PolyRemoveZeroAlg : MetaPolyAlg PolyMu
PolyRemoveZeroAlg PFI = PolyI
PolyRemoveZeroAlg PF0 = Poly0
PolyRemoveZeroAlg PF1 = Poly1
PolyRemoveZeroAlg (p $$+ q) = case p of
  InPCom p' => case p' of
    PF0 => q
    _ => case q of
      InPCom q' => case q' of
        PF0 => p
        _ => p $+ q
PolyRemoveZeroAlg (p $$* q) = case p of
  InPCom p' => case p' of
    PF0 => Poly0
    _ => case q of
      InPCom q' => case q' of
        PF0 => Poly0
        _ => p $* q

public export
polyRemoveZero : PolyMu -> PolyMu
polyRemoveZero = metaPolyCata PolyRemoveZeroAlg

public export
PolyRemoveOneAlg : MetaPolyAlg PolyMu
PolyRemoveOneAlg PFI = PolyI
PolyRemoveOneAlg PF0 = Poly0
PolyRemoveOneAlg PF1 = Poly1
PolyRemoveOneAlg (p $$+ q) = p $+ q
PolyRemoveOneAlg (p $$* q) = case p of
  InPCom p' => case p' of
    PF1 => q
    _ => case q of
      InPCom q' => case q' of
        PF1 => p
        _ => p $* q

public export
polyRemoveOne : PolyMu -> PolyMu
polyRemoveOne = metaPolyCata PolyRemoveOneAlg

---------------------------------------------------------------
---- Composition of polynomial endofunctors (substitution) ----
---------------------------------------------------------------

public export
PolyComposeAlg : MetaPolyAlg (PolyMu -> PolyMu)
PolyComposeAlg PFI q = q
PolyComposeAlg PF0 _ = Poly0
PolyComposeAlg PF1 _ = Poly1
PolyComposeAlg (p $$+ q) r = p r $+ q r
PolyComposeAlg (p $$* q) r = p r $* q r

infixr 2 $.
public export
($.) : PolyMu -> PolyMu -> PolyMu
($.) = metaPolyCata PolyComposeAlg

-----------------------------------------------------
---- Multiplication by a constant (via addition) ----
-----------------------------------------------------

infix 10 $:*
public export
($:*) : Nat -> PolyMu -> PolyMu
n $:* p = foldrNatNoUnit (($+) p) Poly0 p n

---------------------------------------
---- Multiplicative exponentiation ----
---------------------------------------

infix 10 $*^
public export
($*^) : PolyMu -> Nat -> PolyMu
p $*^ n = foldrNatNoUnit (($*) p) Poly1 p n

--------------------------------------------------
---- Compositional exponentiation (iteration) ----
--------------------------------------------------

infix 10 $.^
public export
($.^) : PolyMu -> Nat -> PolyMu
p $.^ n = foldrNatNoUnit (($.) p) PolyI p n

---------------------------------------
---- Composition with zero and one ----
---------------------------------------

public export
polyAppZero : PolyMu -> PolyMu
polyAppZero p = polyRemoveZero (p $. Poly0)

public export
polyAppOne : PolyMu -> PolyMu
polyAppOne p = polyRemoveOne (p $. Poly1)

-------------------------------------------------
---- Conversion to and from algebraic format ----
-------------------------------------------------

public export
CountOnesAlg : MetaPolyAlg Nat
CountOnesAlg PFI = 0
CountOnesAlg PF0 = 0
CountOnesAlg PF1 = 1
CountOnesAlg (p $$+ q) = p + q
CountOnesAlg (p $$* q) = p + q

public export
countOnes : PolyMu -> Nat
countOnes = metaPolyCata CountOnesAlg

public export
CountIdsAlg : MetaPolyAlg Nat
CountIdsAlg PFI = 1
CountIdsAlg PF0 = 0
CountIdsAlg PF1 = 0
CountIdsAlg (p $$+ q) = p + q
CountIdsAlg (p $$* q) = p + q

public export
countIds : PolyMu -> Nat
countIds = metaPolyCata CountIdsAlg

public export
ToPolyShapeAlg : MetaPolyAlg PolyShape
ToPolyShapeAlg PFI = idPolyShape
ToPolyShapeAlg PF0 = initialPolyShape
ToPolyShapeAlg PF1 = terminalPolyShape
ToPolyShapeAlg (p $$+ q) = addPolyShape p q
ToPolyShapeAlg (p $$* q) = mulPolyShape p q

public export
toPolyShape : PolyMu -> PolyShape
toPolyShape = metaPolyCata ToPolyShapeAlg

public export
showPolyShape : PolyMu -> String
showPolyShape = show . toPolyShape

public export
polyPosShow : PolyMu -> String
polyPosShow = psPosShow . toPolyShape

-- Create a polynomial from a list of (power, coefficient) pairs.
public export
fromPolyShapeAcc : PolyShape -> PolyMu -> PolyMu
fromPolyShapeAcc [] q = q
fromPolyShapeAcc ((p, c) :: l) q =
  fromPolyShapeAcc l (c $:* (PolyI $*^ p) $+ q)

public export
fromPolyShape : PolyShape -> PolyMu
fromPolyShape l = fromPolyShapeAcc l Poly0

public export
polyDistrib : PolyMu -> PolyMu
polyDistrib = fromPolyShape . toPolyShape

-----------------------------------------------------------------------------
---- Interpretation of polynomial functors as natural-number polymomials ----
-----------------------------------------------------------------------------

public export
MetaPolyFNatAlg : MetaPolyAlg (Nat -> Nat)
MetaPolyFNatAlg PFI = id
MetaPolyFNatAlg PF0 = const 0
MetaPolyFNatAlg PF1 = const 1
MetaPolyFNatAlg (p $$+ q) = \n => p n + q n
MetaPolyFNatAlg (p $$* q) = \n => p n * q n

public export
MetaPolyFNat : PolyMu -> Nat -> Nat
MetaPolyFNat = metaPolyCata MetaPolyFNatAlg

----------------------------------------------------------
---- Exponentiation (hom-objects) of polynomial types ----
----------------------------------------------------------

public export
PolyHomObjAlg : MetaPolyAlg (PolyMu -> PolyMu)
-- id -> r == r . (id + 1) (see formula 4.27 in _Polynomial Functors: A General
-- Theory of Interaction_)
PolyHomObjAlg PFI r = r $. (PolyI $+ Poly1)
-- 0 -> x == 1
PolyHomObjAlg PF0 _ = Poly1
-- 1 -> x == x
PolyHomObjAlg PF1 q = q
-- (p + q) -> r == (p -> r) * (q -> r)
PolyHomObjAlg (p $$+ q) r = p r $* q r
-- (p * q) -> r == p -> q -> r
PolyHomObjAlg (p $$* q) r = p $ q r

public export
PolyHomObj : PolyMu -> PolyMu -> PolyMu
PolyHomObj = metaPolyCata PolyHomObjAlg

public export
PolyExp : PolyMu -> PolyMu -> PolyMu
PolyExp = flip PolyHomObj

---------------------------------
---- Natural transformations ----
---------------------------------

public export
data PolyMuNT : PolyMu -> PolyMu -> Type where

----------------------------------------
---- Polynomial monads and comonads ----
----------------------------------------

public export
record PolyMonad where
  constructor MkPolyMonad
  pmFunctor : PolyMu
  pmUnit : PolyMuNT PolyI pmFunctor
  pmMul : PolyMuNT (pmFunctor $.^ 2) pmFunctor

public export
record PolyComonad where
  constructor MkPolyComonad
  pmFunctor : PolyMu
  pmEraser : PolyMuNT pmFunctor PolyI
  pmDuplicator : PolyMuNT pmFunctor (pmFunctor $.^ 2)

------------------------------------------------------------------------
---- Interpretation of polynomial functors as metalanguage functors ----
------------------------------------------------------------------------

public export
MetaPolyMetaFAlg : MetaPolyAlg (Type -> Type)
MetaPolyMetaFAlg PFI = id
MetaPolyMetaFAlg PF0 = const Void
MetaPolyMetaFAlg PF1 = const Unit
MetaPolyMetaFAlg (p $$+ q) = CoproductF p q
MetaPolyMetaFAlg (p $$* q) = ProductF p q

public export
MetaPolyFMetaF : PolyMu -> Type -> Type
MetaPolyFMetaF = metaPolyCata MetaPolyMetaFAlg

public export
ConstComponent : PolyMu -> Type
ConstComponent p = MetaPolyFMetaF (polyAppZero p) Void

public export
PositionType : PolyMu -> Type
PositionType p = MetaPolyFMetaF (polyAppOne p) Unit

---------------------------------------------------
---- The free monad in the polynomial category ----
---------------------------------------------------

public export
MetaPolyFreeM : PolyMu -> (0 _ : Type) -> Type
MetaPolyFreeM (InPCom p) = FreeM (MetaPolyFMetaF $ InPCom p)

public export
MetaPolyMu : PolyMu -> Type
MetaPolyMu p = MetaPolyFreeM p Void

-------------------------------------------------------------
-------------------------------------------------------------
---- Natural numbers as objects representing finite sets ----
-------------------------------------------------------------
-------------------------------------------------------------

-- Define and translate two ways of interpreting natural numbers.

---------------------------------------
---- Bounded unary natural numbers ----
---------------------------------------

-- First, as coproducts of Unit.  As such, they are the first non-trivial
-- objects that can be formed in a category which is inductively defined as
-- the smallest one containing only (all) finite coproducts and finite products.
-- In this form, they are unary natural numbers, often suited as indexes.

public export
BUNat : Nat -> Type
BUNat Z = Void
BUNat (S n) = Either Unit (BUNat n)

public export
BUNatDepAlg :
  {0 p : (n : Nat) -> BUNat n -> Type} ->
  ((n : Nat) -> p (S n) (Left ())) ->
  ((n : Nat) ->
   ((bu : BUNat n) -> p n bu) ->
   (bu : BUNat n) -> p (S n) (Right bu)) ->
  NatDepAlgebra (\n => (bu : BUNat n) -> p n bu)
BUNatDepAlg {p} z s =
  (\bu => void bu,
   \n, hyp, bu => case bu of
    Left () => z n
    Right bu' => s n hyp bu')

public export
buNatDepCata :
  {0 p : (n : Nat) -> BUNat n -> Type} ->
  ((n : Nat) -> p (S n) (Left ())) ->
  ((n : Nat) ->
   ((bu : BUNat n) -> p n bu) ->
   (bu : BUNat n) -> p (S n) (Right bu)) ->
  (n : Nat) -> (bu : BUNat n) -> p n bu
buNatDepCata {p} z s = natDepCata (BUNatDepAlg {p} z s)

--------------------------------------------
---- Bounded arithmetic natural numbers ----
--------------------------------------------

-- Second, as bounds, which allow us to do bounded arithmetic,
-- or arithmetic modulo a given number.

public export
BoundedBy : Nat -> DecPred Nat
BoundedBy = gt

public export
NotBoundedBy : Nat -> DecPred Nat
NotBoundedBy = not .* BoundedBy

public export
IsBoundedBy : Nat -> Nat -> Type
IsBoundedBy = Satisfies . BoundedBy

public export
BANat : (0 _ : Nat) -> Type
BANat n = Refinement {a=Nat} (BoundedBy n)

public export
MkBANat : {0 n : Nat} -> (m : Nat) -> {auto 0 satisfies : IsBoundedBy n m} ->
  BANat n
MkBANat = MkRefinement

public export
baS : {0 n : Nat} -> BANat n -> BANat (S n)
baS (Element0 m lt) = Element0 (S m) lt

public export
baShowLong : {n : Nat} -> BANat n -> String
baShowLong {n} m = show m ++ "[<" ++ show n ++ "]"

public export
baNatDepCata :
  {0 p : (n : Nat) -> BANat n -> Type} ->
  ((n : Nat) -> p (S n) (Element0 0 Refl)) ->
  ((n : Nat) ->
   ((ba : BANat n) -> p n ba) ->
   (ba : BANat n) -> p (S n) (baS {n} ba)) ->
  (n : Nat) -> (ba : BANat n) -> p n ba
baNatDepCata {p} z s =
  natDepCata {p=(\n' => (ba' : BANat n') -> p n' ba')}
    (\ba => case ba of Element0 ba' Refl impossible,
     \n, hyp, ba => case ba of
      Element0 Z lt => rewrite uip {eq=lt} {eq'=Refl} in z n
      Element0 (S ba') lt => s n hyp (Element0 ba' lt))

-------------------------------------------------------------------
---- Translation between unary and arithmetic bounded naturals ----
-------------------------------------------------------------------

public export
u2a : {n : Nat} -> BUNat n -> BANat n
u2a {n=Z} v = void v
u2a {n=(S n)} (Left ()) = Element0 0 Refl
u2a {n=(S n)} (Right bu) with (u2a bu)
  u2a {n=(S n)} (Right bu) | Element0 bu' lt = Element0 (S bu') lt

public export
a2u : {n : Nat} -> BANat n -> BUNat n
a2u {n=Z} (Element0 ba Refl) impossible
a2u {n=(S n)} (Element0 Z lt) = Left ()
a2u {n=(S n)} (Element0 (S ba) lt) = Right $ a2u $ Element0 ba lt

public export
u2a2u_correct : {n : Nat} -> {bu : BUNat n} -> bu = a2u {n} (u2a {n} bu)
u2a2u_correct {n=Z} {bu} = void bu
u2a2u_correct {n=(S n)} {bu=(Left ())} = Refl
u2a2u_correct {n=(S n)} {bu=(Right bu)} with (u2a bu) proof eq
  u2a2u_correct {n=(S n)} {bu=(Right bu)} | Element0 m lt =
    rewrite (sym eq) in cong Right $ u2a2u_correct {n} {bu}

public export
a2u2a_fst_correct : {n : Nat} -> {ba : BANat n} ->
  fst0 ba = fst0 (u2a {n} (a2u {n} ba))
a2u2a_fst_correct {n=Z} {ba=(Element0 ba Refl)} impossible
a2u2a_fst_correct {n=(S n)} {ba=(Element0 Z lt)} = Refl
a2u2a_fst_correct {n=(S n)} {ba=(Element0 (S ba) lt)}
  with (u2a (a2u (Element0 ba lt))) proof p
    a2u2a_fst_correct {n=(S n)} {ba=(Element0 (S ba) lt)} | Element0 ba' lt' =
      cong S $ trans (a2u2a_fst_correct {ba=(Element0 ba lt)}) $ cong fst0 p

public export
a2u2a_correct : {n : Nat} -> {ba : BANat n} -> ba = u2a {n} (a2u {n} ba)
a2u2a_correct {n} {ba} = refinementFstEq $ a2u2a_fst_correct {n} {ba}

public export
MkBUNat : {n : Nat} -> (m : Nat) -> {auto 0 satisfies : IsBoundedBy n m} ->
  BUNat n
MkBUNat m {satisfies} = a2u (MkBANat m {satisfies})

public export
up2a : {n : Nat} -> (BUNat n -> Type) -> BANat n -> Type
up2a p ba = p (a2u ba)

public export
ap2u : {n : Nat} -> (BANat n -> Type) -> BUNat n -> Type
ap2u p bu = p (u2a bu)

public export
up2a_rewrite : {0 n : Nat} -> {0 p : BUNat n -> Type} ->
  {0 bu : BUNat n} -> p bu -> up2a {n} p (u2a {n} bu)
up2a_rewrite {p} t = replace {p} u2a2u_correct t

public export
ap2u_rewrite : {0 n : Nat} -> {0 p : BANat n -> Type} ->
  {0 ba : BANat n} -> p ba -> ap2u {n} p (a2u {n} ba)
ap2u_rewrite {p} t = replace {p} a2u2a_correct t

----------------------------------------
---- Bounded-natural-number objects ----
----------------------------------------

-- The bounded natural numbers can be interpreted as a category whose
-- objects are simply natural numbers (which give the bounds) and whose
-- morphisms are the polynomial circuit operations modulo the bounds.
-- An object is therefore specified simply by a natural number, and
-- interpreted as a Nat-bounded set.

public export
BNCatObj : Type
BNCatObj = Nat

-- We can interpret objects of the natural-number-bounded category as
-- bounded unary representations of Nat.
public export
bncInterpU : BNCatObj -> Type
bncInterpU = BUNat

-- We can also interpreted a `BNCatObj` as an arithmetic Nat-bounded set.
-- bounded unary representations of Nat.
public export
bncObjA : (0 _ : BNCatObj) -> Type
bncObjA = BANat

-- The simplest morphisms of the Nat-bounded-set category are specified
-- by spelling out, for each term of the domain, which term of the codomain
-- it maps to.
public export
BNCListMorph : Type
BNCListMorph = List Nat

-- For a given BNCListMorph, we can check whether it is a valid morphism
-- between a given pair of objects.
public export
checkVBNCLM : BNCatObj -> BNCatObj -> DecPred BNCListMorph
checkVBNCLM Z _ [] = True
checkVBNCLM Z _ (_ :: _) = False
checkVBNCLM (S _) _ [] = False
checkVBNCLM (S m') n (k :: ks) = BoundedBy n k && checkVBNCLM m' n ks

public export
isVBNCLM : BNCatObj -> BNCatObj -> BNCListMorph -> Type
isVBNCLM = Satisfies .* checkVBNCLM

-- Given a pair of objects, we can define a type dependent on those
-- objects representing just those BNCListMorphs which are valid
-- morphisms between those particular objects.

public export
VBNCLM : BNCatObj -> BNCatObj -> Type
VBNCLM m n = Refinement {a=BNCListMorph} $ checkVBNCLM m n

public export
MkVBNCLM : {0 m, n : BNCatObj} -> (l : BNCListMorph) ->
  {auto 0 satisfies : isVBNCLM m n l} -> VBNCLM m n
MkVBNCLM l {satisfies} = MkRefinement l {satisfies}

-- We can interpret a valid list-specified morphism as a function
-- of the metalanguage.
public export
bncLMA : {m, n : BNCatObj} -> VBNCLM m n -> BANat m -> BANat n
bncLMA {m=Z} {n} (Element0 [] kvalid) (Element0 p pvalid) = exfalsoFT pvalid
bncLMA {m=(S _)} {n} (Element0 [] kvalid) vp = exfalsoFT kvalid
bncLMA {m=(S m)} {n} (Element0 (k :: ks) kvalid) (Element0 Z pvalid) =
  Element0 k (andLeft kvalid)
bncLMA {m=(S m)} {n} (Element0 (k :: ks) kvalid) (Element0 (S p) pvalid) =
  bncLMA {m} {n} (Element0 ks (andRight kvalid)) (Element0 p pvalid)

-- Utility function for applying a bncLMA to a Nat that can be
-- validated at compile time as satisfying the bounds.
public export
bncLMAN : {m, n : BNCatObj} -> VBNCLM m n -> (k : Nat) ->
  {auto 0 satisfies : IsBoundedBy m k} -> BANat n
bncLMAN lm k {satisfies} = bncLMA lm $ MkBANat k {satisfies}

-- Utility function for applying bncLMAN and then forgetting the
-- constraint on the output.
public export
bncLMANN : {m, n : BNCatObj} -> VBNCLM m n -> (k : Nat) ->
  {auto 0 satisfies : IsBoundedBy m k} -> Nat
bncLMANN l k {satisfies} = fst0 $ bncLMAN l k {satisfies}

-- Another class of morphism in the category of bounded arithmetic
-- natural numbers is the polynomial functions -- constants, addition,
-- multiplication.  Because we are so far defining only a "single-variable"
-- category, we can make all such morphisms valid (as opposed to invalid if
-- they fail bound checks) by performing the arithmetic modulo the sizes
-- of the domain and codomain.

-- Thus we can in particular interpret any metalanguage function on the
-- natural numbers as a function from any BANat object to any non-empty
-- BANat object by post-composing with modulus.

public export
metaToNatToBNC : {n : Nat} -> (Integer -> Integer) -> Nat -> BANat (S n)
metaToNatToBNC {n} f k =
  let
    k' = natToInteger k
    fk = integerToNat $ f k'
  in
  Element0 (modNatNZ fk (S n) SIsNonZero) (modLtDivisor fk n)

public export
metaToBNCToBNC : {m, n : Nat} -> (Integer -> Integer) -> BANat m -> BANat (S n)
metaToBNCToBNC f (Element0 k _) = metaToNatToBNC {n} f k

-- Object-language representation of polynomial morphisms.

prefix 11 #|
infixr 8 #+
infix 8 #-
infixr 9 #*
infix 9 #/
infix 9 #%
infixr 2 #.

public export
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

public export
record BNCPolyMAlg (0 a : BNCPolyM -> Type) where
  constructor MkBNCPolyAlg
  bncaConst : (n : Nat) -> a (#| n)
  bncaId : a PI
  bncaCompose : (q, p : BNCPolyM) -> a q -> a p -> a (q #. p)
  bncaAdd : (p, q : BNCPolyM) -> a p -> a q -> a (p #+ q)
  bncaMul : (p, q : BNCPolyM) -> a p -> a q -> a (p #* q)
  bncaSub : (p, q : BNCPolyM) -> a p -> a q -> a (p #- q)
  bncaDiv : (p, q : BNCPolyM) -> a p -> a q -> a (p #/ q)
  bncaMod : (p, q : BNCPolyM) -> a p -> a q -> a (p #% q)
  bncaIfZ : (p, q, r : BNCPolyM) -> a p -> a q -> a r -> a (IfZero p q r)

public export
bncPolyMInd : {0 a : BNCPolyM -> Type} -> BNCPolyMAlg a -> (p : BNCPolyM) -> a p
bncPolyMInd alg (#| k) = bncaConst alg k
bncPolyMInd alg PI = bncaId alg
bncPolyMInd alg (q #. p) =
  bncaCompose alg q p (bncPolyMInd alg q) (bncPolyMInd alg p)
bncPolyMInd alg (p #+ q) =
  bncaAdd alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #* q) =
  bncaMul alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #- q) =
  bncaSub alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #/ q) =
  bncaDiv alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #% q) =
  bncaMod alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (IfZero p q r) =
  bncaIfZ alg p q r (bncPolyMInd alg p) (bncPolyMInd alg q) (bncPolyMInd alg r)

public export
showInfix : (is, ls, rs : String) -> String
showInfix is ls rs = "(" ++ ls ++ ") " ++ is ++ " (" ++ rs ++ ")"

public export
const2ShowInfix : {0 a, b : Type} ->
  (is : String) -> a -> b -> (ls, rs : String) -> String
const2ShowInfix is _ _ = showInfix is

public export
BNCPMshowAlg : BNCPolyMAlg (const String)
BNCPMshowAlg = MkBNCPolyAlg
  show
  "PI"
  (const2ShowInfix ".")
  (const2ShowInfix "+")
  (const2ShowInfix "*")
  (const2ShowInfix "-")
  (const2ShowInfix "/")
  (const2ShowInfix "%")
  (\_, _, _, ps, qs, rs =>
    "(" ++ ps ++ " == 0 ? " ++ show qs ++ " : " ++ show rs ++ ")")

public export
Show BNCPolyM where
  show  = bncPolyMInd BNCPMshowAlg

public export
P0 : BNCPolyM
P0 = #| 0

public export
P1 : BNCPolyM
P1 = #| 1

public export
powerAcc : BNCPolyM -> Nat -> BNCPolyM -> BNCPolyM
powerAcc p Z acc = acc
powerAcc p (S n) acc = powerAcc p n (p #* acc)

infixl 10 #^
public export
(#^) : BNCPolyM -> Nat -> BNCPolyM
(#^) p n = powerAcc p n P1

-- Interpret a BNCPolyM into the metalanguage.
public export
MetaBNCPolyMAlg : BNCPolyMAlg (\_ => (modpred : Integer) -> Integer -> Integer)
MetaBNCPolyMAlg = MkBNCPolyAlg
  (\n, modpred, _ => modSucc (natToInteger n) modpred)
  (\modpred, k => modSucc k modpred)
  (\q, p, qf, pf, modpred, k => qf modpred (pf modpred k))
  (\p, q, pf, qf, modpred, k =>
    flip modSucc modpred $ pf modpred k + qf modpred k)
  (\p, q, pf, qf, modpred, k =>
    flip modSucc modpred $ pf modpred k * qf modpred k)
  (\p, q, pf, qf, modpred, k =>
    minusModulo (modpred + 1) (pf modpred k) (qf modpred k))
  (\p, q, pf, qf, modpred, k =>
    divWithZtoZ (pf modpred k) (qf modpred k))
  (\p, q, pf, qf, modpred, k =>
    modWithZtoZ (pf modpred k) (qf modpred k))
  (\p, q, r, pf, qf, rf, modpred, k =>
    if pf modpred k == 0 then
      qf modpred k
    else
      rf modpred k)

public export
metaBNCPolyM : (modpred : Integer) -> BNCPolyM -> Integer -> Integer
metaBNCPolyM modpred p = bncPolyMInd MetaBNCPolyMAlg p modpred

-- Interpret a BNCPolyM as a function between BANat objects.
public export
baPolyM : {m, n : Nat} -> BNCPolyM -> BANat m -> BANat (S n)
baPolyM {n} p = metaToBNCToBNC (metaBNCPolyM (natToInteger n) p)

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Compilation of finite polynomial types to circuit operations ----
----------------------------------------------------------------------
----------------------------------------------------------------------

public export
substObjToNat : SubstObjMu -> Nat
substObjToNat = substObjCard

public export
substMorphToBNC : {x, y : SubstObjMu} -> SubstMorph x y -> BNCPolyM
substMorphToBNC {y=x} (SMId x) = PI
substMorphToBNC ((<!) {x} {y} {z} g f) = substMorphToBNC g #. substMorphToBNC f
substMorphToBNC {x=Subst0} (SMFromInit y) = #| 0
substMorphToBNC {y=Subst1} (SMToTerminal x) = #| 1
substMorphToBNC (SMInjLeft x y) = PI
substMorphToBNC (SMInjRight x y) = #| (substObjToNat x) #+ PI
substMorphToBNC (SMCase {x} {y} {z} f g) with (substObjToNat x)
  substMorphToBNC (SMCase {x} {y} {z} f g) | cx =
    if cx == 0 then
      substMorphToBNC g
    else
      IfZero
        (PI #/ #| cx)
        (substMorphToBNC f)
        (substMorphToBNC g #. PI #- #| cx)
substMorphToBNC (SMPair {x} {y} {z} f g) with (substObjToNat x, substObjToNat y)
  substMorphToBNC (SMPair {x} {y} {z} f g) | (cx, cy) =
    #| cy #* substMorphToBNC f #+ substMorphToBNC g
substMorphToBNC (SMProjLeft x y) with (substObjToNat x, substObjToNat y)
  substMorphToBNC (SMProjLeft x y) | (cx, cy) =
    if cy == 0 then
      #| 0
    else
      PI #/ #| cy
substMorphToBNC (SMProjRight x y) with (substObjToNat x, substObjToNat y)
  substMorphToBNC (SMProjRight x y) | (cx, cy) =
    if cy == 0 then
      #| 0
    else
      PI #% #| cy
substMorphToBNC (SMDistrib x y z) = PI

---------------------------------------------------
---------------------------------------------------
---- Older version of polynomial-type category ----
---------------------------------------------------
---------------------------------------------------

public export
MetaSOMorph : SubstObjMu -> SubstObjMu -> Type
-- The unique morphism from the initial object to a given object
MetaSOMorph (InSO SO0) _ = ()
-- There are no morphisms from the terminal object to the initial object
MetaSOMorph (InSO SO1) (InSO SO0) = Void
-- The unique morphism from a given object to the terminal object
-- (in this case, the given object is also the terminal object)
MetaSOMorph (InSO SO1) (InSO SO1) = Unit
-- To form a morphism from the terminal object to a coproduct,
-- we choose a morphism from the terminal object to either the left
-- or the right object of the coproduct
MetaSOMorph (InSO SO1) (InSO (y !!+ z)) =
  Either (MetaSOMorph Subst1 y) (MetaSOMorph Subst1 z)
-- To form a morphism from the terminal object to a product,
-- we choose morphisms from the terminal object to both the left
-- and the right object of the product
MetaSOMorph (InSO SO1) (InSO (y !!* z)) =
  Pair (MetaSOMorph Subst1 y) (MetaSOMorph Subst1 z)
-- The unique morphism from a coproduct to the terminal object
MetaSOMorph (InSO (_ !!+ _)) (InSO SO1) = ()
-- Coproducts are eliminated by cases
MetaSOMorph (InSO (x !!+ y)) z = Pair (MetaSOMorph x z) (MetaSOMorph y z)
-- The unique morphism from a product to the terminal object
MetaSOMorph (InSO (_ !!* _)) (InSO SO1) = ()
-- 0 * y === 0
MetaSOMorph (InSO ((InSO SO0) !!* y)) z = ()
-- 1 * y === y
MetaSOMorph (InSO ((InSO SO1) !!* y)) z = MetaSOMorph y z
-- Distributivity of products over coproducts
MetaSOMorph (InSO ((InSO (x !!+ x')) !!* y)) z =
  MetaSOMorph ((x !* y) !+ (x' !* y)) z
-- Associativity of products
MetaSOMorph (InSO ((InSO (x !!* x')) !!* y)) z = MetaSOMorph (x !* (x' !* y)) z

-----------------------------------------------------------
-----------------------------------------------------------
---- Idris representation of substitutive finite topos ----
-----------------------------------------------------------
-----------------------------------------------------------

-- A finite type, generated only from initial and terminal objects
-- and coproducts and products, which is indexed by a natural-number size
-- (which is the cardinality of the set of the type's elements).
public export
data FinSubstT : (0 cardinality, depth : Nat) -> Type where
  FinInitial : FinSubstT 0 0
  FinTerminal : FinSubstT 1 0
  FinCoproduct : {0 cx, dx, cy, dy : Nat} ->
    FinSubstT cx dx -> FinSubstT cy dy -> FinSubstT (cx + cy) (smax dx dy)
  FinProduct : {0 cx, dx, cy, dy : Nat} ->
    FinSubstT cx dx -> FinSubstT cy dy -> FinSubstT (cx * cy) (smax dx dy)

public export
record FSAlg (0 a : (0 c, d : Nat) -> FinSubstT c d -> Type) where
  constructor MkFSAlg
  fsInitialAlg : a 0 0 FinInitial
  fsTerminalAlg : a 1 0 FinTerminal
  fsCoproductAlg : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    a cx dx x -> a cy dy y -> a (cx + cy) (smax dx dy) (FinCoproduct x y)
  fsProductAlg : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    a cx dx x -> a cy dy y -> a (cx * cy) (smax dx dy) (FinProduct x y)

public export
finSubstCata :
  {0 a : (0 c, d : Nat) -> FinSubstT c d -> Type} ->
  FSAlg a ->
  {0 cardinality, depth : Nat} ->
  (x : FinSubstT cardinality depth) -> a cardinality depth x
finSubstCata alg FinInitial = alg.fsInitialAlg
finSubstCata alg FinTerminal = alg.fsTerminalAlg
finSubstCata alg (FinCoproduct x y) =
  alg.fsCoproductAlg x y (finSubstCata alg x) (finSubstCata alg y)
finSubstCata alg (FinProduct x y) =
  alg.fsProductAlg x y (finSubstCata alg x) (finSubstCata alg y)

public export
data FinSubstTerm : {0 c, d : Nat} -> FinSubstT c d -> Type where
  FinUnit : FinSubstTerm FinTerminal
  FinLeft :
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    FinSubstTerm x -> FinSubstTerm (FinCoproduct x y)
  FinRight :
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    FinSubstTerm y -> FinSubstTerm (FinCoproduct x y)
  FinPair :
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    FinSubstTerm x -> FinSubstTerm y -> FinSubstTerm (FinProduct x y)

public export
record FSTAlg
    (0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type)
    where
  constructor MkFSTAlg
  fstUnit : a 1 0 FinTerminal FinUnit
  fstLeft : {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm x) ->
    a cx dx x t ->
    a (cx + cy) (smax dx dy) (FinCoproduct x y) (FinLeft t)
  fstRight : {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm y) ->
    a cy dy y t ->
    a (cx + cy) (smax dx dy) (FinCoproduct x y) (FinRight t)
  fstPair : {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm x) -> (t' : FinSubstTerm y) ->
    a cx dx x t -> a cy dy y t' ->
    a (cx * cy) (smax dx dy) (FinProduct x y) (FinPair t t')

mutual
  public export
  fstCata :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    FSTAlg a ->
    {0 c, d : Nat} -> {x : FinSubstT c d} ->
    (t : FinSubstTerm x) -> a c d x t
  fstCata {a} alg {x=FinInitial} = fstCataInitial {a}
  fstCata {a} alg {x=FinTerminal} = fstCataTerminal {a} alg
  fstCata {a} alg {x=(FinCoproduct x y)} = fstCataCoproduct {a} alg {x} {y}
  fstCata {a} alg {x=(FinProduct x y)} = fstCataProduct {a} alg {x} {y}

  public export
  fstCataInitial :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    (t : FinSubstTerm FinInitial) -> a _ _ FinInitial t
  fstCataInitial FinUnit impossible
  fstCataInitial (FinLeft x) impossible
  fstCataInitial (FinRight x) impossible
  fstCataInitial (FinPair x y) impossible

  public export
  fstCataTerminal :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    FSTAlg a ->
    (t : FinSubstTerm FinTerminal) -> a _ _ FinTerminal t
  fstCataTerminal alg FinUnit = alg.fstUnit

  public export
  fstCataCoproduct :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    FSTAlg a ->
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm (FinCoproduct x y)) ->
    a _ _ (FinCoproduct x y) t
  fstCataCoproduct alg (FinLeft t) = alg.fstLeft t $ fstCata alg t
  fstCataCoproduct alg (FinRight t) = alg.fstRight t $ fstCata alg t

  public export
  fstCataProduct :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    FSTAlg a ->
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm (FinProduct x y)) ->
    a _  _ (FinProduct x y) t
  fstCataProduct alg (FinPair t t') =
    alg.fstPair t t' (fstCata alg t) (fstCata alg t')

public export
data FinSubstMorph : {0 cx, dx, cy, dy : Nat} ->
    (0 depth : Nat) -> FinSubstT cx dx -> FinSubstT cy dy -> Type where
  FinId : {0 cx, dx : Nat} ->
    (x : FinSubstT cx dx) -> FinSubstMorph {cx} {cy=cx} 0 x x
  FinCompose : {0 cx, dx, cy, dy, cz, dz : Nat} -> {0 dg, df : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} -> {z : FinSubstT cz dz} ->
    FinSubstMorph dg y z -> FinSubstMorph df x y ->
    FinSubstMorph (smax dg df) x z
  FinFromInit : {0 cy, dy : Nat} -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx=0} {cy} 0 FinInitial y
  FinToTerminal : {0 cx, dx : Nat} -> (x : FinSubstT cx dx) ->
    FinSubstMorph {cx} {cy=1} 0 x FinTerminal
  FinInjLeft : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx} {cy=(cx + cy)} 0 x (FinCoproduct {cx} {cy} x y)
  FinInjRight : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx=cy} {cy=(cx + cy)} 0 y (FinCoproduct {cx} {cy} x y)
  FinCase : {0 cx, dx, cy, dy, cz, dz : Nat} -> {0 df, dg : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} -> {z : FinSubstT cz dz} ->
    FinSubstMorph {cx} {cy=cz} df x z ->
    FinSubstMorph {cx=cy} {cy=cz} dg y z ->
    FinSubstMorph {cx=(cx + cy)} {cy=cz}
      (smax df dg) (FinCoproduct {cx} {cy} x y) z
  FinProd : {0 cx, dx, cy, dy, cz, dz : Nat} -> {0 df, dg : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} -> {z : FinSubstT cz dz} ->
    FinSubstMorph {cx} {cy} df x y ->
    FinSubstMorph {cx} {cy=cz} dg x z ->
    FinSubstMorph {cx} {cy=(cy * cz)} (smax df dg) x
      (FinProduct {cx=cy} {cy=cz} y z)
  FinProjLeft : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx=(cx * cy)} {cy=cx} 0 (FinProduct {cx} {cy} x y) x
  FinProjRight : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx=(cx * cy)} {cy} 0 (FinProduct {cx} {cy} x y) y
  FinDistrib : {0 cx, dx, cy, dy, cz, dz : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) -> (z : FinSubstT cz dz) ->
    FinSubstMorph 0
      (FinProduct x (FinCoproduct y z))
      (FinCoproduct (FinProduct x y) (FinProduct x z))

public export
0 finSubstHomObjCard : {0 cx, dx, cy, dy : Nat} ->
  FinSubstT cx dx -> FinSubstT cy dy -> Nat
finSubstHomObjCard {cx} {cy} _ _ = power cy cx

public export
EvalMorphType : {0 cx, dx, cy, dy, dh : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  FinSubstT (finSubstHomObjCard x y) dh -> (0 df : Nat) -> Type
EvalMorphType x y hxy df = FinSubstMorph df (FinProduct hxy x) y

public export
HomObjWithEvalMorphType : {0 cx, dx, cy, dy : Nat} ->
  FinSubstT cx dx -> FinSubstT cy dy -> (0 dh : Nat) -> Type
HomObjWithEvalMorphType x y dh =
  (hxy : FinSubstT (finSubstHomObjCard x y) dh **
   Exists0 Nat (EvalMorphType x y hxy))

-- Compute the exponential object and evaluation morphism of the given finite
-- substitutive types.
public export
FinSubstHomDepthObjEval : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  Exists0 Nat (HomObjWithEvalMorphType x y)
-- 0 -> x == 1
FinSubstHomDepthObjEval FinInitial x =
  (Evidence0 0 (FinTerminal **
    Evidence0 1 $
      FinCompose (FinFromInit x) $ FinProjRight FinTerminal FinInitial))
-- 1 -> x == x
FinSubstHomDepthObjEval {cy} {dy} FinTerminal x =
  let eq = mulPowerZeroRightNeutral {m=cy} {n=cy} in
  (Evidence0 dy $ rewrite eq in (x **
   Evidence0 0 $ rewrite eq in FinProjLeft x FinTerminal))
-- (x + y) -> z == (x -> z) * (y -> z)
FinSubstHomDepthObjEval {cx=(cx + cy)} {cy=cz} (FinCoproduct x y) z with
 (FinSubstHomDepthObjEval x z, FinSubstHomDepthObjEval y z)
  FinSubstHomDepthObjEval {cx=(cx + cy)} {cy=cz} (FinCoproduct x y) z |
   ((Evidence0 dxz (hxz ** (Evidence0 hdxz evalxz))),
    (Evidence0 dyz (hyz ** (Evidence0 hdyz evalyz)))) =
    (Evidence0 (smax dxz dyz) $ rewrite powerOfSum cz cx cy in
     (FinProduct hxz hyz ** Evidence0
      (S (maximum (smax hdxz hdyz) 5))
      $
      rewrite powerOfSum cz cx cy in
      FinCompose (FinCase evalxz evalyz) $ FinCompose
        (FinCase
          (FinCompose (FinInjLeft _ _)
            (FinProd (FinCompose (FinProjLeft _ _) (FinProjLeft _ _))
              (FinProjRight _ _)))
          (FinCompose (FinInjRight _ _)
            (FinProd (FinCompose (FinProjRight _ _) (FinProjLeft _ _))
              (FinProjRight _ _))))
        (FinDistrib (FinProduct hxz hyz) x y)))
-- (x * y) -> z == x -> y -> z
FinSubstHomDepthObjEval {cx=(cx * cy)} {dx=(smax dx dy)} {cy=cz} {dy=dz}
  (FinProduct x y) z with
  (FinSubstHomDepthObjEval y z)
    FinSubstHomDepthObjEval {cx=(cx * cy)} {dx=(smax dx dy)} {cy=cz} {dy=dz}
      (FinProduct x y) z | (Evidence0 dyz (hyz ** Evidence0 hdyz evalyz)) =
        let
          Evidence0 dxyz hexyz = FinSubstHomDepthObjEval {dx} {dy=dyz} x hyz
          (hxyz ** Evidence0 dexyz evalxyz) = hexyz
        in
        Evidence0 dxyz $ rewrite powerOfMulSym cz cx cy in
          (hxyz ** Evidence0 (smax hdyz (smax (smax dexyz 2) 1)) $
            rewrite powerOfMulSym cz cx cy in
            FinCompose evalyz $ FinProd
              (FinCompose evalxyz
               (FinProd
                (FinProjLeft hxyz (FinProduct x y))
                (FinCompose
                  (FinProjLeft x y) (FinProjRight hxyz (FinProduct x y)))))
              (FinCompose
                (FinProjRight x y) (FinProjRight hxyz (FinProduct x y))))

public export
0 finSubstHomObjDepth : {0 cx, dx, cy, dy : Nat} ->
  FinSubstT cx dx -> FinSubstT cy dy -> Nat
finSubstHomObjDepth x y = fst0 $ FinSubstHomDepthObjEval x y

public export
finSubstHomObj : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  FinSubstT (finSubstHomObjCard x y) (finSubstHomObjDepth x y)
finSubstHomObj x y = fst $ snd0 $ FinSubstHomDepthObjEval x y

public export
0 finSubstEvalMorphDepth : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  Nat
finSubstEvalMorphDepth x y = fst0 (snd (snd0 (FinSubstHomDepthObjEval x y)))

public export
finSubstEvalMorph : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  EvalMorphType x y (finSubstHomObj x y) (finSubstEvalMorphDepth x y)
finSubstEvalMorph x y = snd0 $ snd $ snd0 $ FinSubstHomDepthObjEval x y

------------------------------------
---- Compilation to polynomials ----
------------------------------------

public export
FSToBANatMorph : {0 cx, dx, cy, dy : Nat} ->
  {0 depth : Nat} -> {dom : FinSubstT cx dx} -> {cod : FinSubstT cy dy} ->
  FinSubstMorph depth dom cod ->
  BNCPolyM
FSToBANatMorph {cx} {dx} {cy} {dy} {depth} {dom} {cod} morph =
  ?FSToBANatMorph_hole

--------------------------------------
---- Metalanguage interpretations ----
--------------------------------------

public export
InterpFSAlg : FSAlg (\_, _, _ => Type)
InterpFSAlg = MkFSAlg Void Unit (const $ const Either) (const $ const Pair)

public export
interpFinSubst : {0 c, d : Nat} -> FinSubstT c d -> Type
interpFinSubst = finSubstCata InterpFSAlg

public export
InterpTermAlg : FSTAlg (\_, _, x, _ => interpFinSubst x)
InterpTermAlg = MkFSTAlg () (\_ => Left) (\_ => Right) (\_, _ => MkPair)

public export
interpFinSubstTerm : {0 c, d : Nat} -> {x : FinSubstT c d} ->
  FinSubstTerm x -> interpFinSubst {c} {d} x
interpFinSubstTerm {x} = fstCata InterpTermAlg

public export
interpFinSubstMorph : {0 cx, dx, cy, dy, depth : Nat} ->
  {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
  FinSubstMorph {cx} {dx} {cy} {dy} depth x y ->
  interpFinSubst {c=cx} {d=dx} x ->
  interpFinSubst {c=cy} {d=dy} y
interpFinSubstMorph m = ?interpFinSubstMorph_hole
