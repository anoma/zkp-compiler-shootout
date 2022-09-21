module LanguageDef.PatternCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.PolyCat

%default total

--------------------------------------
--------------------------------------
---- Objects and morphisms of Fin ----
--------------------------------------
--------------------------------------

-- Interpreted as the cardinality of a set.
public export
FSObj : Type
FSObj = Nat

public export
FSElem : FSObj -> Type
FSElem = Fin

-- Morphisms between finite sets.
public export
FSMorph : FSObj -> FSObj -> Type
FSMorph m n = Vect m (Fin n)

public export
FSId : (a : FSObj) -> FSMorph a a
FSId a = finFToVect id

public export
FSApply : {a, b : FSObj} -> FSMorph a b -> FSElem a -> FSElem b
FSApply = flip index

public export
FSCompose : {a, b, c : FSObj} -> FSMorph b c -> FSMorph a b -> FSMorph a c
FSCompose g f = finFToVect (FSApply g . FSApply f)

public export
FSInit : FSObj
FSInit = 0

public export
fsFromInit : (a : FSObj) -> FSMorph FSInit a
fsFromInit _ = []

public export
FSTerminal : FSObj
FSTerminal = 1

public export
FSToTerminal : (a : FSObj) -> FSMorph a FSTerminal
FSToTerminal a = finFToVect (const FZ)

public export
FSCoproduct : FSObj -> FSObj -> FSObj
FSCoproduct = (+)

public export
fsCopIntroLeft : (a, b : FSObj) -> FSMorph a (FSCoproduct a b)
fsCopIntroLeft a b = finFToVect (weakenN b)

public export
fsCopIntroRight : (a, b : FSObj) -> FSMorph b (FSCoproduct a b)
fsCopIntroRight a b = finFToVect (shift a)

public export
fsCopElim : {a, b, c : FSObj} ->
  FSMorph a c -> FSMorph b c -> FSMorph (FSCoproduct a b) c
fsCopElim f g = f ++ g

public export
FSProduct : FSObj -> FSObj -> FSObj
FSProduct = (*)

public export
fsProdIntro : {a, b, c : FSObj} ->
  FSMorph a b -> FSMorph a c -> FSMorph a (FSProduct b c)
fsProdIntro {a} {b} {c} f g =
  finFToVect $ \i =>
    natToFinLT
      {prf=(multAddLT (finToNatLT (FSApply f i)) (finToNatLT (FSApply g i)))}
      (c * finToNat (FSApply f i) + finToNat (FSApply g i))

public export
fsProdElimLeft : (a, b : FSObj) -> FSMorph (FSProduct a b) a
fsProdElimLeft a Z = rewrite multZeroRightZero a in []
fsProdElimLeft a (S b) =
  finFToVect $ \i =>
    natToFinLT
      {prf=(multDivLT (finToNatLT i) SIsNonZero)}
      (divNatNZ (finToNat i) (S b) SIsNonZero)

public export
fsProdElimRight : (a, b : FSObj) -> FSMorph (FSProduct a b) b
fsProdElimRight a Z = rewrite multZeroRightZero a in []
fsProdElimRight a (S b) =
  finFToVect $ \i =>
    natToFinLT
      {prf=(modLTDivisor (finToNat i) b)}
      (modNatNZ (finToNat i) (S b) SIsNonZero)

public export
FSExpObj : FSObj -> FSObj -> FSObj
FSExpObj = power

public export
FSHomObj : FSObj -> FSObj -> FSObj
FSHomObj = flip FSExpObj

public export
fsPowerElimRight : (a, b : FSObj) -> FSMorph (FSHomObj a (S b)) (S b)
fsPowerElimRight a b =
  finFToVect $ \i =>
    natToFinLT
      {prf=(modLTDivisor (finToNat i) b)}
      (modNatNZ (finToNat i) (S b) SIsNonZero)

public export
fsEval : (a, b : FSObj) -> FSMorph (FSProduct (FSHomObj a b) a) b
fsEval Z b = []
fsEval (S a) Z = []
fsEval (S a) (S b) =
  rewrite multRightSuccPlus (mult (S b) (power (S b) a)) a in
  rewrite sym (multAssociative (S b) (power (S b) a) a) in
  rewrite sym (multDistributesOverPlusRight
    (S b) (power (S b) a) (mult (power (S b) a) a)) in
  vectRepeat (S b) (fsPowerElimRight a b ++ fsEval a (S b))

public export
fsCurry : {a, b, c : FSObj} ->
  FSMorph (FSProduct a b) c -> FSMorph a (FSHomObj b c)
fsCurry {a} {b=Z} {c} f =
  rewrite sym (multOneRightNeutral a) in vectRepeat a [FZ]
fsCurry {a=Z} {b=(S b)} {c=Z} [] = []
fsCurry {a=(S a)} {b=(S b)} {c=Z} (x :: _) = absurd x
fsCurry {a} {b=(S b)} {c=(S Z)} f =
  finFToVect $ \i =>
    rewrite powerOneIsOne b in
    rewrite plusZeroRightNeutral 1 in
    FZ
fsCurry {a} {b=(S b)} {c=(S (S c))} f =
  let
    f' = replace {p=(flip Vect (Fin (S (S c))))} (multRightSuccPlus a b) f
    (fhd, ftl) = splitAt _ f'
    cftl = fsCurry {a} {b} {c=(S (S c))} ftl
  in
  finFToVect $ \i =>
    let
      fhdi = FSApply fhd i
      ftli = FSApply cftl i
    in
    finPlus (finPow _ b fhdi) (finMul _ c ftli)

public export
fsUncurry : {a, b, c : FSObj} ->
  FSMorph a (FSHomObj b c) -> FSMorph (FSProduct a b) c
fsUncurry {a} {b} {c} f =
  FSCompose
    (fsEval b c)
    (fsProdIntro (FSCompose f $ fsProdElimLeft _ _) (fsProdElimRight _ _))

public export
FSHomElem : FSObj -> FSObj -> Type
FSHomElem = FSElem .* FSHomObj

public export
FSHomElemToMorph : {x, y : FSObj} -> FSHomElem x y -> FSMorph x y
FSHomElemToMorph {x} {y} t =
  rewrite sym (plusZeroRightNeutral x) in
  fsUncurry {a=FSTerminal} {b=x} {c=y} [t]

public export
FSMorphToHomElem : {x, y : FSObj} -> FSMorph x y -> FSHomElem x y
FSMorphToHomElem {x} {y} t =
  let
    t' = rewrite plusZeroRightNeutral x in t
    ct = fsCurry {a=FSTerminal} {b=x} {c=y} t'
  in
  case ct of [t''] => t''

-----------------------------------
-----------------------------------
---- Dependent types in FinSet ----
-----------------------------------
-----------------------------------

public export
FSTypeFam : FSObj -> Type
FSTypeFam n = Vect n FSObj

public export
FSTypeFamObj : {n : FSObj} -> FSTypeFam n -> FSElem n -> FSObj
FSTypeFamObj fam i = index i fam

public export
FSTypeFamType : {n : FSObj} -> FSTypeFam n -> FSElem n -> Type
FSTypeFamType fam i = FSElem (FSTypeFamObj fam i)

public export
FSTypeFamTypes : {n : FSObj} -> FSTypeFam n -> Vect n Type
FSTypeFamTypes {n} = finFToVect . FSTypeFamType {n}

public export
FSDepSumType : {m, n : FSObj} ->
  FSMorph m n -> FSTypeFam m -> FSTypeFam n -> Type
FSDepSumType {m} {n} f fam fam' =
  (i : FSElem m ** j : FSTypeFamType fam i ** FSTypeFamType fam' (FSApply f i))

public export
FSIndexedMorph : {m, n : FSObj} ->
  FSMorph m n -> FSTypeFam m -> FSTypeFam n -> FSElem m -> Type
FSIndexedMorph f fam fam' i =
  FSMorph (FSTypeFamObj fam i) (FSTypeFamObj fam' $ FSApply f i)

public export
FSDepProductType : {m, n : FSObj} ->
  FSMorph m n -> FSTypeFam m -> FSTypeFam n -> Type
FSDepProductType {m} {n} f fam fam' =
  HVect {k=m} $ finFToVect $ FSIndexedMorph f fam fam'

---------------------------------
---------------------------------
---- Derived types in FinSet ----
---------------------------------
---------------------------------

------------------
---- Booleans ----
------------------

public export
FSBool : FSObj
FSBool = FSCoproduct FSTerminal FSTerminal

public export
FSFalse : FSElem FSBool
FSFalse = FZ

public export
FSTrue : FSElem FSBool
FSTrue = FS FZ

public export
fsToBool : FSElem FSBool -> Bool
fsToBool FZ = False
fsToBool (FS FZ) = True

public export
boolToFS : Bool -> FSElem FSBool
boolToFS False = FSFalse
boolToFS True = FSTrue

public export
FSPred : FSObj -> Type
FSPred a = FSMorph a FSBool

public export
FSPredObj : FSObj -> FSObj
FSPredObj a = FSHomObj a FSBool

public export
FSEqualizerPred : {a, b : FSObj} -> FSMorph a b -> FSMorph a b -> FSPred a
FSEqualizerPred {a} {b} f g =
  finFToVect $ \i => if FSApply f i == FSApply g i then FSTrue else FSFalse

------------------------
------------------------
---- Fin as a topos ----
------------------------
------------------------

public export
RefinedFSObj : Type
RefinedFSObj = DPair FSObj FSPred

public export
RFSElem : RefinedFSObj -> Type
RFSElem = FSElem . fst

public export
isRFSElem : (bv : RefinedFSObj) -> RFSElem bv -> Bool
isRFSElem (n ** pred) t = fsToBool (index t pred)

public export
RFSIsElem : (bv : RefinedFSObj) -> RFSElem bv -> Type
RFSIsElem bv i = IsTrue (isRFSElem bv i)

public export
RefinedFSObjFromFunc : {n : Nat} -> (Fin n -> Bool) -> RefinedFSObj
RefinedFSObjFromFunc {n} f = (n ** finFToVect $ boolToFS . f)

public export
RefinedFin : RefinedFSObj -> Type
RefinedFin bv = Subset0 (RFSElem bv) (RFSIsElem bv)

public export
MaybeRefinedFin : RefinedFSObj -> Bool -> Type
MaybeRefinedFin nv True = RefinedFin nv
MaybeRefinedFin nv False = Unit

public export
RefinedFinMorphElemType : (dom, cod : RefinedFSObj) -> RFSElem dom -> Type
RefinedFinMorphElemType mv nv i = MaybeRefinedFin nv (isRFSElem mv i)

public export
getRFElem : {dom, cod : RefinedFSObj} -> {i : RFSElem dom} ->
  RefinedFinMorphElemType dom cod i -> isRFSElem dom i = True -> RefinedFin cod
getRFElem {dom} {cod} {i} t eq with (isRFSElem dom i)
  getRFElem {dom} {cod} {i} t eq | True = t
  getRFElem {dom} {cod} {i} t Refl | False impossible

public export
RefinedFinMorphTypes : (dom, cod : RefinedFSObj) -> Vect (fst dom) Type
RefinedFinMorphTypes mv nv = finFToVect $ RefinedFinMorphElemType mv nv

public export
RefinedFinMorph : RefinedFSObj -> RefinedFSObj -> Type
RefinedFinMorph mv nv = HVect (RefinedFinMorphTypes mv nv)

public export
RFMIdElem : (bv : RefinedFSObj) -> (i : Fin (fst bv)) ->
  MaybeRefinedFin bv (isRFSElem bv i)
RFMIdElem bv i with (isRFSElem bv i) proof isElem
  RFMIdElem bv i | True = Element0 i isElem
  RFMIdElem bv i | False = ()

public export
RFMId : (bv : RefinedFSObj) -> RefinedFinMorph bv bv
RFMId bv = finHFToHVect (RFMIdElem bv)

public export
RFMApply : {dom, cod : RefinedFSObj} ->
  RefinedFinMorph dom cod -> RefinedFin dom -> RefinedFin cod
RFMApply {dom} {cod} m (Element0 i ok) with (isRFSElem dom i) proof prf
  RFMApply {dom} {cod} m (Element0 i Refl) | True =
    replace {p=(MaybeRefinedFin cod)} prf $ finFGet i m
  RFMApply {dom} {cod} m (Element0 i Refl) | False impossible

public export
RFMComposeElem : {a, b, c : RefinedFSObj} ->
  (g : RefinedFinMorph b c) -> (f : RefinedFinMorph a b) ->
  (i : RFSElem a) -> MaybeRefinedFin c (isRFSElem a i)
RFMComposeElem {a} {b} {c} g f i with (isRFSElem a i) proof isElem
  RFMComposeElem {a} {b} {c} g f i | True =
    RFMApply g $ getRFElem (finFGet i f) isElem
  RFMComposeElem {a} {b} {c} g f i | False = ()

public export
RFMCompose : {a, b, c : RefinedFSObj} ->
  RefinedFinMorph b c -> RefinedFinMorph a b -> RefinedFinMorph a c
RFMCompose g f = finHFToHVect (RFMComposeElem g f)

-------------------------------------------
-------------------------------------------
---- Polynomial endofunctors in FinSet ----
-------------------------------------------
-------------------------------------------

---------------------------------------------------
---- Polynomial endofunctors as dependent sets ----
---------------------------------------------------

-- We will use polynomial endofunctors of FinSet to define our first
-- recursive types.

public export
record FSPolyF where
  constructor FSPArena
  -- The length of the list is the number of positions (so the position set
  -- is the set of natural numbers less than the length of the list),
  -- and each element is the number of directions at the corresponding position
  -- (so the direction set is the set of natural numbers less than the element).
  fspArena : List FSObj

public export
fsPolyNPos : FSPolyF -> FSObj
fsPolyNPos = length . fspArena

public export
fsPolyPos : FSPolyF -> Type
fsPolyPos p = FSElem (fsPolyNPos p)

public export
fsPolyNDir : (p : FSPolyF) -> fsPolyPos p -> FSObj
fsPolyNDir (FSPArena a) i = index' a i

public export
fsPolyDir : (p : FSPolyF) -> fsPolyPos p -> Type
fsPolyDir p i = FSElem (fsPolyNDir p i)

public export
fspPF : FSPolyF -> PolyFunc
fspPF p = (fsPolyPos p ** fsPolyDir p)

public export
fsPolyProd : (p : FSPolyF) -> fsPolyPos p -> Type -> Type
fsPolyProd p i = Vect (fsPolyNDir p i)

public export
InterpFSPolyF : FSPolyF -> Type -> Type
InterpFSPolyF p x = (i : fsPolyPos p ** fsPolyProd p i x)

public export
InterpFSPolyFMap : (p : FSPolyF) -> {0 a, b : Type} ->
  (a -> b) -> InterpFSPolyF p a -> InterpFSPolyF p b
InterpFSPolyFMap p m (i ** d) = (i ** map m d)

public export
(p : FSPolyF) => Functor (InterpFSPolyF p) where
  map {p} = InterpFSPolyFMap p

----------------------------------------------
---- Polynomial functors as slice objects ----
----------------------------------------------

-- A polynomial endofunctor may also be viewed as a slice object
-- (in the slice category over its type of positions).
-- (Similarly, it may also be viewed as an object of the
-- arrow category.)

public export
FSSlice : FSObj -> Type
FSSlice = FSTypeFam

public export
FSSliceToType : {n : FSObj} -> FSSlice n -> SliceObj (FSElem n)
FSSliceToType = FSTypeFamType

public export
FSPolyFToSlice : (p : FSPolyF) -> FSSlice (fsPolyNPos p)
FSPolyFToSlice p = fromList (fspArena p)

public export
SliceToFSPolyF : {n : FSObj} -> FSSlice n -> FSPolyF
SliceToFSPolyF {n} sl = FSPArena (toList sl)

public export
FSSliceFiberMap : {n : FSObj} -> FSSlice n -> FSSlice n -> FSElem n -> Type
FSSliceFiberMap sl sl' i = FSMorph (index i sl) (index i sl')

public export
FSSliceMorphism : {n : FSObj} -> FSSlice n -> FSSlice n -> Type
FSSliceMorphism {n} sl sl' = HVect $ finFToVect (FSSliceFiberMap sl sl')

public export
FSSliceMorphToType : {n : FSObj} -> {sl, sl' : FSSlice n} ->
  FSSliceMorphism sl sl' -> SliceMorphism (FSSliceToType sl) (FSSliceToType sl')
FSSliceMorphToType {n} {sl} {sl'} m i d = Vect.index d $ finFGet i m

------------------------------------------------------------------
---- FinSet slices, and polynomial endofunctors, as morphisms ----
------------------------------------------------------------------

-- A slice object over `Fin n` in the category of finite prefixes of the natural
-- numbers may be viewed as a morphism in that category from `Fin n` to another
-- prefix of the natural numbers `Fin m` for some natural number `m` --
-- specifically, where `m` is the successor of the maximum cardinality of the
-- types in the type family which corresponds to the dependent-type view of the
-- slice object.  (The dependet-type view is that a slice object over `Fin n`
-- is a type family indexed by `Fin n`, where the dependent sum of the family is
-- the "total space" -- the domain of the morphism which defines the slice
-- object -- in the category-theoretic view.)  Note that the category-theoretic
-- definition of "slice object" uses a morphism _to_ `Fin n`, whereas this
-- type-theoretic view gives us an interpretation of that same slice object
-- as a morphism _from_ `Fin n`.

public export
FSSliceToMorph : {n : FSObj} -> (sl : FSSlice n) -> FSMorph n (S (vectMax sl))
FSSliceToMorph {n} sl = finFToVect $ vectMaxGet sl

public export
FSMorphToSlice : {m, n : FSObj} -> FSMorph m n -> FSSlice m
FSMorphToSlice {m} {n} v = map finToNat v

-- Because we may view a slice object in the category of finite prefixes of the
-- natural numbers as a morphism in that category, and we may view a
-- polynomial endofunctor on that category as a slice object over that
-- endofunctor's positions, we may view a polynomial endofunctor as a morphism.

public export
FSPolyDirMax : FSPolyF -> Nat
FSPolyDirMax p = vectMax (FSPolyFToSlice p)

public export
FSPolyToMorph : (p : FSPolyF) -> FSMorph (fsPolyNPos p) (S (FSPolyDirMax p))
FSPolyToMorph p = FSSliceToMorph (FSPolyFToSlice p)

public export
FSMorphToPoly : {m, n : FSObj} -> FSMorph m n -> FSPolyF
FSMorphToPoly v = SliceToFSPolyF (FSMorphToSlice v)

---------------------------------------------------------------------------
---- Natural transformations between polynomial endofunctors on FinSet ----
---------------------------------------------------------------------------

public export
FSPosMap : FSPolyF -> FSPolyF -> Type
FSPosMap p q = FSMorph (fsPolyNPos p) (fsPolyNPos q)

public export
FSPosDirMap : (p, q : FSPolyF) -> FSPosMap p q -> fsPolyPos p -> Type
FSPosDirMap p q onPos i =
  FSMorph (fsPolyNDir q $ FSApply onPos i) (fsPolyNDir p i)

public export
FSDirMap : (p, q : FSPolyF) -> FSPosMap p q -> Vect (fsPolyNPos p) Type
FSDirMap p q onPos = finFToVect $ FSPosDirMap p q onPos

public export
FSOnDirT : (p, q : FSPolyF) -> FSPosMap p q -> Type
FSOnDirT p q onPos = HVect $ FSDirMap p q onPos

public export
FSPNatTrans : FSPolyF -> FSPolyF -> Type
FSPNatTrans p q = (onPos : FSPosMap p q ** FSOnDirT p q onPos)

public export
fspOnPos : {0 p, q : FSPolyF} -> FSPNatTrans p q -> FSPosMap p q
fspOnPos = fst

public export
fspOnDir : {0 p, q : FSPolyF} -> (alpha : FSPNatTrans p q) ->
  FSOnDirT p q (fspOnPos {p} {q} alpha)
fspOnDir = snd

public export
fspOnPosF : {p, q : FSPolyF} -> FSPNatTrans p q -> fsPolyPos p -> fsPolyPos q
fspOnPosF (onPos ** onDir) = FSApply onPos

public export
fspOnDirF : {p, q : FSPolyF} -> (alpha : FSPNatTrans p q) ->
  (i : fsPolyPos p) -> fsPolyDir q (fspOnPosF {p} {q} alpha i) -> fsPolyDir p i
fspOnDirF (onPos ** onDir) i = FSApply $ finFGet i onDir

public export
fspNT : {p, q : FSPolyF} -> FSPNatTrans p q -> PolyNatTrans (fspPF p) (fspPF q)
fspNT alpha = (fspOnPosF alpha ** fspOnDirF alpha)
