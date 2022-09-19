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
      {prf=(?fsProdIntro_prf_hole)}
      (c * finToNat (FSApply f i) + finToNat (FSApply g i))

public export
fsProdElimLeft : (a, b : FSObj) -> FSMorph (FSProduct a b) a
fsProdElimLeft a Z = rewrite multZeroRightZero a in []
fsProdElimLeft a (S b) =
  finFToVect $ \i =>
    natToFinLT
      {prf=(?fsProdElimLeft_prf_hole)}
      (divNatNZ (finToNat i) (S b) SIsNonZero)

public export
fsProdElimRight : (a, b : FSObj) -> FSMorph (FSProduct a b) b
fsProdElimRight a Z = rewrite multZeroRightZero a in []
fsProdElimRight a (S b) =
  finFToVect $ \i =>
    natToFinLT
      {prf=(?fsProdElimRight_prf_hole)}
      (modNatNZ (finToNat i) (S b) SIsNonZero)

public export
FSExpObj : FSObj -> FSObj -> FSObj
FSExpObj = power

public export
FSHomObj : FSObj -> FSObj -> FSObj
FSHomObj = flip FSExpObj

public export
vectRepeat : (a, b, c : FSObj) -> Vect b (Fin c) -> Vect (mult a b) (Fin c)
vectRepeat a b c v = ?fsEvalRepeat_hole

public export
fsPowerElimRight : (a, b : FSObj) -> FSMorph (FSHomObj a (S b)) (S b)
fsPowerElimRight a b =
  finFToVect $ \i =>
    natToFinLT
      {prf=(?fsPowerElimRight_prf_hole)}
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
  vectRepeat (S b) _ _ (fsPowerElimRight a b ++ fsEval a (S b))

public export
fsCurry : {a, b, c : FSObj} ->
  FSMorph (FSProduct a b) c -> FSMorph a (FSHomObj b c)
fsCurry {a} {b} {c} f = ?fsCurry_hole

public export
fsUncurry : {a, b, c : FSObj} ->
  FSMorph a (FSHomObj b c) -> FSMorph (FSProduct a b) c
fsUncurry {a} {b} {c} f = ?fsUncurry_hole

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
RefinedFSObj = List Bool

public export
RFSElem : RefinedFSObj -> Type
RFSElem = Fin . length

public export
isRFSElem : (bv : RefinedFSObj) -> RFSElem bv -> Bool
isRFSElem = index'

public export
RFSIsElem : (bv : RefinedFSObj) -> RFSElem bv -> Type
RFSIsElem bv i = IsTrue (isRFSElem bv i)

public export
RefinedFSObjFromFunc : {n : Nat} -> (Fin n -> Bool) -> RefinedFSObj
RefinedFSObjFromFunc = toList . finFToVect

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
RefinedFinMorphTypes : (dom, cod : RefinedFSObj) -> Vect (length dom) Type
RefinedFinMorphTypes mv nv = finFToVect $ RefinedFinMorphElemType mv nv

public export
RefinedFinMorph : RefinedFSObj -> RefinedFSObj -> Type
RefinedFinMorph mv nv = HVect (RefinedFinMorphTypes mv nv)

public export
RFMIdElem : (bv : RefinedFSObj) -> (i : Fin (length bv)) ->
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
  fspArena : List Nat

public export
fsPolyNPos : FSPolyF -> Nat
fsPolyNPos = length . fspArena

public export
fsPolyPos : FSPolyF -> Type
fsPolyPos p = Fin (fsPolyNPos p)

public export
fsPolyNDir : (p : FSPolyF) -> fsPolyPos p -> Nat
fsPolyNDir (FSPArena a) i = index' a i

public export
fsPolyDir : (p : FSPolyF) -> fsPolyPos p -> Type
fsPolyDir p i = Fin (fsPolyNDir p i)

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
-- (in the slice category of its type of positions).
-- (Similarly, it may also be viewed as an object of the
-- arrow category.)

public export
FSSlice : Nat -> Type
FSSlice n = Vect n Nat

public export
FSSliceToType : {n : Nat} -> FSSlice n -> SliceObj (Fin n)
FSSliceToType {n} sl i = Fin (index i sl)

public export
FSPolyFToSlice : (p : FSPolyF) -> FSSlice (fsPolyNPos p)
FSPolyFToSlice p = fromList (fspArena p)

public export
SliceToFSPolyF : {n : Nat} -> FSSlice n -> FSPolyF
SliceToFSPolyF {n} sl = FSPArena (toList sl)

public export
FSSliceFiberMap : {n : Nat} -> FSSlice n -> FSSlice n -> Fin n -> Type
FSSliceFiberMap sl sl' i = Vect (index i sl) (Fin (index i sl'))

public export
FSSliceMorphism : {n : Nat} -> FSSlice n -> FSSlice n -> Type
FSSliceMorphism {n} sl sl' = HVect $ finFToVect (FSSliceFiberMap sl sl')

public export
FSSliceMorphToType : {n : Nat} -> {sl, sl' : FSSlice n} ->
  FSSliceMorphism sl sl' -> SliceMorphism (FSSliceToType sl) (FSSliceToType sl')
FSSliceMorphToType {n} {sl} {sl'} m i d = Vect.index d $ finFGet i m

---------------------------------------------------------------------------
---- Natural transformations between polynomial endofunctors on FinSet ----
---------------------------------------------------------------------------

public export
FSPNatTrans : FSPolyF -> FSPolyF -> Type
FSPNatTrans p q =
  (onPos : fsPolyPos p -> fsPolyPos q **
   SliceMorphism (fsPolyDir q . onPos) (fsPolyDir p))

public export
fspOnPos : {0 p, q : FSPolyF} -> FSPNatTrans p q -> fsPolyPos p -> fsPolyPos q
fspOnPos = fst

public export
fspOnDir : {0 p, q : FSPolyF} -> (alpha : FSPNatTrans p q) ->
  (i : fsPolyPos p) -> fsPolyDir q (fspOnPos {p} {q} alpha i) -> fsPolyDir p i
fspOnDir = snd
