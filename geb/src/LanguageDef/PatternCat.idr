module LanguageDef.PatternCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.PolyCat

%default total

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
