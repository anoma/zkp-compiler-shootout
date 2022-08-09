module Library.IdrisCategories

import Library.IdrisUtils

%default total

-------------------------------
-------------------------------
---- Equivalence relations ----
-------------------------------
-------------------------------

public export
RelationOn : Type -> Type
RelationOn a = a -> a -> Type

public export
IsReflexive : {a : Type} -> RelationOn a -> Type
IsReflexive {a} r = (x : a) -> r x x

public export
IsSymmetric : {a : Type} -> RelationOn a -> Type
IsSymmetric {a} r = {x, y : a} -> r x y -> r y x

public export
IsTransitive : {a : Type} -> RelationOn a -> Type
IsTransitive {a} r = {x, y, z : a} -> r x y -> r y z -> r x z

public export
record IsEquivalence {a : Type} (r : RelationOn a) where
  constructor MkEquivalence
  EquivRefl : IsReflexive r
  EquivSym : IsSymmetric r
  EquivTrans : IsTransitive r

public export
IsDecidable : {a : Type} -> (r : RelationOn a) -> Type
IsDecidable {a} r = (x, y : a) -> Dec (r x y)

public export
record IsDecEquiv {a : Type} (r : RelationOn a) where
  constructor MkDecEquiv
  DecEquivEquiv : IsEquivalence r
  DecEquivDec : IsDecidable r

public export
InverseUpTo : {a, b : Type} -> RelationOn a -> (a -> b) -> (b -> a) -> Type
InverseUpTo r f g = (x : a) -> r (g (f x)) x

-----------------------------------
-----------------------------------
---- Functional extensionality ----
-----------------------------------
-----------------------------------

-- When interpreting category theory into Idris's type system, we could
-- axiomatize functional extensionality, but instead we'll quotient over
-- it explicitly.  This is because we will quotient over a weaker notion
-- than that of functional extensionality:  decidable first-order
-- extensional equality.

public export
ExtEq : {a, b : Type} -> (a -> b) -> (a -> b) -> Type
ExtEq {a} f g = (el : a) -> f el = g el

public export
ExtEqRefl : {a, b : Type} -> (f : a -> b) -> ExtEq f f
ExtEqRefl _ _ = Refl

public export
ExtEqSym : {a, b : Type} -> {f, g : a -> b} -> ExtEq f g -> ExtEq g f
ExtEqSym eq x = sym (eq x)

public export
ExtEqTrans : {a, b : Type} ->
  {f, g, h: a -> b} -> ExtEq f g -> ExtEq g h -> ExtEq f h
ExtEqTrans eq eq' x = trans (eq x) (eq' x)

public export
ExtEqEquiv : {a, b : Type} -> IsEquivalence {a=(a -> b)} (ExtEq {a} {b})
ExtEqEquiv = MkEquivalence ExtEqRefl ExtEqSym ExtEqTrans

public export
EqFunctionExt : {a, b : Type} -> {f, g: a -> b} -> f = g -> ExtEq f g
EqFunctionExt Refl _ = Refl

public export
ExtInverse : {a, b : Type} -> (a -> b) -> (b -> a) -> Type
ExtInverse f g = (ExtEq (f . g) id, ExtEq (g . f) id)

public export
ExtInversePair : {a, b : Type} -> (a -> b, b -> a) -> Type
ExtInversePair (f, g) = ExtInverse f g

--------------------------------------
--------------------------------------
---- Categorial algebra on `Type` ----
--------------------------------------
--------------------------------------

-- The categorial definition of an F-algebra.
public export
Algebra : (Type -> Type) -> Type -> Type
Algebra f a = f a -> a

-- The dual of an F-algebra: an F-coalgebra.
public export
Coalgebra : (Type -> Type) -> Type -> Type
Coalgebra f a = a -> f a

-- For a given functor `F` and object `v`, form the functor `Fv` defined by
-- `Fv[x] = v + F[x]`.  We call it `TermFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing open terms of
-- that datatype with variables drawn from type `v`.
public export
data TermFunctor : (Type -> Type) -> Type -> (Type -> Type) where
  TermVar : {f : Type -> Type} -> {0 v, a : Type} ->
    v -> TermFunctor f v a
  TermComposite : {f : Type -> Type} -> {0 v, a : Type} ->
    f a -> TermFunctor f v a

public export
Functor f => Bifunctor (TermFunctor f) where
  bimap f' g' (TermVar x) = TermVar $ f' x
  bimap f' g' (TermComposite x) = TermComposite $ map g' x

public export
LimitIterF : (Type -> Type) -> (Type -> Type)
LimitIterF f a = TermFunctor f a a

-- For a given functor `F`, form the functor `Fa` defined by
-- `Fa[x] = a * F[x]`.  We call it `TreeFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing potentially infinite
-- trees of that datatype with labels drawn from type `v`.
-- This is the dual of `TermFunctor`.
public export
data TreeFunctor : (Type -> Type) -> Type -> (Type -> Type) where
  TreeNode : {f : Type -> Type} -> {0 l, a : Type} ->
    l -> f a -> TreeFunctor f l a

export
Functor f => Bifunctor (TreeFunctor f) where
  bimap f' g' (TreeNode x fx) = TreeNode (f' x) (map g' fx)

public export
ColimitIterF : (Type -> Type) -> (Type -> Type)
ColimitIterF f a = TreeFunctor f a a

export
treeLabel : {f : Type -> Type} -> {l, a : Type} -> TreeFunctor f l a -> l
treeLabel (TreeNode a' _) = a'

export
treeSubtree : {f : Type -> Type} -> {l, a : Type} -> TreeFunctor f l a -> f a
treeSubtree (TreeNode _ fx) = fx

-- An algebra on a functor representing a type of open terms (as generated
-- by `TermFunctor` above) may be viewed as a polymorphic algebra, because
-- for each object `v` it generates an `F[v]`-algebra on an any given carrier
-- object.  When `v` is the initial object (`Void`), it specializes to
-- generating `F`-algebras.
public export
TermAlgebra : (Type -> Type) -> Type -> Type -> Type
TermAlgebra f v a = Algebra (TermFunctor f v) a

public export
voidAlg : {f : Type -> Type} -> {a : Type} ->
  Algebra f a -> TermAlgebra f Void a
voidAlg alg (TermVar {v=Void} _) impossible
voidAlg alg (TermComposite x) = alg x

public export
TermCoalgebra : (Type -> Type) -> Type -> Type -> Type
TermCoalgebra f v a = Coalgebra (TermFunctor f v) a

-- A coalgebra on a functor representing a type of labeled trees (as generated
-- by `TreeFunctor` above) may be viewed as a polymorphic coalgebra, because
-- for each object `v` it generates an `F[v]`-coalgebra on an any given carrier
-- object.  When `v` is the terminal object (`Unit`), it specializes to
-- generating `F`-coalgebras.
public export
TreeCoalgebra : (Type -> Type) -> Type -> Type -> Type
TreeCoalgebra f v a = Coalgebra (TreeFunctor f v) a

public export
unitCoalg : {f : Type -> Type} -> {a : Type} ->
  Coalgebra f a -> TreeCoalgebra f Unit a
unitCoalg alg x = TreeNode {l=()} () $ alg x

public export
TreeAlgebra : (Type -> Type) -> Type -> Type -> Type
TreeAlgebra f v a = Algebra (TreeFunctor f v) a

--------------------------------------------------
---- Initial algebras and terminal coalgebras ----
--------------------------------------------------

-- If `F` has an initial algebra, then for every object `a`, the functor
-- `Fa` defined above also has an initial algebra, which is isomorphic
-- to `FreeMonad[F, a]`.  Thus `FreeMonad` allows us to create initial
-- `Fa`-algebras parameterized over arbitrary objects `a`, with the initial
-- algebra of `F` itself being the special case where `a` is the initial object
-- (`Void`).  `FreeMonad` is sometimes written `F*`.
--
-- Note that `FreeMonad` itself is a composition, but one which leaves
-- the category in which the endofunctors live before returning:  it is
-- the monad induced by the free-forgetful adjunction between the category
-- of endofunctors and the category of their F-algebras.  (The comonad
-- induced by the dual forgetful-cofree adjunction is `CofreeComonad`.)
public export
data FreeMonad : (Type -> Type) -> (Type -> Type) where
  InFree : {f : Type -> Type} -> {0 a : Type} ->
    TermAlgebra f a (FreeMonad f a)

public export
FreeAlgebra : (Type -> Type) -> Type -> Type
FreeAlgebra f a = Algebra f (FreeMonad f a)

public export
BigStepAlgebra : (Type -> Type) -> Type -> Type
BigStepAlgebra f a = Algebra (FreeMonad f) a

public export
InitialAlgebra : (Type -> Type) -> Type
InitialAlgebra f = FreeAlgebra f Void

-- If `F` has a terminal coalgebra, then for every object `a`, the functor
-- `Fa` defined above also has a terminal coalgebra, which is isomorphic
-- to `CofreeComonad[F, a]`.  Thus `CofreeComonad` allows us to create terminal
-- `Fa`-coalgebras parameterized over arbitrary objects `a`, with the terminal
-- coalgebra of `F` itself being the special case where `a` is the terminal
-- object (`Unit`).  `CofreeComonad` is sometimes written `Finf`.
public export
data CofreeComonad : (Type -> Type) -> (Type -> Type) where
  InCofree :
    {f : Type -> Type} -> {a : Type} ->
    Inf (TreeFunctor f a (CofreeComonad f a)) -> CofreeComonad f a

public export
CofreeCoalgebra : (Type -> Type) -> Type -> Type
CofreeCoalgebra f a = Coalgebra f (CofreeComonad f a)

public export
BigStepCoalgebra : (Type -> Type) -> Type -> Type
BigStepCoalgebra f a = Coalgebra (CofreeComonad f) a

public export
CofreeCoalgMap : (f : Type -> Type) -> Type
CofreeCoalgMap f =
  (a, b : Type) -> (a -> b) -> CofreeCoalgebra f a -> CofreeCoalgebra f b

public export
CofreeCoalgSubtrees : (f : Type -> Type) -> Type
CofreeCoalgSubtrees f =
  (a, b : Type) -> (a -> b) -> CofreeCoalgebra f a -> Coalgebra f b

public export
TerminalCoalgebra : (Type -> Type) -> Type
TerminalCoalgebra f = CofreeCoalgebra f Unit

public export
inFreeVar : {f : Type -> Type} -> Coalgebra (FreeMonad f) a
inFreeVar = InFree . TermVar

public export
inFreeComposite : {f : Type -> Type} -> Algebra f (FreeMonad f a)
inFreeComposite = InFree . TermComposite

public export
outFree : TermCoalgebra f a (FreeMonad f a)
outFree (InFree x) = x

public export
inCofreeTree : {a : Type} -> {f : Type -> Type} ->
  a -> Algebra f (CofreeComonad f a)
inCofreeTree x fx = InCofree $ TreeNode x fx

public export
outCofree : {f : Type -> Type} -> {a : Type} ->
  TreeCoalgebra f a (CofreeComonad f a)
outCofree (InCofree x) = x

-- Special case of `FreeMonad` where `v` is `Void`.
-- This is the fixpoint of an endofunctor (if it exists).
public export
Mu : (Type -> Type) -> Type
Mu f = FreeMonad f Void

-- Special case of `CofreeComonad` where `v` is `Unit`.
-- This is the cofixpoint of an endofunctor (if it exists).
public export
Nu : (Type -> Type) -> Type
Nu f = CofreeComonad f ()

-- Parameterized special induction.
public export
ParamCata : (Type -> Type) -> Type
ParamCata f =
  (v, a : Type) -> (v -> a) -> Algebra f a -> FreeMonad f v -> a

-- Special induction.
public export
Catamorphism : (Type -> Type) -> Type
Catamorphism f = (a : Type) -> Algebra f a -> FreeMonad f Void -> a

public export
cataFromParam : {f : Type -> Type} -> ParamCata f -> Catamorphism f
cataFromParam pcata a = pcata Void a (voidF a)

public export
ParamBigStepCata : (Type -> Type) -> Type
ParamBigStepCata f =
  (v, a : Type) -> (v -> a) -> BigStepAlgebra f a -> FreeMonad f v -> a

public export
BigStepCata : (Type -> Type) -> Type
BigStepCata f =
  (a : Type) -> BigStepAlgebra f a -> FreeMonad f Void -> a

public export
ParamAna : (Type -> Type) -> Type
ParamAna f =
  (l, a : Type) -> (a -> l) -> Coalgebra f a -> a -> CofreeComonad f l

public export
Anamorphism : (Type -> Type) -> Type
Anamorphism f = (a : Type) -> Coalgebra f a -> a -> CofreeComonad f Unit

public export
anaFromParam : {f : Type -> Type} -> ParamAna f -> Anamorphism f
anaFromParam pana a = pana Unit a (const ())

public export
ParamBigStepAna : (Type -> Type) -> Type
ParamBigStepAna f =
  (l, a : Type) -> (a -> l) -> BigStepCoalgebra f a -> a -> CofreeComonad f l

public export
BigStepAna : (Type -> Type) -> Type
BigStepAna f =
  (a : Type) -> BigStepCoalgebra f a -> a -> CofreeComonad f Unit

--------------------
--------------------
---- Bifunctors ----
--------------------
--------------------

-- A bifunctor applied to a type is a functor.  This is simply the
-- currying adjunction in the category of functors -- the functor
-- categories `[C, [D, E]]` and `[C × D, E]` are equivalent.
public export
Bifunctor f => Functor (f a) where
  map = mapSnd

-- A bifunctor with its arguments flipped is a bifunctor.  This
-- reflects the symmetry of the product.
public export
Bifunctor f => Bifunctor (flip f) where
  bimap f g = bimap g f

--------------------------------------------------------------
--------------------------------------------------------------
---- Idris categories: `[Type]`, product, and endofunctor ----
--------------------------------------------------------------
--------------------------------------------------------------

---------------------------------------------------------------
---- Objects/morphisms in `[Type]` (Idris's base category) ----
---------------------------------------------------------------

public export
ObjectT : Type
ObjectT = Type

public export
MorphismT : ObjectT -> ObjectT -> Type
MorphismT a b = a -> b

----------------------------------------------------------------------------
---- Objects/morphisms in `[Type x Type]` (the base's product category) ----
----------------------------------------------------------------------------

public export
ObjectP : Type
ObjectP = (Type, Type)

public export
MorphismP : ObjectP -> ObjectP -> Type
MorphismP (a, b) (c, d) = (MorphismT a c, MorphismT b d)

-------------------------------------------------------------------------------
---- Objects/morphisms in `[Type, Type]` (the base's endofunctor category) ----
-------------------------------------------------------------------------------

public export
ObjectF : Type
ObjectF = Type -> Type

-- Morphisms in the endofunctor category are natural transformations in
-- the base category.
public export
MorphismF : ObjectF -> ObjectF -> Type
MorphismF f g = (a : Type) -> MorphismT (f a) (g a)

------------------------------------------
---- Identity/composition in `[Type]` ----
------------------------------------------

public export
IdT : (a : ObjectT) -> MorphismT a a
IdT a = Prelude.Basics.id {a}

public export
ComposeT : {a, b, c : ObjectT} ->
  MorphismT b c -> MorphismT a b -> MorphismT a c
ComposeT = (.)

-------------------------------------------------
---- Identity/composition in `[Type x Type]` ----
-------------------------------------------------

public export
IdP : (a : ObjectP) -> MorphismP a a
IdP (a, b) = (IdT a, IdT b)

public export
ComposeP : {a, b, c : ObjectP} ->
  MorphismP b c -> MorphismP a b -> MorphismP a c
ComposeP {a=(a, a')} {b=(b, b')} {c=(c, c')} (g, g') (f, f') =
  (ComposeT {a} {b} {c} g f, ComposeT {a=a'} {b=b'} {c=c'} g' f')

------------------------------------------------
---- Identity/composition in `[Type, Type]` ----
------------------------------------------------

-- The identity in the functor category `[Type, Type]`.
public export
IdF : (f : ObjectF) -> MorphismF f f
IdF f a = Prelude.Basics.id {a=(f a)}

-- Composition in the functor category `[Type, Type]`.
-- This is vertical composition of natural transformations.
public export
ComposeF : {f, g, h : ObjectF} ->
  MorphismF g h -> MorphismF f g -> MorphismF f h
ComposeF beta alpha a = ComposeT (beta a) (alpha a)

-- The functor category also has composition of _objects_.
public export
ComposeFObj : ObjectF -> ObjectF -> ObjectF
ComposeFObj = (.)

-- The functor category also has horizonal composition.
public export
ComposeFH : {f, g, h, j : ObjectF} -> Functor g =>
  MorphismF g j -> MorphismF f h -> MorphismF (ComposeT g f) (ComposeT j h)
ComposeFH {g} beta alpha a = (beta (h a) . map {f=g} (alpha a))

----------------------------------------------------
----------------------------------------------------
---- Natural transformations and their algebras ----
----------------------------------------------------
----------------------------------------------------

public export
NaturalTransformation : (Type -> Type) -> (Type -> Type) -> Type
NaturalTransformation f g = (x : Type) -> f x -> g x

public export
AdjUnit : (Type -> Type) -> Type
AdjUnit f = NaturalTransformation id f

public export
AdjCounit : (Type -> Type) -> Type
AdjCounit f = NaturalTransformation f id

public export
FreeNaturalTransformation :
  (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Type
FreeNaturalTransformation m f g =
  (x : Type) -> f (FreeMonad m x) -> g (FreeMonad m x)

public export
CofreeNaturalTransformation :
  (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Type
CofreeNaturalTransformation m f g =
  (x : Type) -> f (CofreeComonad m x) -> g (CofreeComonad m x)

public export
FreeMonadNatTrans : (Type -> Type) -> (Type -> Type) -> Type
FreeMonadNatTrans f g =
  NaturalTransformation (FreeMonad f) (FreeMonad g)

public export
CofreeComonadNatTrans : (Type -> Type) -> (Type -> Type) -> Type
CofreeComonadNatTrans f g =
  NaturalTransformation (CofreeComonad f) (CofreeComonad g)

public export
FreeAdjUnit : (f, g : Type -> Type) -> Type
FreeAdjUnit m f = FreeNaturalTransformation m id f

public export
FreeAdjCounit : (f, g : Type -> Type) -> Type
FreeAdjCounit m f = FreeNaturalTransformation m f id

public export
CofreeAdjUnit : (f, g : Type -> Type) -> Type
CofreeAdjUnit m f = CofreeNaturalTransformation m id f

public export
CofreeAdjCounit : (f, g : Type -> Type) -> Type
CofreeAdjCounit m f = CofreeNaturalTransformation m f id

public export
natTransFreeAlg : {f, g : Type -> Type} ->
  NaturalTransformation f g -> FreeAdjCounit g f
natTransFreeAlg {f} {g} nt a = InFree . TermComposite . nt (FreeMonad g a)

public export
natTransMapFree :
  {f, g : Type -> Type} ->
  ParamCata f ->
  NaturalTransformation f g ->
  FreeMonadNatTrans f g
natTransMapFree {f} {g} cataF nt carrier =
  cataF carrier
    (FreeMonad g carrier) (InFree . TermVar) (natTransFreeAlg nt carrier)

---------------------------------------
---- Polynomial functors on `Type` ----
---------------------------------------

-------------------
---- Constants ----
-------------------

-- Given an object `a`, `Const a` is an endofunctor which takes all objects
-- to `a`.
public export
ConstF : Type -> Type -> Type
ConstF a _ = a

public export
Functor (ConstF a) where
  map = const id

--------------------------------------
---- Terminal and initial objects ----
--------------------------------------

public export
TerminalMonad : Type -> Type
TerminalMonad = ConstF Unit

public export
Functor TerminalMonad where
  map _ () = ()

public export
TerminalNTUnit : (a : Type) -> a -> TerminalMonad a
TerminalNTUnit _ = const ()

public export
TerminalNaturality : {a, b : Type} -> (m : a -> b) ->
  map {f=TerminalMonad} m . TerminalNTUnit a = TerminalNTUnit b . m
TerminalNaturality _ = Refl

public export
InitialComonad : Type -> Type
InitialComonad = ConstF Void

public export
Functor InitialComonad where
  map _ v = v

public export
InitialNTCounit : (0 a : Type) -> InitialComonad a -> a
InitialNTCounit = voidF

public export
InitialNaturality : {a, b : Type} -> (m : a -> b) ->
  ExtEq (InitialNTCounit b . map {f=InitialComonad} m) (m . InitialNTCounit a)
InitialNaturality _ v = void v

------------------
---- Products ----
------------------

-- `ProductF` is an operator on endofunctors which takes two endofunctors
-- to their product.  `ProductF` is therefore not itself an endofunctor; it
-- is a higher-order functor.  (If `Poly[C]` is the category of polynomial
-- endofunctors on some category `C` -- if all of `C`'s endofunctors are
-- polynomial, then `Poly[C]` is `[C,C]` -- then `ProductF` is an object of
-- [Poly[C] x Poly[C], Poly[C].  That is, it is a bifunctor on `Poly[C]`.)
public export
ProductF : (Type -> Type) -> (Type -> Type) -> Type -> Type
ProductF f g a = (f a, g a)

public export
(Functor f, Functor g) => Functor (ProductF f g) where
  map m (x, y) = (map m x, map m y)

public export
ProductMonad : Type -> Type
ProductMonad a = Pair a a

public export
Functor ProductMonad where
  map = mapHom

public export
ProductNTUnit : {a : Type} -> a -> ProductMonad a
ProductNTUnit x = (x, x)

-- The right adjoint to the diagonal functor from the Idris type system
-- (`Type`).
public export
ProductAdjunct : (Type, Type) -> Type
ProductAdjunct (t, t') = Pair t t'

-- The right adjoint to the diagonal functor from the category of Idris
-- functors (`Type -> Type`).
public export
ProductAdjunctFCat : ((Type -> Type), (Type -> Type)) -> Type -> Type
ProductAdjunctFCat p = ProductF (fst p) (snd p)

public export
ProductFAlg : (Type -> Type) -> (Type -> Type) -> Type -> Type
ProductFAlg f g a = f a -> Algebra g a

public export
ProductFAlgToAlg : {f, g : Type -> Type} -> {a : Type} ->
  ProductFAlg f g a -> Algebra (ProductF f g) a
ProductFAlgToAlg {f} {g} {a} alg (fx, gx) = alg fx gx

--------------------
---- Coproducts ----
--------------------

-- `CoproductF` is in `[PolyC x PolyC, PolyC]`, and takes two
-- endofunctors to their coproduct.
public export
CoproductF : (Type -> Type) -> (Type -> Type) -> Type -> Type
CoproductF f g a = Either (f a) (g a)

public export
CoproductFComonad : (Type -> Type) -> Type -> Type
CoproductFComonad f = CoproductF f f

public export
(Functor f, Functor g) => Functor (CoproductF f g) where
  map m (Left x) = Left $ map m x
  map m (Right y) = Right $ map m y

public export
CoproductComonad : Type -> Type
CoproductComonad a = Either a a

public export
CoproductNTCounit : {a : Type} -> CoproductComonad a -> a
CoproductNTCounit (Left x) = x
CoproductNTCounit (Right x) = x

-- The left adjoint to the diagonal functor, in the Idris type system.
public export
CoproductAdjunct : (Type, Type) -> Type
CoproductAdjunct (t, t') = Either t t'

-- The left adjoint to the diagonal functor from the category of Idris
-- functors (`Type -> Type`).
public export
CoproductAdjunctFCat : ((Type -> Type), (Type -> Type)) -> Type -> Type
CoproductAdjunctFCat p = CoproductF (fst p) (snd p)

public export
CoproductFAlg : (Type -> Type) -> (Type -> Type) -> Type -> Type
CoproductFAlg f g a = (f a -> a, g a -> a)

public export
CoproductFAlgToAlg : {f, g : Type -> Type} -> {a : Type} ->
  CoproductFAlg f g a -> Algebra (CoproductF f g) a
CoproductFAlgToAlg (algf, algg) (Left fx) = algf fx
CoproductFAlgToAlg (algf, algg) (Right gx) = algg gx

public export
CoproductToCoproductFAlg :
  (Type -> Type) -> (Type -> Type) ->
  (Type -> Type) -> (Type -> Type) ->
  Type -> Type
-- An algebra for computing a morphism `(f + g) a -> (f' + g') a`.
CoproductToCoproductFAlg f g f' g' a =
  (f a -> CoproductF f' g' a, g a -> CoproductF f' g' a)

---------------------------------------
---- Higher-order utility functors ----
---------------------------------------

public export
IdTF : Type -> Type
IdTF = Prelude.Basics.id {a=Type}

public export
Functor IdTF where
  map = id

public export
PairWithF : Type -> Type -> Type
PairWithF a = ProductF (ConstF a) IdTF

public export
ChoiceBetweenF : Type -> Type -> Type
ChoiceBetweenF a = CoproductF (ConstF a) IdTF

public export
MaybeF : Type -> Type
MaybeF = ChoiceBetweenF ()

public export
CoproductFLNE : (Type -> Type) -> List (Type -> Type) -> Type -> Type
CoproductFLNE f [] = f
CoproductFLNE f (f' :: fs) = CoproductF f (CoproductFLNE f' fs)

public export
CoproductFL : List (Type -> Type) -> Type -> Type
CoproductFL [] = InitialComonad
CoproductFL (f :: fs) = CoproductFLNE f fs

--------------------------------------------------------------
---- Slice categories and more on natural transformations ----
--------------------------------------------------------------

public export
SliceO : Type -> Type
SliceO x = (a : Type ** a -> x)

public export
SliceF : (Type -> Type) -> Type -> Type
SliceF f = SliceO . f

public export
NMSliceCar : Type -> Type
NMSliceCar = SliceF ProductMonad

public export
SliceNT : (Type -> Type) -> (Type -> Type) -> Type
SliceNT f g = NaturalTransformation (SliceF f) (SliceF g)

public export
SliceNTToPreComp : (Type -> Type) -> (Type -> Type) -> Type
SliceNTToPreComp f g = SliceNT f (f . g)

public export
FPred : (Type -> Type) -> Type -> Type
FPred f ty = f ty -> Type

public export
FNatTrans : (Type -> Type) -> (Type -> Type) -> Type
FNatTrans f g = NaturalTransformation (FPred f) (FPred g)

public export
FNatTransDep : (Type -> Type) -> (Type -> Type) -> Type
FNatTransDep f g = FNatTrans f (f . g)

public export
MorphCarrier : Type -> Type
MorphCarrier = FPred ProductMonad

public export
MorphFunctor : (Type -> Type) -> Type
MorphFunctor = FNatTransDep ProductMonad

----------------------------------------
----------------------------------------
---- Representables and polynomials ----
----------------------------------------
----------------------------------------

public export
ProductN : Nat -> Type -> Type
ProductN 0 _ = ()
ProductN (S n) a = (a, ProductN n a)

public export
mapProductN : (n : Nat) -> {0 a, b : Type} ->
  (f : a -> b) -> ProductN n a -> ProductN n b
mapProductN Z f () = ()
mapProductN (S n) f (x, p) = (f x, mapProductN n f p)

public export
(n : Nat) => Functor (ProductN n) where
  map {n} = mapProductN n

public export
CovarHomFunc : Type -> (Type -> Type)
CovarHomFunc a = \ty => a -> ty

public export
FinCovarHomFunc : Nat -> (Type -> Type)
FinCovarHomFunc = ProductN

public export
CovarHomAlg : Type -> Type -> Type
CovarHomAlg a b = (a -> b) -> b

public export
FinCovarHomAlg : Nat -> Type -> Type
FinCovarHomAlg Z b = b
FinCovarHomAlg (S n) b = b -> FinCovarHomAlg n b

CovarHomAlgCorrect : (a, b : Type) ->
  CovarHomAlg a b = Algebra (CovarHomFunc a) b
CovarHomAlgCorrect a b = Refl

public export
CovarHomCoalg : Type -> Type -> Type
CovarHomCoalg a b = b -> (a -> b)

public export
FinCovarHomCoalg : Nat -> Type -> Type
FinCovarHomCoalg n b = ProductN n (b -> b)

CovarHomCoalgCorrect : (a, b : Type) ->
  CovarHomCoalg a b = Coalgebra (CovarHomFunc a) b
CovarHomCoalgCorrect a b = Refl

public export
ContravarHomFunc : Type -> (Type -> Type)
ContravarHomFunc a = \ty => ty -> a

public export
FinContravarHomFunc : Nat -> (Type -> Type)
FinContravarHomFunc n = \ty => ty -> Fin n

public export
ContravarHomAlg : Type -> Type -> Type
ContravarHomAlg a b = (b -> a) -> b

public export
FinContravarHomAlg : Nat -> Type -> Type
FinContravarHomAlg n b = (b -> Fin n) -> b

public export
ContravarHomAlgCorrect : (a, b : Type) ->
  ContravarHomAlg a b = Algebra (ContravarHomFunc a) b
ContravarHomAlgCorrect a b = Refl

public export
ContravarHomCoalg : Type -> Type -> Type
ContravarHomCoalg a b = b -> (b -> a)

public export
FinContravarHomCoalg : Nat -> Type -> Type
FinContravarHomCoalg n b = b -> b -> Fin n

public export
ContravarHomCoalgCorrect : (a, b : Type) ->
  ContravarHomCoalg a b = Coalgebra (ContravarHomFunc a) b
ContravarHomCoalgCorrect a b = Refl

public export
FreeCovar : Type -> Type -> Type
FreeCovar = FreeMonad . CovarHomFunc

public export
FreeFinCovar : Nat -> Type -> Type
FreeFinCovar = FreeMonad . FinCovarHomFunc

public export
MuFinCovar : Nat -> Type
MuFinCovar = Mu . FinCovarHomFunc

public export
FinCovarHomAlgToAlg : {n : Nat} -> {b : Type} ->
  FinCovarHomAlg n b -> Algebra (FinCovarHomFunc n) b
FinCovarHomAlgToAlg {n=0} alg x = alg
FinCovarHomAlgToAlg {n=(S n)} alg (x, p) = FinCovarHomAlgToAlg (alg x) p

public export
finCovarFreeAlgebra : (n : Nat) -> (0 a : Type) ->
  FreeAlgebra (FinCovarHomFunc n) a
finCovarFreeAlgebra Z a x = InFree $ TermComposite ()
finCovarFreeAlgebra (S n) a (x, p) = InFree $ TermComposite (x, p)

public export
FinCovarInitialAlgebra : (n : Nat) -> InitialAlgebra (FinCovarHomFunc n)
FinCovarInitialAlgebra n = finCovarFreeAlgebra n Void

mutual
  public export
  cataFinCovar : (n : Nat) -> ParamCata (FinCovarHomFunc n)
  cataFinCovar n v a subst alg (InFree x) = case x of
    TermVar var => subst var
    TermComposite com => alg $ case n of
      Z => com
      S n' => case com of
        (x', com') =>
          (cataFinCovar (S n') v a subst alg x',
           cataFinCovarN n' (S n') v a subst alg com')

  public export
  cataFinCovarN : (n, n' : Nat) -> (v, a : Type) ->
    (v -> a) -> Algebra (FinCovarHomFunc n') a ->
    ProductN n (FreeFinCovar n' v) -> ProductN n a
  cataFinCovarN Z n' v a subst alg () = ()
  cataFinCovarN (S n) n' v a subst alg (x, p) =
    (cataFinCovar n' v a subst alg x,
     cataFinCovarN n n' v a subst alg p)

public export
finCovarMap : {n : Nat} -> {a, b : Type} ->
  (a -> b) -> FreeFinCovar n a -> FreeFinCovar n b
finCovarMap {n} {a} {b} f =
  cataFinCovar n a (FreeFinCovar n b)
    (InFree . TermVar . f)
    (InFree . TermComposite)

public export
finCovarMapN : {n, n' : Nat} -> {a, b : Type} ->
    (a -> b) -> ProductN n (FreeFinCovar n' a) -> ProductN n (FreeFinCovar n' b)
finCovarMapN {n} {n'} f =
  cataFinCovarN n n' a (FreeFinCovar n' b)
    (InFree . TermVar . f)
    (InFree . TermComposite)

public export
finCovarReturn : {n : Nat} -> {0 a : Type} -> a -> FreeFinCovar n a
finCovarReturn x = InFree $ TermVar x

public export
finCovarBigStepCata : {n : Nat} -> ParamBigStepCata (FinCovarHomFunc n)
finCovarBigStepCata {n} v a subst alg (InFree x) = case x of
  TermVar var => subst var
  TermComposite com => alg $ InFree $ TermComposite $
    mapProductN n (finCovarMap subst) com

public export
finCovarBigStepCataN : (n, n' : Nat) -> (v, a : Type) ->
  (v -> a) -> Algebra (FreeFinCovar n') a ->
  ProductN n (FreeFinCovar n' v) ->
  ProductN n a
finCovarBigStepCataN n n' v a subst alg =
  mapProductN n (finCovarBigStepCata v a subst alg)

mutual
  public export
  finCovarApply : {n : Nat} -> {a, b : Type} ->
    FreeFinCovar n (a -> b) ->
    FreeFinCovar n a ->
    FreeFinCovar n b
  finCovarApply (InFree f) (InFree x) = InFree $ case (f, x) of
    (TermVar fv, TermVar xv) =>
      TermVar $ fv xv
    (TermVar fv, TermComposite xc) =>
      TermComposite $ finCovarMapN fv xc
    (TermComposite fc, TermVar xv) =>
      TermComposite $ finCovarApplyN1 fc xv
    (TermComposite fc, TermComposite xc) =>
      TermComposite $ finCovarApplyNN fc xc

  public export
  finCovarApply11 : {n : Nat} -> {0 a, b : Type} ->
    FreeFinCovar n (a -> b) ->
    a ->
    FreeFinCovar n b
  finCovarApply11 {n=Z} (InFree f) x = InFree $ TermComposite ()
  finCovarApply11 {n=(S n)} (InFree f) x = InFree $ case f of
    TermVar fv => TermVar $ fv x
    TermComposite (f, fp) => TermComposite $
      (finCovarApply11 f x, finCovarApplyN1 fp x)

  public export
  finCovarApplyN1 : {n, n' : Nat} -> {0 a, b : Type} ->
    ProductN n (FreeFinCovar n' (a -> b)) ->
    a ->
    ProductN n (FreeFinCovar n' b)
  finCovarApplyN1 {n=Z} () x = ()
  finCovarApplyN1 {n=(S n)} (f, fp) x =
    (finCovarApply11 f x, finCovarApplyN1 fp x)

  public export
  finCovarApplyNN : {n, n' : Nat} -> {a, b : Type} ->
    ProductN n (FreeFinCovar n' (a -> b)) ->
    ProductN n (FreeFinCovar n' a) ->
    ProductN n (FreeFinCovar n' b)
  finCovarApplyNN {n=Z} () () = ()
  finCovarApplyNN {n=(S n)} (InFree f, fp) (InFree x, xp) =
    let
      recnn = finCovarApplyNN fp xp
      recapply = InFree $ case (f, x) of
        (TermVar fv, TermVar xv) =>
          TermVar $ fv xv
        (TermVar fv, TermComposite xc) =>
          TermComposite $ finCovarMapN fv xc
        (TermComposite fc, TermVar xv) =>
          TermComposite $ finCovarApplyN1 fc xv
        (TermComposite fc, TermComposite xc) =>
          TermComposite $ finCovarApplyNN fc xc
    in
    (recapply, recnn)

mutual
  public export
  finCovarJoin : {n : Nat} -> {0 a : Type} ->
    FreeFinCovar n (FreeFinCovar n a) -> FreeFinCovar n a
  finCovarJoin (InFree x) = case x of
    TermVar var => var
    TermComposite com => finCovarFreeAlgebra n a $ finCovarJoinN com

  public export
  finCovarJoinN : {n, n' : Nat} -> {0 a : Type} ->
    ProductN n (FreeFinCovar n' (FreeFinCovar n' a)) ->
    ProductN n (FreeFinCovar n' a)
  finCovarJoinN {n=Z} () = ()
  finCovarJoinN {n=(S n)} (x, p) = (finCovarJoin x, finCovarJoinN p)

{-
 -
public export
[FinCovarFunctor] (n : Nat) => Functor (FreeFinCovar n) where
  map = finCovarMap {n}
 -
 - Idris for some reason can't find the Functor or Applicative instances in
 - the Applicative or Monad declarations respectively.
 -
public export
[FinCovarApplicative] (n : Nat) =>
    Applicative (FreeFinCovar n) using FinCovarFunctor where
  pure = finCovarReturn {n}
  (<*>) = finCovarApply {n}

public export
[FinCovarMonad] (n : Nat) =>
    Monad (FreeFinCovar n) using FinCovarApplicative where
  join = finCovarJoin {n}
 -
 -}

public export
FinPolyData : Type
FinPolyData = List (Type, Nat)

public export
FinPolyFunc : FinPolyData -> (Type -> Type)
FinPolyFunc [] _ = Void
FinPolyFunc ((coeff, pow) :: l) ty =
  Either (coeff -> FinCovarHomFunc pow ty) (FinPolyFunc l ty)

public export
FinPolyAlg : FinPolyData -> Type -> Type
FinPolyAlg [] _ = ()
FinPolyAlg ((coeff, pow) :: l) ty =
  ((coeff -> FinCovarHomFunc pow ty) -> ty, FinPolyAlg l ty)

public export
FinPolyAlgToAlg : {fpd : FinPolyData} -> {a : Type} ->
  FinPolyAlg fpd a -> Algebra (FinPolyFunc fpd) a
FinPolyAlgToAlg {fpd=[]} {a} alg x = void x
FinPolyAlgToAlg {fpd=((coeff, pow) :: fpd')} {a} (leftAlg, rightAlg) x =
  case x of
    Left fields => leftAlg fields
    Right records => FinPolyAlgToAlg {fpd=fpd'} rightAlg records

public export
FreeFinPoly : FinPolyData -> Type -> Type
FreeFinPoly = FreeMonad . FinPolyFunc

public export
MuFinPoly : FinPolyData -> Type
MuFinPoly = Mu . FinPolyFunc

public export
finPolyFreeAlgebra : (fpd : FinPolyData) -> (0 a : Type) ->
  FreeAlgebra (FinPolyFunc fpd) a
finPolyFreeAlgebra [] a v = void v
finPolyFreeAlgebra fpd a x = InFree $ TermComposite x

public export
FinPolyInitialAlgebra : (fpd : FinPolyData) -> InitialAlgebra (FinPolyFunc fpd)
FinPolyInitialAlgebra fpd = finPolyFreeAlgebra fpd Void

mutual
  public export
  cataFinPoly : (fpd : FinPolyData) -> ParamCata (FinPolyFunc fpd)
  cataFinPoly fpd v a subst alg (InFree poly) = case poly of
    TermVar var => subst var
    TermComposite com => alg $ case fpd of
      [] => void com
      ((coeff, pow) :: terms) => case com of
        Left fields => Left $ cataFinPolyFuncN subst alg . fields -- (c, cataFinPolyFuncN subst alg p)
        Right poly => Right $
          cataFinPolyFunc
            {fpd=terms} {fpd'=((coeff, pow) :: terms)} {v} {a} subst alg poly

  public export
  cataFinPolyFunc : {fpd, fpd' : FinPolyData} -> {v, a : Type} ->
    (v -> a) -> Algebra (FinPolyFunc fpd') a ->
    FinPolyFunc fpd (FreeFinPoly fpd' v) -> FinPolyFunc fpd a
  cataFinPolyFunc {fpd=[]} {fpd'} {a} subst alg poly = void poly
  cataFinPolyFunc {fpd=((_, pow) :: terms)} {fpd'} {v} {a} subst alg poly =
    case poly of
      Left fields => Left $ cataFinPolyFuncN {fpd=fpd'} {pow} subst alg . fields
      Right poly' => Right $ cataFinPolyFunc {fpd=terms} {fpd'} subst alg poly'

  public export
  cataFinPolyFuncN : {fpd : FinPolyData} -> {v, a : Type} -> {pow : Nat} ->
    (v -> a) -> Algebra (FinPolyFunc fpd) a ->
    ProductN pow (FreeFinPoly fpd v) ->
    ProductN pow a
  cataFinPolyFuncN {pow=Z} subst alg () = ()
  cataFinPolyFuncN {pow=(S pow)} subst alg (x, p) =
    (cataFinPoly fpd v a subst alg x, cataFinPolyFuncN {pow} subst alg p)

public export
finPolyMap : {fpd : FinPolyData} -> {a, b : Type} ->
  (a -> b) -> FinPolyFunc fpd a -> FinPolyFunc fpd b
finPolyMap {fpd=[]} {a} {b} f poly = void poly
finPolyMap {fpd=((coeff, pow) :: terms)} {a} {b} f poly = case poly of
  Left fields => Left $ mapProductN pow f . fields
  Right poly' => Right $ finPolyMap f poly'

public export
freeFinPolyMap : {fpd : FinPolyData} -> {a, b : Type} ->
  (a -> b) -> FreeFinPoly fpd a -> FreeFinPoly fpd b
freeFinPolyMap {fpd} {a} {b} f =
  cataFinPoly fpd
    a (FreeFinPoly fpd b) (InFree . TermVar . f) (InFree . TermComposite)

public export
finPolyFuncMap : {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
  (a -> b) ->
  FinPolyFunc fpd (FreeFinPoly fpd' a) -> FinPolyFunc fpd (FreeFinPoly fpd' b)
finPolyFuncMap {a} {b} f =
  cataFinPolyFunc
    {v=a} {a=(FreeFinPoly fpd' b)}
    (InFree . TermVar . f) (InFree . TermComposite)

public export
freeFinPolyMapN : {pow : Nat} -> {fpd : FinPolyData} -> {a, b : Type} ->
  (a -> b) ->
  ProductN pow (FreeFinPoly fpd a) -> ProductN pow (FreeFinPoly fpd b)
freeFinPolyMapN {pow} {fpd} {a} {b} f =
  cataFinPolyFuncN {fpd} {v=a} {a=(FreeFinPoly fpd b)}
    (InFree . TermVar . f) (InFree . TermComposite)

public export
finPolyReturn : {fpd : FinPolyData} -> {0 a : Type} -> a -> FreeFinPoly fpd a
finPolyReturn x = InFree $ TermVar x

public export
finPolyBigStepCata : {fpd : FinPolyData} ->
  ParamBigStepCata (FinPolyFunc fpd)
finPolyBigStepCata {fpd} v a subst alg (InFree x) = case x of
  TermVar var => subst var
  TermComposite com => alg $ InFree $ TermComposite $ finPolyFuncMap subst com

public export
finPolyBigStepCataFunc : (fpd, fpd' : FinPolyData) -> (v, a : Type) ->
  (v -> a) -> Algebra (FreeFinPoly fpd') a ->
  FinPolyFunc fpd (FreeFinPoly fpd' v) ->
  FinPolyFunc fpd a
finPolyBigStepCataFunc fpd fpd' v a subst alg =
  finPolyMap {fpd} {a=(FreeFinPoly fpd' v)} {b=a}
    (finPolyBigStepCata {fpd=fpd'} v a subst alg)

public export
finPolyBigStepCataN : (fpd : FinPolyData) -> (n : Nat) -> (v, a : Type) ->
  (v -> a) -> Algebra (FreeFinPoly fpd) a ->
  ProductN n (FreeFinPoly fpd v) ->
  ProductN n a
finPolyBigStepCataN fpd n v a subst alg =
  mapProductN n (finPolyBigStepCata {fpd} v a subst alg)

{-
 - This won't work until the specification for polynomial endofunctors
 - becomes narrower.
mutual
  public export
  finPolyApply : {fpd : FinPolyData} -> {a, b : Type} ->
    FreeFinPoly fpd (a -> b) ->
    FreeFinPoly fpd a ->
    FreeFinPoly fpd b
  finPolyApply {fpd} (InFree f) (InFree x) = InFree $ case fpd of
    [] => case f of
      TermVar fvar => TermVar $ case x of
        TermVar xvar => fvar xvar
        TermComposite xcom => void xcom
      TermComposite fcom => void fcom
    ((coeff, pow) :: terms) => case (f, x) of
      (TermVar fv, TermVar xv) => TermVar $ fv xv
      (TermVar fv, TermComposite xc) => TermComposite $ case xc of
        Left fields => Left $ freeFinPolyMapN fv . fields
        Right xcr => Right $ finPolyFuncMap fv xcr
      (TermComposite fc, TermVar xv) => TermComposite $ case fc of
        Left fields => Left $ mapProductN pow (finPolyApply11 xv) . fields
        Right terms => Right $ finPolyApplyF1 xv terms
      (TermComposite fc, TermComposite xc) => TermComposite $ case (fc, xc) of
        (Left ffields, Left xfields) =>
          Left $ \c => finPolyApplyNN (ffields c) (xfields c)
        (Left ffields, Right xterms) =>
          Left $ \c => finPolyApplyNF (ffields c) xterms
        (Right fterm, Left xfields) =>
          Left $ \c => finPolyApplyFN fterm (xfields c)
        (Right fterm, Right xterms) =>
          Right $ finPolyApplyFF fterm xterms

  public export
  finPolyApply11 : {fpd : FinPolyData} -> {a, b : Type} ->
    a -> FreeFinPoly fpd (a -> b) -> FreeFinPoly fpd b
  finPolyApply11 ax (InFree fx) = InFree $ case fx of
    TermVar fv => TermVar $ fv ax
    TermComposite fcom => TermComposite $ finPolyApplyF1 ax fcom

  public export
  finPolyApplyNF : {pow : Nat} -> {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    ProductN pow (FreeFinPoly fpd' (a -> b)) ->
    FinPolyFunc fpd (FreeFinPoly fpd' a) ->
    ProductN pow (FreeFinPoly fpd' b)
  finPolyApplyNF {pow=Z} () ap = ()
  finPolyApplyNF {pow=(S pow)} (fp, fn) ap =
    (finPolyApplyFP fp ap, finPolyApplyNF fn ap)

  public export
  finPolyApplyFP : {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    FreeFinPoly fpd' (a -> b) ->
    FinPolyFunc fpd (FreeFinPoly fpd' a) ->
    FreeFinPoly fpd' b
  finPolyApplyFP {fpd=[]} (InFree fx) v = void v
  finPolyApplyFP {fpd=((coeff, pow) :: terms)} (InFree fx) xp = case (fx, xp) of
    (TermVar fv, Left xfields) =>
      InFree $ TermComposite $ finPolyApplyFP_hole_fvxf
    (TermComposite fc, Left xfields) =>
      finPolyApplyFP_hole_fcxf
    (TermVar fv, Right xterms) =>
      finPolyApplyFP_hole_fvxt
    (TermComposite fc, Right xterms) =>
      finPolyApplyFP_hole_fcxt

  public export
  finPolyApplyFN : {pow : Nat} -> {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    FinPolyFunc fpd (FreeFinPoly fpd' (a -> b)) ->
    ProductN pow (FreeFinPoly fpd' a) ->
    ProductN pow (FreeFinPoly fpd' b)
  finPolyApplyFN = finPolyApplyFN_hole

  public export
  finPolyApplyF1 : {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    a ->
    FinPolyFunc fpd (FreeFinPoly fpd' (a -> b)) ->
    FinPolyFunc fpd (FreeFinPoly fpd' b)
  finPolyApplyF1 = finPolyApply1F_hole

  public export
  finPolyApply1N : {pow : Nat} -> {fpd : FinPolyData} -> {a, b : Type} ->
    a ->
    ProductN pow (FreeFinPoly fpd (a -> b)) ->
    ProductN pow (FreeFinPoly fpd b)
  finPolyApply1N = finPolyApplyN_hole

  public export
  finPolyApplyNN : {pow : Nat} -> {fpd : FinPolyData} -> {a, b : Type} ->
    ProductN pow (FreeFinPoly fpd (a -> b)) ->
    ProductN pow (FreeFinPoly fpd a) ->
    ProductN pow (FreeFinPoly fpd b)
  finPolyApplyNN = finPolyApplyNN_hole

  public export
  finPolyApplyFF : {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    FinPolyFunc fpd (FreeFinPoly fpd' (a -> b)) ->
    FinPolyFunc fpd (FreeFinPoly fpd' a) ->
    FinPolyFunc fpd (FreeFinPoly fpd' b)
  finPolyApplyFF {fpd=[]} _ v = void v
  finPolyApplyFF {fpd=((coeff, pow) :: terms)} f x = finPolyApplyFF_hole

mutual
  public export
  finPolyJoin : {fpd : FinPolyData} -> {0 a : Type} ->
    FreeFinPoly fpd (FreeFinPoly fpd a) -> FreeFinPoly fpd a
  finPolyJoin {fpd} {a} (InFree x) = case x of
    TermVar var => var
    TermComposite com => finPolyFreeAlgebra fpd a $ finPolyJoinFunc com

  public export
  finPolyJoinN : {pow : Nat} -> {fpd : FinPolyData} -> {0 a : Type} ->
    ProductN pow (FreeFinPoly fpd (FreeFinPoly fpd a)) ->
    ProductN pow (FreeFinPoly fpd a)
  finPolyJoinN {pow=Z} () = ()
  finPolyJoinN {pow=(S pow)} (x, p) = (finPolyJoin x, finPolyJoinN {pow} p)

  public export
  finPolyJoinFunc : {fpd, fpd' : FinPolyData} -> {0 a : Type} ->
    FinPolyFunc fpd (FreeFinPoly fpd' (FreeFinPoly fpd' a)) ->
    FinPolyFunc fpd (FreeFinPoly fpd' a)
  finPolyJoinFunc {fpd=[]} {fpd'} v = void v
  finPolyJoinFunc {fpd=((coeff, pow) :: terms)} {fpd'} poly = case poly of
    Left fields => Left $ finPolyJoinN . fields
    Right poly' => Right $ finPolyJoinFunc poly'
 -}

------------------------------------------
---- Potentially-infinite polynomials ----
------------------------------------------

public export
PolyData : Type
PolyData = List (Type, Type)

public export
PolyFunc : PolyData -> (Type -> Type)
PolyFunc [] _ = Void
PolyFunc ((coeff, rep) :: l) ty =
  Either (coeff, CovarHomFunc rep ty) (PolyFunc l ty)

public export
DirichFunc : PolyData -> (Type -> Type)
DirichFunc [] _ = Void
DirichFunc ((coeff, rep) :: l) ty =
  Either (coeff, ContravarHomFunc rep ty) (DirichFunc l ty)

--------------------
--------------------
---- Core types ----
--------------------
--------------------

------------------------------------------------------------
---- Non-terminating attempt at Nat-indexed hom-functor ----
------------------------------------------------------------

public export
NatCovarHomFunc : Type -> Type
NatCovarHomFunc = CovarHomFunc Nat

public export
FreeNatCovar : Type -> Type
FreeNatCovar = FreeMonad NatCovarHomFunc

{-
mutual
  public export
  cataNatCovar : ParamCata NatCovarHomFunc
  cataNatCovar v a subst alg (InFree x) = case x of
    TermVar var => subst var
    TermComposite com => alg $ (cataNatCovar v a subst alg) . com
    -}

public export
FinRepHomFunc : Nat -> Type -> Type
FinRepHomFunc n = \ty => MuFinCovar n -> ty

-------------------------
---- Natural numbers ----
-------------------------

public export
data NatF : Type -> Type where
  ZeroF : NatF carrier
  SuccF : carrier -> NatF carrier

public export
Functor NatF where
  map _ ZeroF = ZeroF
  map f (SuccF n) = SuccF $ f n

public export
Show carrier => Show (NatF carrier) where
  show ZeroF = "0"
  show (SuccF n) = "S(" ++ show n ++ ")"

public export
NatAlg : Type -> Type
NatAlg = Algebra NatF

public export
FreeNat : Type -> Type
FreeNat = FreeMonad NatF

public export
MuNat : Type
MuNat = Mu NatF

public export
NatCoalg : Type -> Type
NatCoalg = Coalgebra NatF

public export
CofreeNat : Type -> Type
CofreeNat = CofreeComonad NatF

public export
NuNat : Type
NuNat = Nu NatF

public export
cataNatF : ParamCata NatF
cataNatF v a subst alg (InFree x) = case x of
  TermVar var => subst var
  TermComposite n => alg $ case n of
    ZeroF => ZeroF
    SuccF n' => SuccF $ cataNatF v a subst alg n'

public export
interpNatFAlg : NatAlg Nat
interpNatFAlg ZeroF = Z
interpNatFAlg (SuccF n) = S n

public export
showNatFAlg : NatAlg String
showNatFAlg = show

public export
interpFreeNatF : {v : Type} -> (subst : v -> Nat) -> FreeNat v -> Nat
interpFreeNatF {v} subst = cataNatF v Nat subst interpNatFAlg

public export
interpMuNatF : MuNat -> Nat
interpMuNatF = interpFreeNatF {v=Void} (voidF Nat)

public export
NatFZ : FreeMonad NatF a
NatFZ = InFree $ TermComposite ZeroF

public export
NatFS : FreeMonad NatF a -> FreeMonad NatF a
NatFS = InFree . TermComposite . SuccF

---------------------------------------
---- Natural numbers as a category ----
---------------------------------------

public export
ProductMNatF : Type -> Type
ProductMNatF = ProductMonad . NatF

public export
NTToProductMNatF : (Type -> Type) -> Type
NTToProductMNatF f = NaturalTransformation f ProductMNatF

public export
pairZero : NTToProductMNatF NatF
pairZero ty = MkPair {a=(NatF ty)} {b=(NatF ty)} ZeroF

public export
pairSucc : NTToProductMNatF ProductMonad
pairSucc ty = map {f=ProductMonad} {a=ty} {b=(NatF ty)} SuccF

public export
data NatLTMorphF : MorphFunctor NatF where
  NatLTZ :
    {natCarrier : Type} -> {morphCarrier : MorphCarrier natCarrier} ->
    (n : NatF natCarrier) ->
    NatLTMorphF natCarrier morphCarrier (pairZero natCarrier n)
  NatLTS :
    {natCarrier : Type} -> {morphCarrier : MorphCarrier natCarrier} ->
    (mn : ProductMonad natCarrier) -> morphCarrier mn ->
    NatLTMorphF natCarrier morphCarrier (pairSucc natCarrier mn)

public export
data NatObj : Type where
  InNat : NatF NatObj -> NatObj

public export
NatOZ : NatObj
NatOZ = InNat ZeroF

public export
NatOS : NatObj -> NatObj
NatOS = InNat . SuccF

public export
NatO1 : NatObj
NatO1 = NatOS NatOZ

public export
NatO2 : NatObj
NatO2 = NatOS NatO1

public export
ProductMNatFObj : Type
ProductMNatFObj = ProductMNatF NatObj

public export
ProductMNatObj : Type
ProductMNatObj = ProductMonad NatObj

-- A natural transformation in the product category.
public export
inFreePN : ProductMonad (NatF NatObj) -> ProductMonad NatObj
inFreePN = map {f=ProductMonad} InNat

-------------------
---- Induction ----
-------------------

public export
NatObjIndBaseCase : (NatObj -> Type) -> Type
NatObjIndBaseCase p = p NatOZ

public export
NatObjInductionStep : (NatObj -> Type) -> Type
NatObjInductionStep p = (n' : NatObj) -> p n' -> p (NatOS n')

public export
NatObjInd :
  (0 p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatObjInductionStep p ->
  (n : NatObj) -> p n
NatObjInd p z s (InNat n) = case n of
  ZeroF => z
  SuccF n' => s n' $ NatObjInd p z s n'

public export
NatObjDepIndBaseCase :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  (zp : NatObjIndBaseCase p) ->
  Type
NatObjDepIndBaseCase dp zp = dp NatOZ zp

public export
NatObjDepInductionStep :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  (sp : NatObjInductionStep p) ->
  Type
NatObjDepInductionStep {p} dp sp =
  (n' : NatObj) -> (pn : p n') -> dp n' pn -> dp (NatOS n') (sp n' pn)

public export
NatObjDepInd :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  {zp : NatObjIndBaseCase p} ->
  {sp : NatObjInductionStep p} ->
  NatObjDepIndBaseCase dp zp ->
  NatObjDepInductionStep dp sp ->
  (n : NatObj) -> dp n (NatObjInd p zp sp n)
NatObjDepInd {p} dp {zp} {sp} dzp dsp =
  NatObjInd (\n => dp n (NatObjInd p zp sp n))
    dzp (\n', dpn => dsp n' (NatObjInd p zp sp n') dpn)

public export
NatObjToMeta : NatObj -> Nat
NatObjToMeta = NatObjInd (const Nat) Z (const S)

public export
MetaToNatObj : Nat -> NatObj
MetaToNatObj Z = NatOZ
MetaToNatObj (S n) = NatOS (MetaToNatObj n)

public export
NatToMetaId : (n : NatObj) -> MetaToNatObj (NatObjToMeta n) = n
NatToMetaId = NatObjInd _ Refl $ \n, eq => rewrite eq in Refl

public export
MetaToNatId : (n : Nat) -> (NatObjToMeta (MetaToNatObj n)) = n
MetaToNatId Z = Refl
MetaToNatId (S n) = cong S $ MetaToNatId n

public export
NatObjToMetaInj : (m, n : NatObj) -> NatObjToMeta m = NatObjToMeta n -> m = n
NatObjToMetaInj m n eq =
  rewrite sym (NatToMetaId m) in
  rewrite sym (NatToMetaId n) in
  cong MetaToNatObj eq

public export
MetaToNatObjInj : (m, n : Nat) -> MetaToNatObj m = MetaToNatObj n -> m = n
MetaToNatObjInj m n eq =
  rewrite sym (MetaToNatId m) in
  rewrite sym (MetaToNatId n) in
  cong NatObjToMeta eq

public export
NatObjPredToNat : (NatObj -> Type) -> Nat -> Type
NatObjPredToNat p = p . MetaToNatObj

public export
NatPredToNatObj : (Nat -> Type) -> NatObj -> Type
NatPredToNatObj p = p . NatObjToMeta

public export
NatObjIndFromNat :
  (p : NatObj -> Type) ->
  (NatObjPredToNat p (NatObjToMeta NatOZ)) ->
  ((n' : NatObj) ->
   NatObjPredToNat p (NatObjToMeta n') ->
   NatObjPredToNat p (NatObjToMeta (NatOS n'))) ->
  (n : NatObj) -> p n
NatObjIndFromNat p z s (InNat n) = case n of
  ZeroF => z
  SuccF n' =>
    rewrite sym (NatToMetaId n') in
    s n' $ rewrite NatToMetaId n' in NatObjIndFromNat p z s n'

public export
NatIndFromNatObj :
  (p : Nat -> Type) ->
  (NatPredToNatObj p (MetaToNatObj Z)) ->
  ((n' : Nat) ->
   NatPredToNatObj p (MetaToNatObj n') ->
   NatPredToNatObj p (MetaToNatObj (S n'))) ->
  (n : Nat) -> p n
NatIndFromNatObj p z s n = case n of
  Z => z
  S n' =>
    rewrite sym (MetaToNatId n') in
    s n' $ rewrite MetaToNatId n' in NatIndFromNatObj p z s n'

public export
Show NatObj where
  show = show . NatObjToMeta

public export
NatObjPair : Type
NatObjPair = ProductMonad NatObj

public export
NatPair : Type
NatPair = ProductMonad Nat

public export
NatObjPairIndCurried :
  (p : NatObjPair -> Type) ->
  (p (NatOZ, NatOZ)) ->
  ((n' : NatObj) -> p (NatOZ, n') -> p (NatOZ, NatOS n')) ->
  ((n' : NatObj) -> p (n', NatOZ) -> p (NatOS n', NatOZ)) ->
  ((m', n' : NatObj) -> p (m', n') -> p (NatOS m', NatOS n')) ->
  (m, n : NatObj) -> p (m, n)
NatObjPairIndCurried p zz zs sz ss (InNat ZeroF) (InNat ZeroF) = zz
NatObjPairIndCurried p zz zs sz ss (InNat ZeroF) (InNat (SuccF n')) =
  zs n' $ NatObjPairIndCurried p zz zs sz ss (InNat ZeroF) n'
NatObjPairIndCurried p zz zs sz ss (InNat (SuccF m')) (InNat ZeroF) =
  sz m' $ NatObjPairIndCurried p zz zs sz ss m' (InNat ZeroF)
NatObjPairIndCurried p zz zs sz ss (InNat (SuccF m')) (InNat (SuccF n')) =
  ss m' n' $ NatObjPairIndCurried p zz zs sz ss m' n'

public export
NatObjPairIndZeroZeroCase : (NatObjPair -> Type) -> Type
NatObjPairIndZeroZeroCase p = p (NatOZ, NatOZ)

public export
NatObjPairIndZeroSuccCase : (NatObjPair -> Type) -> Type
NatObjPairIndZeroSuccCase p =
  (n' : NatObj) -> p (NatOZ, n') -> p (NatOZ, NatOS n')

public export
NatObjPairIndSuccZeroCase : (NatObjPair -> Type) -> Type
NatObjPairIndSuccZeroCase p =
  (n' : NatObj) -> p (n', NatOZ) -> p (NatOS n', NatOZ)

public export
NatObjPairIndSuccSuccCase : (NatObjPair -> Type) -> Type
NatObjPairIndSuccSuccCase p =
  (m', n' : NatObj) -> p (m', n') -> p (NatOS m', NatOS n')

public export
NatObjPairInd :
  (p : NatObjPair -> Type) ->
  NatObjPairIndZeroZeroCase p ->
  NatObjPairIndZeroSuccCase p ->
  NatObjPairIndSuccZeroCase p ->
  NatObjPairIndSuccSuccCase p ->
  (mn : NatObjPair) -> p mn
NatObjPairInd p zz zs sz ss (m, n) = NatObjPairIndCurried p zz zs sz ss m n

public export
NatObjPairDepZeroZeroCase :
  {p : NatObjPair -> Type} -> (dp : (np : NatObjPair) -> p np -> Type) ->
  (zzp : NatObjPairIndZeroZeroCase p) -> Type
NatObjPairDepZeroZeroCase dp zzp = dp (NatOZ, NatOZ) zzp

public export
NatObjPairDepZeroSuccCase :
  {p : NatObjPair -> Type} -> (dp : (np : NatObjPair) -> p np -> Type) ->
  NatObjPairIndZeroSuccCase p -> Type
NatObjPairDepZeroSuccCase {p} dp zsp =
  (n' : NatObj) -> (pzn : p (NatOZ, n')) -> dp (NatOZ, n') pzn ->
  dp (NatOZ, NatOS n') $ zsp n' pzn

public export
NatObjPairDepSuccZeroCase :
  {p : NatObjPair -> Type} -> (dp : (np : NatObjPair) -> p np -> Type) ->
  NatObjPairIndSuccZeroCase p -> Type
NatObjPairDepSuccZeroCase {p} dp szp =
  (n' : NatObj) -> (pnz : p (n', NatOZ)) -> dp (n', NatOZ) pnz ->
  dp (NatOS n', NatOZ) $ szp n' pnz

public export
NatObjPairDepSuccSuccCase :
  {p : NatObjPair -> Type} -> (dp : (np : NatObjPair) -> p np -> Type) ->
  NatObjPairIndSuccSuccCase p -> Type
NatObjPairDepSuccSuccCase {p} dp ssp =
  (n, n' : NatObj) -> (pnn : p (n, n')) -> dp (n, n') pnn ->
  dp (NatOS n, NatOS n') $ ssp n n' pnn

public export
NatObjPairDepInd :
  {p : NatObjPair -> Type} ->
  (dp : (np : NatObjPair) -> p np -> Type) ->
  {zzp : NatObjPairIndZeroZeroCase p} ->
  {zsp : NatObjPairIndZeroSuccCase p} ->
  {szp : NatObjPairIndSuccZeroCase p} ->
  {ssp : NatObjPairIndSuccSuccCase p} ->
  NatObjPairDepZeroZeroCase dp zzp ->
  NatObjPairDepZeroSuccCase dp zsp ->
  NatObjPairDepSuccZeroCase dp szp ->
  NatObjPairDepSuccSuccCase dp ssp ->
  (mn : NatObjPair) -> dp mn (NatObjPairInd p zzp zsp szp ssp mn)
NatObjPairDepInd {p} dp {zzp} {zsp} {szp} {ssp} dzzp dzsp dszp dssp =
  NatObjPairInd (\mn => dp mn (NatObjPairInd p zzp zsp szp ssp mn))
    dzzp
    (\n', dpzn => dzsp n' (NatObjPairInd p zzp zsp szp ssp (NatOZ, n')) dpzn)
    (\n', dpnz => dszp n' (NatObjPairInd p zzp zsp szp ssp (n', NatOZ)) dpnz)
    (\n, n', dpnn => dssp n n' (NatObjPairInd p zzp zsp szp ssp (n, n')) dpnn)

public export
NatObjPairToMeta : NatObjPair -> NatPair
NatObjPairToMeta = map {f=ProductMonad} NatObjToMeta

public export
NatMetaPairToObj : NatPair -> NatObjPair
NatMetaPairToObj = map {f=ProductMonad} MetaToNatObj

public export
NatPairToMetaId :
  (mn : NatObjPair) -> NatMetaPairToObj (NatObjPairToMeta mn) = mn
NatPairToMetaId (m, n) =
  rewrite NatToMetaId m in
  rewrite NatToMetaId n in
  Refl

public export
MetaToNatPairId :
  (mn : NatPair) -> NatObjPairToMeta (NatMetaPairToObj mn) = mn
MetaToNatPairId (m, n) =
  rewrite MetaToNatId m in
  rewrite MetaToNatId n in
  Refl

public export
NatObjPairPredToNat : (NatObjPair -> Type) -> NatPair -> Type
NatObjPairPredToNat p = p . NatMetaPairToObj

public export
NatPairPredToNatObj : (NatPair -> Type) -> NatObjPair -> Type
NatPairPredToNatObj p = p . NatObjPairToMeta

public export
DecEq NatObj where
  decEq m n with (decEq (NatObjToMeta m) (NatObjToMeta n))
    decEq m n | Yes eq = Yes $
      rewrite sym (NatToMetaId m) in
      rewrite sym (NatToMetaId n) in
      cong MetaToNatObj eq
    decEq m n | No neq = No $ \eq => case eq of Refl => neq Refl

public export
Eq NatObj where
  m == m' = case decEq m m' of
    Yes _ => True
    No _ => False

public export
NatObjPairIndFromNat :
  (p : NatObjPair -> Type) ->
  (NatObjPairPredToNat p (NatObjPairToMeta (NatOZ, NatOZ))) ->
  ((n' : NatObj) ->
   NatObjPairPredToNat p (NatObjPairToMeta (NatOZ, n')) ->
   NatObjPairPredToNat p (NatObjPairToMeta (NatOZ, NatOS n'))) ->
  ((n' : NatObj) ->
   NatObjPairPredToNat p (NatObjPairToMeta (n', NatOZ)) ->
   NatObjPairPredToNat p (NatObjPairToMeta (NatOS n', NatOZ))) ->
  ((m', n' : NatObj) ->
   NatObjPairPredToNat p (NatObjPairToMeta (m', n')) ->
   NatObjPairPredToNat p (NatObjPairToMeta (NatOS m', NatOS n'))) ->
  (m, n : NatObj) -> p (m, n)
NatObjPairIndFromNat p zz zs sz ss (InNat ZeroF) (InNat ZeroF) =
  zz
NatObjPairIndFromNat p zz zs sz ss (InNat ZeroF) (InNat $ SuccF n') =
  rewrite sym (NatPairToMetaId (NatOZ, InNat $ SuccF n')) in
  zs n' $
    rewrite NatPairToMetaId (NatOZ, n') in
    NatObjPairIndFromNat p zz zs sz ss (InNat ZeroF) n'
NatObjPairIndFromNat p zz zs sz ss (InNat $ SuccF m') (InNat ZeroF) =
  rewrite sym (NatPairToMetaId (InNat $ SuccF m', NatOZ)) in
  sz m' $
    rewrite NatPairToMetaId (m', NatOZ) in
    NatObjPairIndFromNat p zz zs sz ss m' (InNat ZeroF)
NatObjPairIndFromNat p zz zs sz ss (InNat $ SuccF m') (InNat $ SuccF n') =
  rewrite sym (NatPairToMetaId (InNat $ SuccF m', InNat $ SuccF n')) in
  ss m' n' $
    rewrite NatPairToMetaId (m', n') in
    NatObjPairIndFromNat p zz zs sz ss m' n'

public export
NatPairIndFromNatObj :
  (p : NatPair -> Type) ->
  (NatPairPredToNatObj p (NatMetaPairToObj (Z, Z))) ->
  ((n' : Nat) ->
   NatPairPredToNatObj p (NatMetaPairToObj (Z, n')) ->
   NatPairPredToNatObj p (NatMetaPairToObj (Z, S n'))) ->
  ((n' : Nat) ->
   NatPairPredToNatObj p (NatMetaPairToObj (n', Z)) ->
   NatPairPredToNatObj p (NatMetaPairToObj (S n', Z))) ->
  ((m', n' : Nat) ->
   NatPairPredToNatObj p (NatMetaPairToObj (m', n')) ->
   NatPairPredToNatObj p (NatMetaPairToObj (S m', S n'))) ->
  (m, n : Nat) -> p (m, n)
NatPairIndFromNatObj p zz zs sz ss Z Z =
  zz
NatPairIndFromNatObj p zz zs sz ss Z (S n') =
  rewrite sym (MetaToNatPairId (Z, S n')) in
  zs n' $
    rewrite MetaToNatPairId (Z, n') in
    NatPairIndFromNatObj p zz zs sz ss Z n'
NatPairIndFromNatObj p zz zs sz ss (S m') Z =
  rewrite sym (MetaToNatPairId (S m', Z)) in
  sz m' $
    rewrite MetaToNatPairId (m', Z) in
    NatPairIndFromNatObj p zz zs sz ss m' Z
NatPairIndFromNatObj p zz zs sz ss (S m') (S n') =
  rewrite sym (MetaToNatPairId (S m', S n')) in
  ss m' n' $
    rewrite MetaToNatPairId (m', n') in
    NatPairIndFromNatObj p zz zs sz ss m' n'

public export
MapAlg : (Type -> Type) -> Type -> Type -> Type
MapAlg f x v = (v -> x) -> f v -> x

public export
mapAlg : {0 f : Type -> Type} -> Functor f => {0 x, v : Type} ->
  Algebra f x ->
  MapAlg f x v
mapAlg alg m = alg . map {f} m

public export
MapAlgF : (Type -> Type) -> Type -> Type
MapAlgF f x = (v : Type) -> MapAlg f x v

public export
mapAlgF : {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  MapAlgF f x
mapAlgF alg v = mapAlg {v} alg

public export
FunctorIter : (Type -> Type) -> NatObj -> Type -> Type
FunctorIter f n a = NatObjInd (const Type) a (const f) n

public export
FunctorIterIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> FunctorIter f n' a -> Type) -> Type
FunctorIterIndBaseCase {a} p = (z : a) -> p NatOZ z

public export
FunctorIterInductionStep : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> FunctorIter f n' a -> Type) -> Type
FunctorIterInductionStep {f} {a} p =
  (n' : NatObj) ->
   ((ty : FunctorIter f n' a) -> p n' ty) ->
   ((ty : f (FunctorIter f n' a)) -> p (NatOS n') ty)

public export
FunctorIterInd : {0 f : Type -> Type} -> {0 a : Type} ->
  (0 p : (n' : NatObj) -> FunctorIter f n' a -> Type) ->
  FunctorIterIndBaseCase {f} {a} p ->
  FunctorIterInductionStep {f} {a} p ->
  (n : NatObj) -> (ty : FunctorIter f n a) -> p n ty
FunctorIterInd {f} {a} p =
  NatObjInd (\n' => (ty : FunctorIter f n' a) -> p n' ty)

public export
FunctorIterMapAlg : (Type -> Type) -> Type -> Type -> Type
FunctorIterMapAlg f x v = (v -> x) -> (n : NatObj) -> FunctorIter f n v -> x

public export
functorIterMapAlg :
  {0 f : Type -> Type} -> Functor f => {0 v, x : Type} ->
  Algebra f x ->
  FunctorIterMapAlg f x v
functorIterMapAlg {f} {x} {v} alg m =
  FunctorIterInd (\_, _ => x) m $ \n => mapAlg alg

public export
FunctorIterMapAlgF : (Type -> Type) -> Type -> Type
FunctorIterMapAlgF f x = (v : Type) -> FunctorIterMapAlg f x v

public export
functorIterMapAlgF :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  FunctorIterMapAlgF f x
functorIterMapAlgF alg v = functorIterMapAlg {v} alg

public export
FunctorIterAlg : (Type -> Type) -> Type -> Type
FunctorIterAlg f a = (n : NatObj) -> Algebra (FunctorIter f n) a

public export
FunctorIterAlgF : (Type -> Type) -> Type
FunctorIterAlgF f = (a : Type) -> FunctorIterAlg f a

public export
functorIterAlg :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  FunctorIterAlg f x
functorIterAlg {f} {x} alg = functorIterMapAlg {v=x} alg id

public export
functorIterMap :
  {0 f : Type -> Type} -> Functor f =>
  {0 a, b : Type} ->
  (n : NatObj) -> (a -> b) -> FunctorIter f n a -> FunctorIter f n b
functorIterMap {f} {b} n m =
    FunctorIterInd (\n', _ => FunctorIter f n' b) m (\n' => map {f}) n

public export
(n : NatObj) => Functor f => Functor (FunctorIter f n) where
  map m {n} = functorIterMap n m

public export
functorIterShow : {0 f : Type -> Type} -> {0 a : Type} -> Functor f => Show a =>
  (sf : Algebra f String) -> (n : NatObj) -> (ty : FunctorIter f n a) -> String
functorIterShow {f} {a} sf = functorIterMapAlg {v=a} {x=String} sf show

public export
Functor f => Show a => Show (f String) => (n : NatObj) =>
    Show (FunctorIter f n a) where
  show {f} {a} {n} = functorIterShow {f} {a} show n

public export
FunctorIterDepIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  ((n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  FunctorIterIndBaseCase {f} {a} p ->
  Type
FunctorIterDepIndBaseCase {f} {a} {p} dp zp =
  (z : a) -> dp NatOZ z (zp z)

public export
FunctorIterDepInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  ((n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  FunctorIterInductionStep {f} {a} p ->
  Type
FunctorIterDepInductionStep {f} {a} {p} dp sp =
  (n' : NatObj) ->
   (pty : ((ty : FunctorIter f n' a) -> p n' ty)) ->
   (dephyp : (ty : FunctorIter f n' a) -> dp n' ty (pty ty)) ->
   ((ty : f (FunctorIter f n' a)) -> dp (NatOS n') ty (sp n' pty ty))

public export
FunctorIterDepInd : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  (dp : (n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  {zp : FunctorIterIndBaseCase {f} {a} p} ->
  {sp : FunctorIterInductionStep {f} {a} p} ->
  FunctorIterDepIndBaseCase {f} {a} {p} dp zp ->
  FunctorIterDepInductionStep {f} {a} {p} dp sp ->
  (n : NatObj) -> (ty : FunctorIter f n a) ->
  dp n ty (FunctorIterInd {f} {a} p zp sp n ty)
FunctorIterDepInd {f} {a} {p} dp {zp} {sp} dzp dsp =
  FunctorIterInd {f} {a}
    (\n', ty => dp n' ty (FunctorIterInd {f} {a} p zp sp n' ty))
    dzp
    (\n => dsp n (FunctorIterInd {f} {a} p zp sp n))

public export
data OmegaStep : (Type -> Type) -> Type -> Type where
  OmegaInj : carrier -> OmegaStep f carrier
  OmegaIter : f carrier -> OmegaStep f carrier

public export
omegaStepElim :
  {0 f : Type -> Type} -> {0 a : Type} -> {0 b : OmegaStep f a -> Type} ->
  ((x : a) -> b (OmegaInj x)) ->
  ((fx : f a) -> b (OmegaIter fx)) ->
  (x : OmegaStep f a) -> b x
omegaStepElim {f} {a} {b} elimInj elimIter (OmegaInj x) = elimInj x
omegaStepElim {f} {a} {b} elimInj elimIter (OmegaIter fx) = elimIter fx

public export
OmegaMapAlg : (Type -> Type) -> Type -> Type -> Type
OmegaMapAlg f x v = (v -> x) -> OmegaStep f v -> x

public export
omegaMapAlg :
  {0 f : Type -> Type} -> Functor f => {0 x, v : Type} ->
  (f x -> x) ->
  OmegaMapAlg f x v
omegaMapAlg alg carrier = omegaStepElim carrier $ mapAlg alg carrier

public export
OmegaMapAlgF : (Type -> Type) -> Type -> Type
OmegaMapAlgF f x = (v : Type) -> OmegaMapAlg f x v

public export
omegaMapAlgF :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  (f x -> x) ->
  OmegaMapAlgF f x
omegaMapAlgF alg v = omegaMapAlg {v} alg

public export
OmegaAlg : (Type -> Type) -> Type -> Type
OmegaAlg f a = Algebra (OmegaStep f) a

public export
omegaAlg :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  OmegaAlg f x
omegaAlg {f} {x} alg = omegaMapAlg {v=x} alg id

public export
omegaStepMap :
  {0 f : Type -> Type} -> Functor f =>
  {0 a, b : Type} ->
  (a -> b) -> OmegaStep f a -> OmegaStep f b
omegaStepMap m = omegaStepElim (OmegaInj . m) (OmegaIter . map m)

public export
Functor f => Functor (OmegaStep f) where
  map = omegaStepMap

public export
omegaStepShow : {0 f : Type -> Type} -> {0 a : Type} -> Functor f => Show a =>
  Algebra f String -> OmegaStep f a -> String
omegaStepShow {f} {a} fAlg = omegaMapAlg {f} {x=String} {v=a} fAlg show

public export
Functor f => Show a => Show (f String) => Show (OmegaStep f a) where
  show = omegaStepShow show

public export
OmegaChain : (Type -> Type) -> NatObj -> Type -> Type
OmegaChain = FunctorIter . OmegaStep

public export
ChainIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> OmegaChain f n' a -> Type) -> Type
ChainIndBaseCase {f} = FunctorIterIndBaseCase {f=(OmegaStep f)}

public export
ChainInductionStep : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> OmegaChain f n' a -> Type) -> Type
ChainInductionStep {f} = FunctorIterInductionStep {f=(OmegaStep f)}

public export
ChainInduction : {0 f : Type -> Type} -> {0 a : Type} ->
  (0 p : (n' : NatObj) -> OmegaChain f n' a -> Type) ->
  ChainIndBaseCase {f} {a} p ->
  ChainInductionStep {f} {a} p ->
  (n : NatObj) -> (ty : OmegaChain f n a) -> p n ty
ChainInduction {f} = FunctorIterInd {f=(OmegaStep f)}

public export
ChainMapAlg : (Type -> Type) -> Type -> Type -> Type
ChainMapAlg f x v = (v -> x) -> (n : NatObj) -> OmegaChain f n v -> x

public export
chainMapAlg :
  {0 f : Type -> Type} -> Functor f => {0 x, v : Type} ->
  Algebra f x ->
  ChainMapAlg f x v
chainMapAlg {f} {x} alg m =
  ChainInduction (\_, _ => x) m $ \_ => omegaMapAlg alg

public export
ChainMapAlgF : (Type -> Type) -> Type -> Type
ChainMapAlgF f x = (v : Type) -> ChainMapAlg f x v

public export
chainMapAlgF :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  ChainMapAlgF f x
chainMapAlgF alg v = chainMapAlg {v} alg

public export
ChainAlg : (Type -> Type) -> Type -> Type
ChainAlg f a = (n : NatObj) -> Algebra (OmegaChain f n) a

public export
ChainAlgF : (Type -> Type) -> Type
ChainAlgF f = (a : Type) -> ChainAlg f a

public export
chainAlg :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  ChainAlg f x
chainAlg {f} {x} alg = chainMapAlg {v=x} alg id

public export
omegaChainMap : {0 f : Type -> Type} -> Functor f => {0 a, b : Type} ->
  (m : a -> b) -> (n : NatObj) -> OmegaChain f n a -> OmegaChain f n b
omegaChainMap {f} m =
  ChainInduction (\n', _ => OmegaChain f n' b) m (\n' => map {f=(OmegaStep f)})

public export
(n : NatObj) => Functor f => Functor (OmegaChain f n) where
  map {n} {f} m = omegaChainMap {f} m n

public export
omegaChainShow : {0 f : Type -> Type} -> {0 a : Type} -> Functor f => Show a =>
  (sf : Algebra f String) -> (n : NatObj) -> (ty : OmegaChain f n a) -> String
omegaChainShow {f} {a} sf = chainMapAlg {v=a} {x=String} sf show

public export
Functor f => Show a => Show (f String) => (n : NatObj) =>
    Show (OmegaChain f n a) where
  show {f} {a} {n} = omegaChainShow {f} {a} show n

public export
ChainDepIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  ((n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  ChainIndBaseCase {f} {a} p ->
  Type
ChainDepIndBaseCase {f} = FunctorIterDepIndBaseCase {f=(OmegaStep f)}

public export
ChainDepInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  ((n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  ChainInductionStep {f} {a} p ->
  Type
ChainDepInductionStep {f} = FunctorIterDepInductionStep {f=(OmegaStep f)}

public export
ChainDepInd : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  (dp : (n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  {zp : ChainIndBaseCase {f} {a} p} ->
  {sp : ChainInductionStep {f} {a} p} ->
  ChainDepIndBaseCase {f} {a} {p} dp zp ->
  ChainDepInductionStep {f} {a} {p} dp sp ->
  (n : NatObj) -> (ty : OmegaChain f n a) ->
  dp n ty (ChainInduction {f} {a} p zp sp n ty)
ChainDepInd {f} = FunctorIterDepInd {f=(OmegaStep f)}

public export
OmegaInjN : {f : Type -> Type} -> {a : Type} ->
  (n : NatObj) -> (x : a) -> OmegaChain f n a
OmegaInjN {f} {a} n x =
  NatObjInd (\n' => OmegaChain f n' a) x (\_ => OmegaInj) n

public export
OmegaN : {f : Type -> Type} -> Functor f => {a : Type} ->
  {n : NatObj} -> FunctorIter f n a -> OmegaChain f n a
OmegaN {f} {a} {n} =
  NatObjInd (\n' => FunctorIter f n' a -> OmegaChain f n' a)
    id
    (\n', hyp => OmegaIter . map {f} hyp)
    n

-- AKA free monad.
public export
OmegaColimit : (Type -> Type) -> Type -> Type
OmegaColimit f a = (n : NatObj ** OmegaChain f n a)

public export
PredColimitToChain : {f : Type -> Type} -> {a : Type} ->
  (OmegaColimit f a -> Type) ->
  ((n : NatObj) -> OmegaChain f n a -> Type)
PredColimitToChain p n ty = p (n ** ty)

public export
PredChainToColimit : {f : Type -> Type} -> {a : Type} ->
  ((n : NatObj) -> OmegaChain f n a -> Type) ->
  (OmegaColimit f a -> Type)
PredChainToColimit p (n ** ty) = p n ty

public export
ColimitIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  (p : OmegaColimit f a -> Type) -> Type
ColimitIndBaseCase = ChainIndBaseCase . PredColimitToChain

public export
ColimitInductionStep : {f : Type -> Type} -> {a : Type} ->
  (p : OmegaColimit f a -> Type) -> Type
ColimitInductionStep = ChainInductionStep . PredColimitToChain

public export
ColimitInduction : {0 f : Type -> Type} -> {0 a : Type} ->
  (0 p : OmegaColimit f a -> Type) ->
  ColimitIndBaseCase {f} {a} p ->
  ColimitInductionStep {f} {a} p ->
  (ty : OmegaColimit f a) -> p ty
ColimitInduction p z s (n ** ty) =
  ChainInduction (PredColimitToChain p) z s n ty

-- AKA parameterized catamorphism.
public export
ColimitMapAlg : (Type -> Type) -> Type -> Type -> Type
ColimitMapAlg f x v = (v -> x) -> OmegaColimit f v -> x

public export
colimitMapAlg :
  {0 f : Type -> Type} -> {isF : Functor f} -> {0 x, v : Type} ->
  Algebra f x ->
  ColimitMapAlg f x v
colimitMapAlg alg m (n ** c) = chainMapAlg alg m n c

public export
ColimitMapAlgF : (Type -> Type) -> Type -> Type
ColimitMapAlgF f x = (v : Type) -> ColimitMapAlg f x v

public export
colimitMapAlgF :
  {0 f : Type -> Type} -> {isF : Functor f} -> {0 x : Type} ->
  Algebra f x ->
  ColimitMapAlgF f x
colimitMapAlgF {isF} alg v = colimitMapAlg {isF} {v} alg

public export
ColimitAlg : (Type -> Type) -> Type -> Type
ColimitAlg f a = Algebra (OmegaColimit f) a

public export
ColimitAlgF : (Type -> Type) -> Type
ColimitAlgF f = (a : Type) -> Algebra (OmegaColimit f) a

public export
colimitAlg :
  {0 f : Type -> Type} -> {isF : Functor f} -> {0 x : Type} ->
  Algebra f x ->
  ColimitAlg f x
colimitAlg {f} {isF} {x} alg = colimitMapAlg {isF} {v=x} alg id

public export
omegaColimitMap : {0 f : Type -> Type} -> Functor f => {0 a, b : Type} ->
  (a -> b) -> OmegaColimit f a -> OmegaColimit f b
omegaColimitMap {f} {a} {b} m (n ** c) = (n ** omegaChainMap {f} m n c)

public export
Functor f => Functor (OmegaColimit f) where
  map = omegaColimitMap

public export
omegaColimitShow :
  {0 f : Type -> Type} -> {0 a : Type} -> Functor f => Show a =>
  Algebra f String -> OmegaColimit f a -> String
omegaColimitShow {f} {a} sf (n ** c) =
  "(" ++ show n ++ ":" ++ omegaChainShow {f} {a} sf n c ++ ")"

public export
Functor f => Show a => Show (f String) => Show (OmegaColimit f a) where
  show {f} {a} = omegaColimitShow {f} {a} show

public export
DepPredColimitToChain : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  ((c : OmegaColimit f a) -> p c -> Type) ->
  ((n : NatObj) ->
   (c : OmegaChain f n a) ->
   PredColimitToChain {f} {a} p n c ->
   Type)
DepPredColimitToChain dp n c pc = dp (n ** c) pc

public export
DepPredChainToColimit : {f : Type -> Type} -> {a : Type} ->
  {p : (n : NatObj) -> OmegaChain f n a -> Type} ->
  ((n : NatObj) -> (c : OmegaChain f n a) -> p n c -> Type) ->
  ((c : OmegaColimit f a) -> PredChainToColimit {f} {a} p c -> Type)
DepPredChainToColimit dp (n ** c) pc = dp n c pc

public export
ColimitDepIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  ((c : OmegaColimit f a) -> p c -> Type) ->
  ColimitIndBaseCase {f} {a} p ->
  Type
ColimitDepIndBaseCase = ChainDepIndBaseCase . DepPredColimitToChain

public export
ColimitDepInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  ((c : OmegaColimit f a) -> p c -> Type) ->
  ColimitInductionStep {f} {a} p ->
  Type
ColimitDepInductionStep = ChainDepInductionStep . DepPredColimitToChain

public export
ColimitDepInd : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  (dp : (c : OmegaColimit f a) -> p c -> Type) ->
  {zp : ColimitIndBaseCase {f} {a} p} ->
  {sp : ColimitInductionStep {f} {a} p} ->
  ColimitDepIndBaseCase {f} {a} {p} dp zp ->
  ColimitDepInductionStep {f} {a} {p} dp sp ->
  (c : OmegaColimit f a) ->
  dp c (ColimitInduction {f} {a} p zp sp c)
ColimitDepInd {p} dp {zp} {sp} dzp dsp (n ** c) =
  ChainDepInd
    {p=(PredColimitToChain p)}
    (DepPredColimitToChain dp)
    {zp} {sp} dzp dsp n c

public export
InitialIter : (Type -> Type) -> NatObj -> Type
InitialIter f n = FunctorIter f n Void

public export
InitialChain : (Type -> Type) -> NatObj -> Type
InitialChain f n = OmegaChain f n Void

public export
InitialColimit : (Type -> Type) -> Type
InitialColimit f = OmegaColimit f Void

public export
ColimitCata : (Type -> Type) -> Type
ColimitCata f = (x : Type) -> Algebra f x -> InitialColimit f -> x

public export
colimitCata : {f : Type -> Type} -> {isF : Functor f} -> ColimitCata f
colimitCata {f} {isF} x alg = colimitMapAlg {f} {isF} {x} {v=Void} alg (voidF _)

-----------------------------------
---- Product functor iteration ----
-----------------------------------

public export
ProductFunctor : Type -> Type
ProductFunctor t = (t -> Type) -> t -> Type

public export
ProductFunctorIter : {t : Type} ->
  ProductFunctor t -> NatObj -> ProductFunctor t
ProductFunctorIter {t} f n a = NatObjInd (const $ t -> Type) a (const f) n

public export
ProductFunctorIterIndBaseCase :
  {t : Type} -> {f : ProductFunctor t} -> {a : t -> Type} ->
  (p : (n : NatObj) -> (x : t) -> ProductFunctorIter f n a x -> Type) -> Type
ProductFunctorIterIndBaseCase {t} {a} p = (x : t) -> (z : a x) -> p NatOZ x z

public export
ProductFunctorIterInductionStep :
  {t : Type} -> {f : ProductFunctor t} -> {a : t -> Type} ->
  (p : (n : NatObj) -> (x : t) -> ProductFunctorIter f n a x -> Type) -> Type
ProductFunctorIterInductionStep {t} {f} {a} p =
  (n : NatObj) ->
  ((x : t) -> (it : ProductFunctorIter f n a x) -> p n x it) ->
  ((x : t) -> (it : f (ProductFunctorIter f n a) x) -> p (NatOS n) x it)

public export
ProductFunctorIterInd :
  {0 t : Type} -> {0 f : ProductFunctor t} -> {0 a : t -> Type} ->
  (0 p : (n : NatObj) -> (x : t) -> ProductFunctorIter f n a x -> Type) ->
  ProductFunctorIterIndBaseCase {f} {a} p ->
  ProductFunctorIterInductionStep {f} {a} p ->
  (n : NatObj) -> (x : t) -> (it : ProductFunctorIter f n a x) -> p n x it
ProductFunctorIterInd {t} {f} {a} p =
  NatObjInd (\n => (x : t) -> (it : ProductFunctorIter f n a x) -> p n x it)

public export
ProductFunctorIterMapAlg : {t : Type} ->
  ProductFunctor t -> (t -> Type) -> (t -> Type) -> Type
ProductFunctorIterMapAlg {t} f x v =
  ((elem : t) -> v elem -> x elem) ->
  (n : NatObj) -> (elem : t) -> ProductFunctorIter f n v elem -> x elem

--------------------------
---- Initial algebras ----
--------------------------

public export
FInitAlg : (Type -> Type) -> Type
FInitAlg f = Algebra f (InitialColimit f)

public export
FInitAlgLift : (Type -> Type) -> Type
FInitAlgLift f = Algebra f (f (InitialColimit f))

public export
FInitAlgInv : (Type -> Type) -> Type
FInitAlgInv f = Coalgebra f (InitialColimit f)

public export
fInitAlgInv : {f : Type -> Type} -> {isF : Functor f} ->
  FInitAlg f -> FInitAlgInv f
fInitAlgInv {f} {isF} alg =
  colimitCata {isF} (f (InitialColimit f)) (map {f} alg)

public export
InitAlgCorrect : {f : Type -> Type} -> {isF : Functor f} -> FInitAlg f -> Type
InitAlgCorrect {f} {isF} alg =
  ExtEq
    (fInitAlgInv {isF} alg . alg)
    (map {f} alg . map {f} (fInitAlgInv {isF} alg))

-----------------------------------------------------------------
---- Slices of natural number category as functor iterations ----
-----------------------------------------------------------------

public export
NatStrictPrefix : NatObj -> Type
NatStrictPrefix = InitialIter Maybe

public export
NatLTSlice : NatObj -> Type
NatLTSlice n = FunctorIter (Either ()) n ()

public export
NatLTSliceZ : (n : NatObj) -> NatLTSlice n
NatLTSliceZ (InNat ZeroF) = ()
NatLTSliceZ (InNat $ SuccF _) = Left ()

public export
ltSliceObjToNatStep :
  (n : NatObj) -> (NatLTSlice n -> NatObj) -> NatLTSlice (NatOS n) -> NatObj
ltSliceObjToNatStep n step (Left ()) = NatOZ
ltSliceObjToNatStep n step (Right n') = NatOS $ step n'

public export
ltSliceObjToNat : {n : NatObj} -> NatLTSlice n -> NatObj
ltSliceObjToNat {n} =
  FunctorIterInd (\_, _ => NatObj) (const NatOZ) ltSliceObjToNatStep n

public export
ltSliceOfSliceObjStep : (n : NatObj) ->
  ((slice : NatLTSlice n) ->
   (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
   NatLTSlice n) ->
  (slice : NatLTSlice (NatOS n)) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n=(NatOS n)} slice)) ->
  NatLTSlice (NatOS n)
ltSliceOfSliceObjStep n hyp (Left ()) slice' = Left ()
ltSliceOfSliceObjStep n hyp (Right slice) slice' =
  case slice' of
    Left () => Left ()
    Right slice'' => Right $ hyp slice slice''

public export
ltSliceOfSliceObj : {n : NatObj} ->
  (slice : NatLTSlice n) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
  NatLTSlice n
ltSliceOfSliceObj {n} =
  NatObjInd
    (\n' =>
      (slice : NatLTSlice n') ->
      (slice' : NatLTSlice (ltSliceObjToNat {n=n'} slice)) ->
      NatLTSlice n')
    (\_, _ => ())
    ltSliceOfSliceObjStep
    n

public export
ltSliceOfSliceObjCorrectStep : (n : NatObj) ->
  ((slice : NatLTSlice n) ->
   (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
    ltSliceObjToNat {n=(ltSliceObjToNat {n} slice)} slice' =
    ltSliceObjToNat {n} (ltSliceOfSliceObj {n} slice slice')) ->
  (slice : NatLTSlice (NatOS n)) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n=(NatOS n)} slice)) ->
    ltSliceObjToNat {n=(ltSliceObjToNat {n=(NatOS n)} slice)} slice' =
    ltSliceObjToNat {n=(NatOS n)} (ltSliceOfSliceObj {n=(NatOS n)} slice slice')
ltSliceOfSliceObjCorrectStep n hyp (Left ()) slice' =
  Refl
ltSliceOfSliceObjCorrectStep n hyp (Right slice) slice' =
  case slice' of
    Left () => Refl
    Right slice'' => cong (InNat . SuccF) $ hyp slice slice''

public export
ltSliceOfSliceObjCorrect : {n : NatObj} ->
  (slice : NatLTSlice n) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
    ltSliceObjToNat {n=(ltSliceObjToNat {n} slice)} slice' =
    ltSliceObjToNat {n} (ltSliceOfSliceObj {n} slice slice')
ltSliceOfSliceObjCorrect {n} =
  NatObjInd
    (\n' =>
      (slice : NatLTSlice n') ->
      (slice' : NatLTSlice (ltSliceObjToNat {n=n'} slice)) ->
        ltSliceObjToNat {n=(ltSliceObjToNat {n=n'} slice)} slice' =
        ltSliceObjToNat {n=n'} (ltSliceOfSliceObj {n=n'} slice slice'))
    (\_, _ => Refl)
    ltSliceOfSliceObjCorrectStep
    n

public export
ltSliceMax : (n : NatObj) -> NatLTSlice n
ltSliceMax = NatObjInd NatLTSlice () (\_ => Right)

public export
ltSliceMaxCorrect : (n : NatObj) -> ltSliceObjToNat {n} (ltSliceMax n) = n
ltSliceMaxCorrect = NatObjInd _ Refl (\_ => cong (InNat . SuccF))

public export
NatLTGenInductionStep : (NatObj -> Type) -> Type
NatLTGenInductionStep p =
  (n' : NatObj) ->
  ((sl : NatLTSlice n') -> p (ltSliceObjToNat sl)) ->
  p (NatOS n')

public export
ltSubSlice : {n : NatObj} ->
  (p : NatObj -> Type) ->
  ((slice : NatLTSlice n) -> p (ltSliceObjToNat {n} slice)) ->
  (slice : NatLTSlice n) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
  p (ltSliceObjToNat {n=(ltSliceObjToNat {n} slice)} slice')
ltSubSlice {n} p hyp slice slice' =
  replace {p} (sym $ ltSliceOfSliceObjCorrect slice slice') $
    hyp $ ltSliceOfSliceObj slice slice'

public export
NatLTGenIndStrengthedDefinitionStep :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatLTGenInductionStep p ->
  (n : NatObj) -> ((slice : NatLTSlice n) -> p (ltSliceObjToNat {n} slice)) ->
  (slice : NatLTSlice (NatOS n)) -> p (ltSliceObjToNat {n=(NatOS n)} slice)
NatLTGenIndStrengthedDefinitionStep p z s n step (Left ()) = z
NatLTGenIndStrengthedDefinitionStep p z s n step (Right slice) =
  s (ltSliceObjToNat slice) $ \slice' => ltSubSlice p step slice slice'

public export
NatLTGenIndStrengthened :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatLTGenInductionStep p ->
  (n : NatObj) -> ((sl : NatLTSlice n) -> p (ltSliceObjToNat {n} sl))
NatLTGenIndStrengthened p z s =
  FunctorIterInd _ (const z) (NatLTGenIndStrengthedDefinitionStep p z s)

public export
NatLTGenInd :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatLTGenInductionStep p ->
  (n : NatObj) -> p n
NatLTGenInd p z s n =
  rewrite sym (ltSliceMaxCorrect n) in
  NatLTGenIndStrengthened p z s n (ltSliceMax n)

----------------------------------------------------------
---- Natural number morphisms (in less-than category) ----
----------------------------------------------------------

public export
ProductMNatPred : Type
ProductMNatPred = MorphCarrier NatObj

public export
data NatLTMorph : ProductMNatPred where
  InNatLT :
    (mn : ProductMNatF NatObj) ->
    NatLTMorphF NatObj NatLTMorph mn ->
    NatLTMorph (Library.IdrisCategories.inFreePN mn)

public export
isLTZ : {mn : NatObjPair} -> NatLTMorph mn -> Bool
isLTZ (InNatLT _ (NatLTZ _)) = True
isLTZ (InNatLT _ (NatLTS _ _)) = False

public export
NatLTMorphToSucc : {m, n : NatObj} ->
  NatLTMorph (m, n) -> NatLTMorph (NatOS m, NatOS n)
NatLTMorphToSucc morph = InNatLT _ (NatLTS _ morph)

public export
NatMorphIndCurried :
  (p : (mn : NatObjPair) -> NatLTMorph mn -> Type) ->
  ((n : NatF NatObj) -> p (NatOZ, InNat n) $ InNatLT (ZeroF, n) $ NatLTZ n) ->
  ((m, n : NatObj) ->
   (morph : NatLTMorph (m, n)) ->
   p (m, n) morph ->
   p (InNat $ SuccF m, InNat $ SuccF n) $
    InNatLT (SuccF m, SuccF n) $ NatLTS (m, n) morph) ->
  (m, n : NatObj) -> (morph : NatLTMorph (m, n)) -> p (m, n) morph
NatMorphIndCurried p zn ss (InNat ZeroF) _ morph =
  case morph of
    InNatLT _ (NatLTZ $ n'') =>
      zn n''
    InNatLT _ (NatLTS (_, _) _) impossible
NatMorphIndCurried p zn ss (InNat $ SuccF _) (InNat ZeroF) morph =
  case morph of
    InNatLT _ (NatLTZ $ ZeroF) impossible
    InNatLT _ (NatLTS (_, _) _) impossible
NatMorphIndCurried p zn ss (InNat $ SuccF _) (InNat $ SuccF _) morph =
  case morph of
    InNatLT _ (NatLTZ $ SuccF _) impossible
    InNatLT _ (NatLTS (m'', n'') morph') =>
      ss m'' n'' morph' $ NatMorphIndCurried p zn ss m'' n'' morph'

public export
NatMorphIndZCase : (p : (mn : NatObjPair) -> NatLTMorph mn -> Type) -> Type
NatMorphIndZCase p =
  (n : NatF NatObj) -> p (NatOZ, InNat n) $ InNatLT (ZeroF, n) $ NatLTZ n

public export
NatMorphIndSCase : (p : (mn : NatObjPair) -> NatLTMorph mn -> Type) -> Type
NatMorphIndSCase p =
  (m, n : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  p (m, n) morph ->
  p (InNat $ SuccF m, InNat $ SuccF n) $
    InNatLT (SuccF m, SuccF n) $ NatLTS (m, n) morph

public export
NatMorphInd :
  (p : (mn : NatObjPair) -> NatLTMorph mn -> Type) ->
  NatMorphIndZCase p ->
  NatMorphIndSCase p ->
  (mn : NatObjPair) -> (morph : NatLTMorph mn) -> p mn morph
NatMorphInd p zn ss (m, n) = NatMorphIndCurried p zn ss m n

public export
NatMorphDepIndZCase :
  {p : (mn : NatObjPair) -> NatLTMorph mn -> Type} ->
  (dp : (mn : NatObjPair) -> (morph : NatLTMorph mn) -> p mn morph -> Type) ->
  (zp : NatMorphIndZCase p) ->
  Type
NatMorphDepIndZCase {p} dp zp =
  (n : NatF NatObj) ->
  dp (NatOZ, InNat n) (InNatLT (ZeroF, n) (NatLTZ n)) (zp n)

public export
NatMorphDepIndSCase :
  {p : (mn : NatObjPair) -> NatLTMorph mn -> Type} ->
  (dp : (mn : NatObjPair) -> (morph : NatLTMorph mn) -> p mn morph -> Type) ->
  (sp : NatMorphIndSCase p) ->
  Type
NatMorphDepIndSCase {p} dp sp =
  (m, n : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  (pmn : p (m, n) morph) ->
  dp (m, n) morph pmn ->
  dp
    (InNat $ SuccF m, InNat $ SuccF n)
    (InNatLT (SuccF m, SuccF n) $ NatLTS (m, n) morph)
    (sp m n morph pmn)

public export
NatMorphDepInd :
  {p : (mn : NatObjPair) -> NatLTMorph mn -> Type} ->
  (dp : (mn : NatObjPair) -> (morph : NatLTMorph mn) -> p mn morph -> Type) ->
  {zp : NatMorphIndZCase p} ->
  {sp : NatMorphIndSCase p} ->
  (dzp : NatMorphDepIndZCase dp zp) ->
  (dsp : NatMorphDepIndSCase dp sp) ->
  (mn : NatObjPair) -> (morph : NatLTMorph mn) ->
  dp mn morph (NatMorphInd p zp sp mn morph)
NatMorphDepInd {p} dp {zp} {sp} dzp dsp =
  NatMorphInd
    (\mn', morph' => dp mn' morph' (NatMorphInd p zp sp mn' morph'))
    dzp
    (\m', n', morph', dpmn' =>
      dsp m' n' morph' (NatMorphInd p zp sp (m', n') morph') dpmn')

public export
NatMorphZThin : (n : NatF NatObj) ->
  (morph : NatLTMorph (InNat ZeroF, InNat n)) ->
  InNatLT (ZeroF, n) (NatLTZ n) = morph
NatMorphZThin ZeroF morph =
  case morph of
    InNatLT _ (NatLTZ $ ZeroF) => Refl
    InNatLT _ (NatLTS (m', n') morph') impossible
NatMorphZThin (SuccF n') morph =
  case morph of
    InNatLT _ (NatLTZ $ ZeroF) impossible
    InNatLT _ (NatLTS (m', n') morph') impossible

public export
NatMorphSThin :
  (m, n : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  ((morph' : NatLTMorph (m, n)) -> morph = morph') ->
  (morph' : NatLTMorph (InNat (SuccF m), InNat (SuccF n))) ->
  InNatLT (SuccF m, SuccF n) (NatLTS (m, n) morph) = morph'
NatMorphSThin (InNat m) (InNat n) morph eq morph' = case m of
  ZeroF => case morph of
    InNatLT _ (NatLTZ m') => case morph' of
      InNatLT _ (NatLTZ $ SuccF $ InNat n') impossible
      InNatLT _ (NatLTS (InNat ZeroF, InNat n'') morphs) =>
        rewrite eq morphs in
        Refl
    InNatLT _ (NatLTS (m', n') morphs) impossible
  SuccF m' => case morph of
    InNatLT _ (NatLTZ m'') impossible
    InNatLT _ (NatLTS (m'', n'') morphs) => case morph' of
      InNatLT _ (NatLTZ $ SuccF $ InNat m''') impossible
      InNatLT _ (NatLTS (InNat $ SuccF m''', InNat $ SuccF n''') morphs') =>
        rewrite eq morphs' in
        Refl

public export
NatCatThin : (mn : NatObjPair) ->
  (morph, morph' : NatLTMorph mn) -> morph = morph'
NatCatThin =
  NatMorphInd
    (\mn, morph => (morph' : NatLTMorph mn) -> morph = morph')
    NatMorphZThin
    NatMorphSThin

public export
LTEThin : {m, n : Nat} -> (l, l' : LTE m n) -> l = l'
LTEThin LTEZero LTEZero = Refl
LTEThin LTEZero (LTESucc l) impossible
LTEThin (LTESucc l) LTEZero impossible
LTEThin (LTESucc l) (LTESucc l') = cong LTESucc (LTEThin l l')

public export
NatMorphToLTE : {mn : NatObjPair} ->
  NatLTMorph mn -> LTE (NatObjToMeta (fst mn)) (NatObjToMeta (snd mn))
NatMorphToLTE {mn=mn'} =
  NatMorphInd
    (\mn, morph => LTE (NatObjToMeta (fst mn)) (NatObjToMeta (snd mn)))
    (\n => LTEZero {right=(NatObjToMeta $ InNat n)})
    (\m, n, morph, lt => LTESucc lt)
    mn'

public export
LTEToNatMorph : {mn : NatPair} ->
  LTE (fst mn) (snd mn) -> NatLTMorph (NatMetaPairToObj mn)
LTEToNatMorph {mn=(Z, Z)} LTEZero =
  InNatLT (ZeroF, ZeroF) $ NatLTZ ZeroF
LTEToNatMorph {mn=(Z, Z)} (LTESucc _) impossible
LTEToNatMorph {mn=(Z, S n)} LTEZero =
  InNatLT (ZeroF, SuccF $ MetaToNatObj n) $ NatLTZ $ SuccF $ MetaToNatObj n
LTEToNatMorph {mn=(Z, S n)} (LTESucc _) impossible
LTEToNatMorph {mn=(S m, Z)} LTEZero impossible
LTEToNatMorph {mn=(S m, Z)} (LTESucc _) impossible
LTEToNatMorph {mn=(S m, S n)} LTEZero impossible
LTEToNatMorph {mn=(S m, S n)} (LTESucc lt) =
  InNatLT (SuccF $ MetaToNatObj m, SuccF $ MetaToNatObj n) $
    NatLTS (MetaToNatObj m, MetaToNatObj n) $
      LTEToNatMorph {mn=(m, n)} lt

public export
NatMorphCompose : {m, n, p : NatObj} ->
  NatLTMorph (n, p) ->
  NatLTMorph (m, n) ->
  NatLTMorph (m, p)
NatMorphCompose {m} {n} {p} g f =
  rewrite sym (NatToMetaId m) in
  rewrite sym (NatToMetaId p) in
  LTEToNatMorph {mn=(NatObjToMeta m, NatObjToMeta p)} $
    transitive (NatMorphToLTE f) (NatMorphToLTE g)

public export
NatLTOZ : (n : NatObj) -> NatLTMorph (NatOZ, n)
NatLTOZ (InNat n) = InNatLT (ZeroF, n) (NatLTZ n)

public export
NatLTOZ1 : NatLTMorph (NatOZ, NatO1)
NatLTOZ1 = NatLTOZ NatO1

public export
NatLTStrict : NatObj -> NatObj -> Type
NatLTStrict m n = NatLTMorph (NatOS m, n)

public export
OnlyZLtZ : (n : NatObj) -> NatLTMorph (n, NatOZ) -> n = NatOZ
OnlyZLtZ (InNat n) (InNatLT (n, ZeroF) m) = case n of
  ZeroF => Refl
  SuccF n' => let _ = OnlyZLtZ n' in case m of
    NatLTZ ZeroF impossible
    NatLTS (s, z) m' impossible

public export
OnlyZLtZMorph : (n : NatObj) -> (morph : NatLTMorph (n, NatOZ)) ->
  morph = NatLTOZ NatOZ
OnlyZLtZMorph n morph =
  rewrite OnlyZLtZ n morph in
  case morph of
    InNatLT _ (NatLTZ _) => Refl
    InNatLT _ (NatLTS (_, _) _) impossible

public export
NatMorphId : (n : NatObj) -> NatLTMorph (n, n)
NatMorphId (InNat n) = case n of
  ZeroF => InNatLT (ZeroF, ZeroF) $ NatLTZ ZeroF
  SuccF n' => InNatLT (SuccF n', SuccF n') $ NatLTS (n', n') $ NatMorphId n'

public export
NatLTSucc : (n : NatObj) -> NatLTMorph (n, NatOS n)
NatLTSucc = NatObjInd _ NatLTOZ1 $
  \n', morph => InNatLT _ $ NatLTS (n', InNat $ SuccF n') morph

public export
NatLTInc : {m, n : NatObj} -> NatLTMorph (m, n) -> NatLTMorph (m, NatOS n)
NatLTInc {n} = NatMorphCompose (NatLTSucc n)

public export
NatLTDec : {n, n' : NatObj} -> NatLTMorph (NatOS n, n') -> NatLTMorph (n, n')
NatLTDec {n} morph = NatMorphCompose morph $ NatLTSucc n

public export
NatMorphIdZ : NatLTMorph (NatOZ, NatOZ)
NatMorphIdZ = NatMorphId NatOZ

public export
NatMorphCompare : (m, n : NatObj) ->
  Either (m = n) $ Either (NatLTStrict m n) (NatLTStrict n m)
NatMorphCompare m n with (decEq (NatObjToMeta m) (NatObjToMeta n))
  NatMorphCompare m n | Yes eq = Left $ NatObjToMetaInj m n eq
  NatMorphCompare m n | No neq = Right $ case connex {rel=LTE} neq of
    Left lte => Left $
      let
        lt = lteTolt lte neq
        morph = LTEToNatMorph {mn=(S $ NatObjToMeta m, NatObjToMeta n)} lt
      in
      rewrite sym (NatToMetaId m) in
      rewrite sym (NatToMetaId n) in
      morph
    Right gte => Right $
      let
        lt = lteTolt gte $ \eq => neq $ sym eq
        morph = LTEToNatMorph {mn=(S $ NatObjToMeta n, NatObjToMeta m)} lt
      in
      rewrite sym (NatToMetaId m) in
      rewrite sym (NatToMetaId n) in
      morph

public export
NatLTFromSucc : (m, n : NatObj) -> NatLTMorph (NatOS m, NatOS n) ->
  NatLTMorph (m, n)
NatLTFromSucc _ _ (InNatLT (SuccF m, SuccF n) morph) = case morph of
  NatLTZ (SuccF n') impossible
  NatLTS (m', n') mn' => mn'

public export
FromLTZeroContra : (n : NatObj) -> NatLTMorph (NatOS n, NatOZ) -> Void
FromLTZeroContra _ = succNotLTEzero . NatMorphToLTE

public export
FromSuccContra : (n : NatObj) -> NatLTMorph (NatOS n, n) -> Void
FromSuccContra _ = succNotLTEpred . NatMorphToLTE

public export
LTcontraGTE : {m, n : NatObj} -> NatLTStrict m n -> NatLTMorph (n, m) -> Void
LTcontraGTE lt gte = FromSuccContra _ $ NatMorphCompose gte lt

public export
MorphToStrict : {m, n : NatObj} ->
  NatLTMorph (m, n) -> Either (m = n) (NatLTStrict m n)
MorphToStrict {m} {n} morph with (NatMorphCompare m n)
  MorphToStrict {m} {n} morph | Left eq = Left eq
  MorphToStrict {m} {n} morph | Right (Left lt) = Right lt
  MorphToStrict {m} {n} morph | Right (Right gt) = void $ LTcontraGTE gt morph

public export
NatMorphDec : (m, n : NatObj) ->
  Either (m = n) $ Either (NatLTMorph (m, n)) (NatLTMorph (n, m))
NatMorphDec m n = case NatMorphCompare m n of
  Left eq => Left eq
  Right morph => Right $ bimap {f=Either} NatLTDec NatLTDec morph

public export
NatMorphMaybe : (m, n : NatObj) -> Maybe (NatLTMorph (m, n))
NatMorphMaybe m n = case NatMorphDec m n of
  Left _ => Nothing
  Right e => case e of
    Left morph => Just morph
    Right _ => Nothing

public export
NatLTEDec : (m, n : NatObj) -> Either (NatLTMorph (m, n)) (NatLTStrict n m)
NatLTEDec m n = case NatMorphCompare m n of
  Left eq => rewrite eq in Left $ NatMorphId _
  Right morph => case morph of
    Left lt => Left $ NatLTDec lt
    Right gt => Right gt

public export
NatStrictLTDec : (m, n : NatObj) -> Either (NatLTStrict m n) (NatLTMorph (n, m))
NatStrictLTDec m n = case NatMorphCompare m n of
  Left eq => rewrite eq in Right $ NatMorphId _
  Right morph => case morph of
    Left lt => Left lt
    Right gt => Right $ NatLTDec gt

public export
NatLTStrictMaybe : (m, n : NatObj) -> Maybe (NatLTStrict m n)
NatLTStrictMaybe m n = case NatStrictLTDec m n of
  Left morph => Just morph
  Right _ => Nothing

public export
NatMorphDecSucc : (m, n : NatObj) ->
  Either (m = n) $
    Either (NatLTMorph (NatOS m, NatOS n)) (NatLTMorph (NatOS n, NatOS m))
NatMorphDecSucc m n = case NatMorphDec m n of
  Left eq =>
    Left eq
  Right morph =>
    Right $ bimap {f=Either} NatLTMorphToSucc NatLTMorphToSucc morph

public export
NatMorphSucc : (m, n : NatObj) -> NatLTMorph (m, NatOS n) ->
  Either (NatLTMorph (m, n)) (m = NatOS n)
NatMorphSucc m n morph =
  case NatMorphCompare m (NatOS n) of
    Left eq => Right eq
    Right (Left lt) => Left $ NatLTFromSucc m n lt
    Right (Right gt) =>
      void $ FromSuccContra n $ NatLTFromSucc _ _ $ NatMorphCompose morph gt

---------------------------------------------------
---- Colimit/initial algebra utility functions ----
---------------------------------------------------

public export
colimitInj :
  {f : Type -> Type} -> Functor f =>
  InitialColimit f -> InitialColimit f
colimitInj (n ** f') = (NatOS n ** OmegaInj f')

public export
colimitConst : {f : Type -> Type} -> Functor f =>
  (one : f Void) -> InitialColimit f
colimitConst one = (NatO1 ** OmegaIter one)

public export
colimitOne :
  {f : Type -> Type} -> Functor f =>
  (succ : {n : NatObj} -> InitialChain f n -> f (InitialChain f n)) ->
  InitialColimit f -> InitialColimit f
colimitOne succ (n ** f') = (NatOS n ** OmegaIter $ succ f')

public export
OmegaChainCompose : {f : Type -> Type} -> {a : Type} -> {n, n' : NatObj} ->
  Functor f => NatLTMorph (n, n') -> OmegaChain f n a -> OmegaChain f n' a
OmegaChainCompose {f} {n} {n'} =
  NatMorphInd
    (\mn, _ => OmegaChain f (fst mn) a -> OmegaChain f (snd mn) a)
    (\k => OmegaInjN {f} {a} (InNat k))
    (\_, _, _ => map {f=(OmegaStep f)})
    (n, n')

public export
colimitPair :
  {f : Type -> Type} -> Functor f =>
  (combine : {n : NatObj} ->
    InitialChain f n -> InitialChain f n -> f (InitialChain f n)) ->
  InitialColimit f -> InitialColimit f -> InitialColimit f
colimitPair combine (m ** f') (n ** g') =
  case NatMorphDec m n of
    Left eq => (NatOS m ** case eq of Refl => OmegaIter $ combine f' g')
    Right morph => case morph of
      Left ltmn =>
        (NatOS n ** OmegaIter $ combine (OmegaChainCompose ltmn f') g')
      Right ltnm =>
        (NatOS m ** OmegaIter $ combine f' (OmegaChainCompose ltnm g'))

------------------------------
---- Slices and morphisms ----
------------------------------

public export
ltSliceObjToNatMorphStep :
  (n : NatObj) ->
  ((slice : NatLTSlice n) -> NatLTMorph (ltSliceObjToNat {n} slice, n)) ->
  (slice : NatLTSlice (NatOS n)) ->
  NatLTMorph (ltSliceObjToNat {n=(NatOS n)} slice, NatOS n)
ltSliceObjToNatMorphStep n step (Left ()) = NatLTOZ $ NatOS n
ltSliceObjToNatMorphStep n step (Right n') = NatLTMorphToSucc $ step n'

public export
ltSliceObjToNatMorph : (n : NatObj) ->
  (slice : NatLTSlice n) -> NatLTMorph (ltSliceObjToNat {n} slice, n)
ltSliceObjToNatMorph =
  FunctorIterInd _ (const NatMorphIdZ) ltSliceObjToNatMorphStep

public export
natMorphToLTSlice : {m, n : NatObj} -> NatLTMorph (m, n) -> NatLTSlice n
natMorphToLTSlice {m} {n} =
  NatMorphInd
    (\mn, _ => NatLTSlice (snd mn))
    (\n' => case n' of
      ZeroF => ()
      SuccF n'' => Left ())
    (\m', n', morph, slice => if isLTZ morph then Left () else Right slice)
    (m, n)

----------------------------------------------
---- Slices (prefixes) of natural numbers ----
----------------------------------------------

public export
NatOPrefix : NatObj -> Type
NatOPrefix n = (m : NatObj ** NatLTStrict m n)

public export
NatOPrefixMaybe : {n : NatObj} -> NatObj -> Maybe (NatOPrefix n)
NatOPrefixMaybe {n} m = case NatLTStrictMaybe m n of
  Just lt => Just (m ** lt)
  Nothing => Nothing

public export
InitNatOPrefix :
  {n : NatObj} -> (m : NatObj) ->
  {auto ok : IsJustTrue (NatOPrefixMaybe {n} m)} ->
  NatOPrefix n
InitNatOPrefix _ {ok} = fromIsJust ok

public export
NatOPrefixZ : (n : NatObj) -> NatOPrefix (NatOS n)
NatOPrefixZ n = (NatOZ ** NatLTMorphToSucc $ NatLTOZ n)

public export
NatOSlice : NatObj -> Type
NatOSlice n = (m : NatObj ** NatLTMorph (m, n))

public export
NatOSliceMaybe : {n : NatObj} -> NatObj -> Maybe (NatOSlice n)
NatOSliceMaybe {n} m = case NatMorphMaybe m n of
  Just lt => Just (m ** lt)
  Nothing => Nothing

public export
InitNatOSlice :
  {n : NatObj} -> (m : NatObj) ->
  {auto ok : isJust (NatOSliceMaybe {n} m) = True} ->
  NatOSlice n
InitNatOSlice _ {ok} = fromIsJust ok

public export
NatZSlice : Type
NatZSlice = NatOSlice NatOZ

public export
NatOSliceZ : (n : NatObj) -> NatOSlice n
NatOSliceZ n = (NatOZ ** NatLTOZ n)

public export
NatOSliceMax : (n : NatObj) -> NatOSlice n
NatOSliceMax n = (n ** NatMorphId n)

public export
NatZSliceSingleton : (sl : NatZSlice) -> sl = NatOSliceZ NatOZ
NatZSliceSingleton (m ** morph) =
  case OnlyZLtZ m morph of Refl => rewrite OnlyZLtZMorph m morph in Refl

public export
NatOSliceIndBaseCase : ((n : NatObj) -> NatOSlice n -> Type) -> Type
NatOSliceIndBaseCase p = p NatOZ (NatOSliceZ NatOZ)

public export
NatOSliceInductionStep : ((n : NatObj) -> NatOSlice n -> Type) -> Type
NatOSliceInductionStep p =
  (n : NatObj) ->
  ((sl : NatOSlice n) -> p n sl) ->
  (sl : NatOSlice (NatOS n)) -> p (NatOS n) sl

public export
NatOSliceInduction :
  (p : (n : NatObj) -> NatOSlice n -> Type) ->
  NatOSliceIndBaseCase p ->
  NatOSliceInductionStep p ->
  (n : NatObj) -> (sl : NatOSlice n) -> p n sl
NatOSliceInduction p z =
  NatObjInd
    (\n => (sl : NatOSlice n) -> p n sl)
    (\sl => replace {p=(p NatOZ)} (sym (NatZSliceSingleton sl)) z)

public export
NatOSliceDepIndBaseCase :
  {p : (n : NatObj) -> NatOSlice n -> Type} ->
  ((n : NatObj) -> (sl : NatOSlice n) -> p n sl -> Type) ->
  NatOSliceIndBaseCase p ->
  Type
NatOSliceDepIndBaseCase {p} dp z = dp NatOZ (NatOSliceZ NatOZ) z

public export
NatOSliceDepInductionStep :
  {p : (n : NatObj) -> NatOSlice n -> Type} ->
  ((n : NatObj) -> (sl : NatOSlice n) -> p n sl -> Type) ->
  NatOSliceInductionStep p ->
  Type
NatOSliceDepInductionStep {p} dp s =
  (n : NatObj) ->
  (hyp : (sl : NatOSlice n) -> p n sl) ->
  (dephyp : (sl : NatOSlice n) -> dp n sl (hyp sl)) ->
  (sl : NatOSlice (NatOS n)) ->
  dp (NatOS n) sl (s n hyp sl)

public export
NatOSliceDepInduction :
  {p : (n : NatObj) -> NatOSlice n -> Type} ->
  (dp : (n : NatObj) -> (sl : NatOSlice n) -> p n sl -> Type) ->
  {z : NatOSliceIndBaseCase p} ->
  {s : NatOSliceInductionStep p} ->
  NatOSliceDepIndBaseCase dp z ->
  NatOSliceDepInductionStep dp s ->
  (n : NatObj) -> (sl : NatOSlice n) -> dp n sl (NatOSliceInduction p z s n sl)
NatOSliceDepInduction {p} dp {z} {s} dz ds =
  NatOSliceInduction
    (\n, sl => dp n sl (NatOSliceInduction p z s n sl))
    dz
    (\n => ds n (NatOSliceInduction p z s n))

public export
(n : NatObj) => DecEq (NatOSlice n) where
  decEq {n} (m ** morph) (m' ** morph') with (decEq m m')
    decEq {n} (m ** morph) (m' ** morph') | Yes eq = Yes $
      case eq of Refl => rewrite NatCatThin _ morph morph' in Refl
    decEq {n} (m ** morph) (m' ** morph') | No neq = No $ \eq =>
      case eq of Refl => neq Refl

public export
(n : NatObj) => Eq (NatOSlice n) where
  m == m' = case decEq m m' of
    Yes _ => True
    No _ => False

public export
NatObjBoundedGenIndMorph : {n : NatObj} -> {0 a : NatOSlice n -> Type} ->
  a (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) -> a (m ** NatLTDec morph) ->
    a (NatOS m ** morph)) ->
  (n' : NatObj) -> (morph : NatLTMorph (n', n)) -> a (n' ** morph)
NatObjBoundedGenIndMorph {n} {a} i f =
  NatObjInd
    (\n' => (morph : NatLTMorph (n', n)) -> a (n' ** morph))
    (\morph' => rewrite NatCatThin _ morph' (NatLTOZ n) in i)
    (\n', hyp, morph => f n' morph $ hyp $ NatLTDec morph)

public export
NatObjBoundedGenInd : {n : NatObj} -> {0 a : NatOSlice n -> Type} ->
  a (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) -> a (m ** NatLTDec morph) ->
    a (NatOS m ** morph)) ->
  (m : NatOSlice n) -> a m
NatObjBoundedGenInd {a} i f (n' ** morph) =
  NatObjBoundedGenIndMorph {a} i f n' morph

public export
NatObjBoundedInd : {n : NatObj} -> {a : NatOSlice n -> Type} ->
  a (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) -> a (m ** NatLTDec morph) ->
    a (NatOS m ** morph)) ->
  a (NatOSliceMax n)
NatObjBoundedInd {n} {a} i f = NatObjBoundedGenInd {a} i f (NatOSliceMax n)

public export
NatOSliceFromSucc : {n : NatObj} ->
  (m : NatObj ** NatLTMorph (NatOS m, NatOS n)) -> NatOSlice n
NatOSliceFromSucc {n} (m ** morph) = (m ** NatLTFromSucc m n morph)

public export
NatOSliceSuccElimMorph : {n : NatObj} ->
  {a : NatOSlice n -> Type} ->
  ((sl : (m : NatObj ** NatLTMorph (NatOS m, NatOS n))) ->
    a (fst sl ** NatLTFromSucc _ _ $ snd sl)) ->
  (m : NatObj) -> (morph : NatLTMorph (m, n)) -> a (m ** morph)
NatOSliceSuccElimMorph {n} {a} f m morph = f (m ** NatLTMorphToSucc morph)

public export
NatOSliceSuccElim : {n : NatObj} ->
  {a : NatOSlice n -> Type} ->
  ((sl : (m : NatObj ** NatLTMorph (NatOS m, NatOS n))) ->
    a (fst sl ** NatLTFromSucc _ _ $ snd sl)) ->
  (m : NatOSlice n) -> a m
NatOSliceSuccElim {a} f (m ** morph) = NatOSliceSuccElimMorph {a} f m morph

public export
NatObjBoundedGenMap :
  {n : NatObj} ->
  {a, b : NatOSlice n -> Type} ->
  (m : ((sl : NatOSlice n) -> a sl -> b sl)) ->
  ((sl : NatOSlice n) -> a sl) ->
  ((sl : NatOSlice n) -> b sl)
NatObjBoundedGenMap {n} m g sl = m sl $ g sl

public export
NatObjBoundedMap :
  {n : NatObj} ->
  {a, b : NatOSlice n -> Type} ->
  (m : ((sl : NatOSlice n) -> a sl -> b sl)) ->
  ((sl : NatOSlice n) -> a sl) ->
  b (NatOSliceMax n)
NatObjBoundedMap {a} {b} {n} m g =
  NatObjBoundedGenMap {a} {b} {n} m g $ NatOSliceMax n

public export
NatObjBoundedGenFold :
  {n : NatObj} ->
  {a : NatOSlice n -> Type} ->
  {b : NatOSlice (NatOS n) -> Type} ->
  ((sl : NatOSlice n) -> a sl) ->
  b (NatOSliceZ $ NatOS n) ->
  ((m : NatObj) -> (morph : NatLTMorph (m, n)) ->
   a (m ** morph) ->
   b (m ** NatLTInc morph) ->
   b (NatOS m ** NatLTMorphToSucc morph)) ->
  (m : NatOSlice (NatOS n)) -> b m
NatObjBoundedGenFold {a} {b} {n} ga z s =
  NatObjBoundedGenInd {a=b}
    z
    (\n', morph, b' =>
      let morph' = NatLTFromSucc _ _ morph in
      rewrite NatCatThin _ morph (NatLTMorphToSucc morph') in
      s n' morph'
        (ga (n' ** morph'))
        (rewrite NatCatThin (n', NatOS n) (NatLTInc morph') _ in b'))

public export
NatObjBoundedFold :
  {n : NatObj} ->
  {a : NatOSlice n -> Type} ->
  {b : NatOSlice (NatOS n) -> Type} ->
  ((sl : NatOSlice n) -> a sl) ->
  b (NatOSliceZ $ NatOS n) ->
  ((m : NatObj) -> (morph : NatLTMorph (m, n)) ->
   a (m ** morph) ->
   b (m ** NatLTInc morph) ->
   b (NatOS m ** NatLTMorphToSucc morph)) ->
  b (NatOSliceMax (NatOS n))
NatObjBoundedFold {n} {a} {b} ga z s =
  NatObjBoundedGenFold {a} {b} ga z s (NatOSliceMax (NatOS n))

public export
NatObjBoundedGenMapFold :
  {n : NatObj} ->
  {a, b : NatOSlice n -> Type} ->
  {c : NatOSlice (NatOS n) -> Type} ->
  (m : ((sl : NatOSlice n) -> a sl -> b sl)) ->
  ((sl : NatOSlice n) -> a sl) ->
  c (NatOSliceZ $ NatOS n) ->
  ((m : NatObj) -> (morph : NatLTMorph (m, n)) ->
   b (m ** morph) ->
   c (m ** NatLTInc morph) ->
   c (NatOS m ** NatLTMorphToSucc morph)) ->
  (m : NatOSlice (NatOS n)) -> c m
NatObjBoundedGenMapFold {a} {b} {c} {n} mab ga =
  NatObjBoundedGenFold {a=b} {b=c} $ NatObjBoundedGenMap {a} {b} mab ga

public export
NatObjBoundedMapFold :
  {n : NatObj} ->
  {a, b : NatOSlice n -> Type} ->
  {c : NatOSlice (NatOS n) -> Type} ->
  (m : ((sl : NatOSlice n) -> a sl -> b sl)) ->
  ((sl : NatOSlice n) -> a sl) ->
  c (NatOSliceZ $ NatOS n) ->
  ((m : NatObj) -> (morph : NatLTMorph (m, n)) ->
   b (m ** morph) ->
   c (m ** NatLTInc morph) ->
   c (NatOS m ** NatLTMorphToSucc morph)) ->
  c (NatOSliceMax (NatOS n))
NatObjBoundedMapFold {a} {b} {c} {n} mab ga z s =
  NatObjBoundedGenMapFold {a} {b} {c} {n} mab ga z s (NatOSliceMax (NatOS n))

public export
NatObjPrefixGenMap :
  {n : NatObj} ->
  {0 a, b : NatOPrefix n -> Type} ->
  (m : ((sl : NatOPrefix n) -> a sl -> b sl)) ->
  ((sl : NatOPrefix n) -> a sl) ->
  ((sl : NatOPrefix n) -> b sl)
NatObjPrefixGenMap {n} m g sl = m sl $ g sl

public export
NatObjPrefixGenFold :
  {n : NatObj} ->
  {0 a : NatOPrefix n -> Type} ->
  {0 b : NatOSlice n -> Type} ->
  ((sl : NatOPrefix n) -> a sl) ->
  b (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) ->
   a (m ** morph) -> b (m ** NatLTDec morph) -> b ((NatOS m) ** morph)) ->
  (sl : NatOSlice n) -> b sl
NatObjPrefixGenFold {a} {b} {n} ga z s =
  NatObjBoundedGenInd {a=b}
    z
    (\n', morph, b' => s n' morph (ga (n' ** morph)) b')

public export
NatObjPrefixFold :
  {n : NatObj} ->
  {0 a : NatOPrefix n -> Type} ->
  {0 b : NatOSlice n -> Type} ->
  ((sl : NatOPrefix n) -> a sl) ->
  b (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) ->
   a (m ** morph) -> b (m ** NatLTDec morph) -> b ((NatOS m) ** morph)) ->
  b (NatOSliceMax n)
NatObjPrefixFold {a} {b} {n} ga z s =
  NatObjPrefixGenFold {a} {b} {n} ga z s (NatOSliceMax n)

public export
NatObjPrefixGenMapFold :
  {n : NatObj} ->
  {0 a, b : NatOPrefix n -> Type} ->
  {0 c : NatOSlice n -> Type} ->
  (m : ((sl : NatOPrefix n) -> a sl -> b sl)) ->
  ((sl : NatOPrefix n) -> a sl) ->
  c (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) ->
   b (m ** morph) -> c (m ** NatLTDec morph) -> c ((NatOS m) ** morph)) ->
  (sl : NatOSlice n) -> c sl
NatObjPrefixGenMapFold {a} {b} {c} {n} m ga =
  NatObjPrefixGenFold {a=b} {b=c} $ NatObjPrefixGenMap {a} {b} m ga

public export
NatObjPrefixMapFold :
  {n : NatObj} ->
  {0 a, b : NatOPrefix n -> Type} ->
  {0 c : NatOSlice n -> Type} ->
  (m : ((sl : NatOPrefix n) -> a sl -> b sl)) ->
  ((sl : NatOPrefix n) -> a sl) ->
  c (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) ->
   b (m ** morph) -> c (m ** NatLTDec morph) -> c ((NatOS m) ** morph)) ->
  c (NatOSliceMax n)
NatObjPrefixMapFold {a} {b} {c} {n} mab ga z s =
  NatObjPrefixGenMapFold {a} {b} {c} {n} mab ga z s (NatOSliceMax n)

---------------------------
---- General induction ----
---------------------------

public export
ForallLTE : (NatObj -> Type) -> NatObj -> Type
ForallLTE p n = (sl : NatOSlice n) -> p (fst sl)

public export
NatObjGenInductionStep : (NatObj -> Type) -> Type
NatObjGenInductionStep p = (n' : NatObj) -> ForallLTE p n' -> p (NatOS n')

public export
NatObjGenIndStrengthenedStep :
  (p : NatObj -> Type) ->
  NatObjGenInductionStep p ->
  (n : NatObj) ->
  ForallLTE p n ->
  ForallLTE p (NatOS n)
NatObjGenIndStrengthenedStep p s n hyp (n' ** m) =
  case NatMorphSucc n' n m of
    Left m' => hyp (n' ** m')
    Right eqn => rewrite eqn in s n hyp

public export
NatObjGenIndStrengthened :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatObjGenInductionStep p ->
  (n : NatObj) -> ForallLTE p n
NatObjGenIndStrengthened p z s =
  NatOSliceInduction
    (\n, sl => p (fst sl))
    z
    (NatObjGenIndStrengthenedStep p s)

public export
NatObjGenInd :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatObjGenInductionStep p ->
  (n : NatObj) -> p n
NatObjGenInd p z s n = NatObjGenIndStrengthened p z s n (NatOSliceMax n)

public export
ForallLTEDep : {p : NatObj -> Type} ->
  ((n : NatObj) -> p n -> Type) ->
  (n : NatObj) -> ForallLTE p n -> Type
ForallLTEDep {p} dp n ps = (sl : NatOSlice n) -> dp (fst sl) (ps sl)

public export
NatObjDepGenInductionStep :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  (sp : NatObjGenInductionStep p) ->
  Type
NatObjDepGenInductionStep {p} dp sp =
  (n' : NatObj) -> (pn : ForallLTE p n') -> ForallLTEDep dp n' pn ->
  dp (NatOS n') (sp n' pn)

public export
NatObjDepGenIndStrengthenedStep :
  (p : NatObj -> Type) ->
  (dp : (n : NatObj) -> p n -> Type) ->
  (sp : NatObjGenInductionStep p) ->
  NatObjDepGenInductionStep dp sp ->
  (n : NatObj) ->
  (hyp : ForallLTE p n) ->
  (dh : ForallLTEDep dp n hyp) ->
  (sl : NatOSlice (NatOS n)) ->
  dp (fst sl) (NatObjGenIndStrengthenedStep p sp n hyp sl)
NatObjDepGenIndStrengthenedStep p dp sp dsp n hyp dh (n' ** m)
  with (NatMorphSucc n' n m)
    NatObjDepGenIndStrengthenedStep p dp sp dsp n hyp dh (n' ** m) | Left m' =
      dh (n' ** m')
    NatObjDepGenIndStrengthenedStep p dp sp dsp n hyp dh (n' ** m) | Right eqn =
      rewrite eqn in
      dsp n hyp dh

public export
NatObjDepGenIndStrengthened :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  {zp : NatObjIndBaseCase p} ->
  {sp : NatObjGenInductionStep p} ->
  NatObjDepIndBaseCase dp zp ->
  NatObjDepGenInductionStep dp sp ->
  (n : NatObj) -> ForallLTEDep dp n (NatObjGenIndStrengthened p zp sp n)
NatObjDepGenIndStrengthened {p} dp {zp} {sp} dzp dsp =
  NatOSliceDepInduction
    {p=(\n, sl => p (fst sl))}
    (\n, sl, ps => dp (fst sl) ps)
    {z=zp}
    {s=(NatObjGenIndStrengthenedStep p sp)}
    dzp
    (NatObjDepGenIndStrengthenedStep p dp sp dsp)

public export
NatObjDepGenInd :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  {zp : NatObjIndBaseCase p} ->
  {sp : NatObjGenInductionStep p} ->
  NatObjDepIndBaseCase dp zp ->
  NatObjDepGenInductionStep dp sp ->
  (n : NatObj) -> dp n (NatObjGenInd p zp sp n)
NatObjDepGenInd {p} dp {zp} {sp} dzp dsp n =
  NatObjDepGenIndStrengthened {p} dp {zp} {sp} dzp dsp n (NatOSliceMax n)

public export
FunctorIterLTE : {f : Type -> Type} -> {a : Type} ->
  ((n : NatObj) -> FunctorIter f n a -> Type) -> NatObj -> Type
FunctorIterLTE {f} {a} p n =
  (sl : NatOSlice n) -> (ty : FunctorIter f (fst sl) a) -> p (fst sl) ty

public export
FunctorIterGenIndStep : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> FunctorIter f n' a -> Type) -> Type
FunctorIterGenIndStep {f} {a} p =
  (n' : NatObj) ->
  FunctorIterLTE p n' ->
  (ty : FunctorIter f (NatOS n') a) ->
  p (NatOS n') ty

public export
FunctorIterGenInd : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> FunctorIter f n' a -> Type) ->
  FunctorIterIndBaseCase {f} {a} p ->
  FunctorIterGenIndStep {f} {a} p ->
  (n : NatObj) -> (ty : FunctorIter f n a) -> p n ty
FunctorIterGenInd {f} {a} p =
  NatObjGenInd (\n' => (ty : FunctorIter f n' a) -> p n' ty)

public export
FunctorIterLTEDep : {f : Type -> Type} -> {a : Type} ->
  {p : (n : NatObj) -> FunctorIter f n a -> Type} ->
  (dp : (n : NatObj) -> (ty : FunctorIter f n a) -> p n ty -> Type) ->
  (n : NatObj) -> FunctorIterLTE {f} {a} p n -> Type
FunctorIterLTEDep {f} {a} {p} dp n lte =
  (sl : NatOSlice n) ->
  (ty : FunctorIter f (fst sl) a) ->
  dp (fst sl) ty (lte sl ty)

public export
FunctorIterDepGenInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  ((n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  FunctorIterGenIndStep {f} {a} p ->
  Type
FunctorIterDepGenInductionStep {f} {a} {p} dp sp =
  (n' : NatObj) ->
  (pty : FunctorIterLTE p n') ->
  (dephyp : FunctorIterLTEDep dp n' pty) ->
  ((ty : f (FunctorIter f n' a)) -> dp (NatOS n') ty (sp n' pty ty))

public export
FunctorIterDepGenInd : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  (dp : (n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  {zp : FunctorIterIndBaseCase {f} {a} p} ->
  {sp : FunctorIterGenIndStep {f} {a} p} ->
  FunctorIterDepIndBaseCase {f} {a} {p} dp zp ->
  FunctorIterDepGenInductionStep {f} {a} {p} dp sp ->
  (n : NatObj) -> (ty : FunctorIter f n a) ->
  dp n ty (FunctorIterGenInd {f} {a} p zp sp n ty)
FunctorIterDepGenInd {f} {a} {p} dp =
  NatObjDepGenInd
    {p=(\n' => (ty : FunctorIter f n' a) -> p n' ty)}
    (\n', hyp' => (ty : FunctorIter f n' a) -> dp n' ty (hyp' ty))

public export
ChainLTE : {f : Type -> Type} -> {a : Type} ->
  ((n : NatObj) -> OmegaChain f n a -> Type) -> NatObj -> Type
ChainLTE {f} {a} p n =
  (sl : NatOSlice n) -> (ty : OmegaChain f (fst sl) a) -> p (fst sl) ty

public export
ChainGenIndStep : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> OmegaChain f n' a -> Type) -> Type
ChainGenIndStep {f} = FunctorIterGenIndStep {f=(OmegaStep f)}

public export
ChainGenInd : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> OmegaChain f n' a -> Type) ->
  ChainIndBaseCase {f} {a} p ->
  ChainGenIndStep {f} {a} p ->
  (n : NatObj) -> (ty : OmegaChain f n a) -> p n ty
ChainGenInd {f} = FunctorIterGenInd {f=(OmegaStep f)}

public export
ChainLTEDep : {f : Type -> Type} -> {a : Type} ->
  {p : (n : NatObj) -> OmegaChain f n a -> Type} ->
  (dp : (n : NatObj) -> (ty : OmegaChain f n a) -> p n ty -> Type) ->
  (n : NatObj) -> ChainLTE {f} {a} p n -> Type
ChainLTEDep {f} {a} {p} dp n lte =
  (sl : NatOSlice n) ->
  (ty : OmegaChain f (fst sl) a) ->
  dp (fst sl) ty (lte sl ty)

public export
ChainDepGenInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  ((n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  ChainGenIndStep {f} {a} p ->
  Type
ChainDepGenInductionStep {f} {a} {p} dp sp =
  (n' : NatObj) ->
  (pty : ChainLTE p n') ->
  (dephyp : ChainLTEDep dp n' pty) ->
  ((ty : OmegaStep f (OmegaChain f n' a)) -> dp (NatOS n') ty (sp n' pty ty))

public export
ChainDepGenInd : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  (dp : (n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  {zp : ChainIndBaseCase {f} {a} p} ->
  {sp : ChainGenIndStep {f} {a} p} ->
  ChainDepIndBaseCase {f} {a} {p} dp zp ->
  ChainDepGenInductionStep {f} {a} {p} dp sp ->
  (n : NatObj) -> (ty : OmegaChain f n a) ->
  dp n ty (ChainGenInd {f} {a} p zp sp n ty)
ChainDepGenInd {f} = FunctorIterDepGenInd {f=(OmegaStep f)}

public export
ColimitGenIndStep : {f : Type -> Type} -> {a : Type} ->
  (p : OmegaColimit f a -> Type) -> Type
ColimitGenIndStep = ChainGenIndStep . PredColimitToChain

public export
ColimitGenInd : {f : Type -> Type} -> {a : Type} ->
  (p : OmegaColimit f a -> Type) ->
  ColimitIndBaseCase {f} {a} p ->
  ColimitGenIndStep {f} {a} p ->
  (c : OmegaColimit f a) -> p c
ColimitGenInd p zp sp (n ** c) = ChainGenInd (PredColimitToChain p) zp sp n c

public export
ColimitDepGenInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  ((c : OmegaColimit f a) -> p c -> Type) ->
  ColimitGenIndStep {f} {a} p ->
  Type
ColimitDepGenInductionStep = ChainDepGenInductionStep . DepPredColimitToChain

public export
ColimitDepGenInd : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  (dp : (c : OmegaColimit f a) -> p c -> Type) ->
  {zp : ColimitIndBaseCase {f} {a} p} ->
  {sp : ColimitGenIndStep {f} {a} p} ->
  ColimitDepIndBaseCase {f} {a} {p} dp zp ->
  ColimitDepGenInductionStep {f} {a} {p} dp sp ->
  (c : OmegaColimit f a) ->
  dp c (ColimitGenInd {f} {a} p zp sp c)
ColimitDepGenInd {p} dp {zp} {sp} dzp dsp (n ** c) =
  ChainDepGenInd
    {p=(PredColimitToChain p)}
    (DepPredColimitToChain dp)
    {zp} {sp} dzp dsp n c

--------------------
---- Arithmetic ----
--------------------

public export
PrefixArray : NatObj -> Type -> Type
PrefixArray n ty = NatOPrefix n -> ty

public export
SliceArray : NatObj -> Type -> Type
SliceArray n ty = NatOSlice n -> ty

public export
prefixArrayFromSlice : {a : Type} -> {n : NatObj} ->
  SliceArray n a -> PrefixArray (NatOS n) a
prefixArrayFromSlice {n} v (m ** morph) = v (m ** NatLTFromSucc m n morph)

public export
prefixArrayFromList : {a : Type} ->
  (l : List a) -> PrefixArray (MetaToNatObj (length l)) a
prefixArrayFromList [] (m ** morph) = void $ FromLTZeroContra m morph
prefixArrayFromList (x :: xs) (m ** morph) = case m of
  InNat ZeroF => x
  InNat (SuccF m') => prefixArrayFromList xs (m' ** NatLTFromSucc _ _ morph)

public export
sliceArrayFromList : {a : Type} ->
  (i : a) -> (l : List a) -> SliceArray (MetaToNatObj (length l)) a
sliceArrayFromList i l (m ** morph) = case m of
  InNat ZeroF => i
  InNat (SuccF m') => prefixArrayFromList l (m' ** morph)

public export
prefixArrayStringFold : {n : NatObj} -> {0 a : Type} ->
  (a -> String) -> PrefixArray n a -> String
prefixArrayStringFold {n} {a} sa v =
  NatObjPrefixMapFold {a=(const a)} {b=(const String)} {c=(const String)}
    (const sa)
    v
    "[empty]"
    (\n', morph, ss, sc =>
      let sc' = if n' == NatOZ then "" else sc ++ "; " in
      sc' ++ "val[" ++ show n' ++ "]=" ++ ss)

public export
showPrefixArrayArray : {m, n : NatObj} -> {0 a : Type} ->
  (a -> String) -> PrefixArray m (PrefixArray n a) -> String
showPrefixArrayArray = prefixArrayStringFold . prefixArrayStringFold

public export
PrefixArrayTruncate : {m : NatObj} -> {0 a : Type} ->
  PrefixArray (NatOS m) a -> PrefixArray m a
PrefixArrayTruncate arr (m ** morph) = arr (m ** NatLTInc morph)

public export
PrefixArrayTruncateEq : {m : NatObj} -> {0 a : Type} ->
  (arr : PrefixArray (NatOS m) a) ->
  (n : NatObj) ->
  (morph : NatLTStrict n m) ->
  (morph' : NatLTStrict n (NatOS m)) ->
  PrefixArrayTruncate arr (n ** morph) = arr (n ** morph')
PrefixArrayTruncateEq arr n morph morph' =
  rewrite NatCatThin _ morph' _ in Refl

public export
PrefixMap : NatObj -> NatObj -> Type
PrefixMap m n = NatOPrefix m -> NatOPrefix n

public export
MetaPrefixMap : Nat -> Nat -> Type
MetaPrefixMap m n = PrefixMap (MetaToNatObj m) (MetaToNatObj n)

public export
showPrefixMap : {m, n : NatObj} ->
  (NatOPrefix m -> NatOPrefix n) -> String
showPrefixMap = prefixArrayStringFold (show . fst)

public export
PrefixMapTruncate : {m, n : NatObj} ->
  PrefixMap (NatOS m) n -> PrefixMap m n
PrefixMapTruncate arr (m ** morph) = arr (m ** NatLTInc morph)

public export
PrefixMapTruncateEq : {m, n : NatObj} ->
  (pm : PrefixMap (NatOS m) n) ->
  (k : NatObj) ->
  (morph : NatLTStrict k m) ->
  (morph' : NatLTStrict k (NatOS m)) ->
  PrefixMapTruncate pm (k ** morph) = pm (k ** morph')
PrefixMapTruncateEq pm k morph morph' =
  rewrite NatCatThin _ morph' _ in Refl

public export
sliceArrayStringFold : {n : NatObj} -> {a : Type} ->
  (a -> String) -> SliceArray n a -> String
sliceArrayStringFold {n} {a} sa v =
  prefixArrayStringFold sa $ prefixArrayFromSlice {n} v

public export
(n : NatObj) => (a : Type) => Show a => Show (PrefixArray n a) where
  show {n} {a} = prefixArrayStringFold show

public export
(n : NatObj) => (a : Type) => Show a => Show (SliceArray n a) where
  show {n} {a} = sliceArrayStringFold show

public export
PrefixArrayConst : {n : NatObj} -> {a : Type} -> (x : a) -> PrefixArray n a
PrefixArrayConst x _ = x

public export
SliceArrayConst : {n : NatObj} -> {a : Type} -> (x : a) -> SliceArray n a
SliceArrayConst x _ = x

public export
natObjSum : NatObj -> NatObj -> NatObj
natObjSum =
  NatObjInd
    (const $ NatObj -> NatObj)
    id
    (const $ (.) NatOS)

public export
natObjMinus : {m, n : NatObj} -> NatLTMorph (n, m) -> NatObj
natObjMinus {m} {n} =
  NatMorphInd
    (\_, _ => NatObj)
    InNat
    (\_, _, _ => id)
    (n, m)

public export
natObjMinusLt : {m, n, k : NatObj} ->
  (lte : NatLTMorph (m, k)) ->
  NatLTStrict k (natObjSum m n) -> NatLTStrict (natObjMinus lte) n
natObjMinusLt {m} {n} {k} =
  NatMorphInd
    (\mk, morph => case mk of
      (m', k') =>
        NatLTStrict k' (natObjSum m' n) ->
        NatLTStrict (natObjMinus {m=k'} {n=m'} morph) n)
    (\n', morph' => morph')
    (\m', n', morph', hyp, lte' => hyp $ NatLTFromSucc _ _ lte')
    (m, k)

public export
natObjMul : NatObj -> NatObj -> NatObj
natObjMul =
  NatObjInd
    (const $ NatObj -> NatObj)
    (const NatOZ)
    (\pred, mulbypred, n => natObjSum (mulbypred n) n)

public export
natObjRaiseTo : NatObj -> NatObj -> NatObj
natObjRaiseTo =
  NatObjInd
    (const $ NatObj -> NatObj)
    (const NatO1)
    (\pred, raisetopred, n => natObjMul (raisetopred n) n)

public export
natObjPow : NatObj -> NatObj -> NatObj
natObjPow = flip natObjRaiseTo

public export
NatPrefixReplicate : {a : Type} -> (n : NatObj) -> (x : a) -> PrefixArray n a
NatPrefixReplicate n x sl = x

public export
NatPrefixAppend : {a : Type} -> {m, n : NatObj} ->
  PrefixArray m a -> PrefixArray n a -> PrefixArray (natObjSum m n) a
NatPrefixAppend {a} {m} {n} f g (k ** morph) with (NatStrictLTDec k m)
  NatPrefixAppend {a} {m} {n} f g (k ** morph) | Left lt =
    f (k ** lt)
  NatPrefixAppend {a} {m} {n} f g (k ** morph) | Right gte =
    g (natObjMinus gte ** natObjMinusLt gte morph)

public export
natSliceRunningSum : {n : NatObj} ->
  SliceArray n NatObj -> SliceArray (NatOS n) NatObj
natSliceRunningSum {n} v =
  NatObjBoundedGenFold {n} {a=(const NatObj)} {b=(const NatObj)}
    v NatOZ (\_, _ => natObjSum)

public export
natSliceSum : {n : NatObj} -> SliceArray n NatObj -> NatObj
natSliceSum {n} v = natSliceRunningSum v (NatOSliceMax (NatOS n))

public export
NatSliceTruncate : {a : Type} -> {n : NatObj} ->
  SliceArray (NatOS n) a -> SliceArray n a
NatSliceTruncate arr (m ** morph) = arr (m ** NatLTInc morph)

public export
NatPrefixTruncate : {a : Type} -> {n : NatObj} ->
  PrefixArray (NatOS n) a -> PrefixArray n a
NatPrefixTruncate arr (m ** morph) = arr (m ** NatLTInc morph)

public export
NatPrefixFoldAppendStepSumMorph : {a : Type} -> {n : NatObj} ->
  (lengths : SliceArray n NatObj) ->
  (m : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  (morph' : NatLTMorph (m, NatOS n)) ->
  (morph'' : NatLTMorph (NatOS m, NatOS n)) ->
  natObjSum
    (lengths (m ** morph))
    (natSliceRunningSum lengths (m ** morph')) =
  natSliceRunningSum lengths (NatOS m ** morph'')
NatPrefixFoldAppendStepSumMorph {a} {n} lengths m morph morph' morph'' =
  rewrite NatCatThin _ (NatLTFromSucc m n morph'') morph in
  rewrite NatCatThin _ morph' _ in
  Refl

public export
NatPrefixFoldAppendStepSum : {a : Type} -> {n : NatObj} ->
  (lengths : SliceArray n NatObj) ->
  (m : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  natObjSum
    (lengths (m ** morph))
    (natSliceRunningSum lengths (m ** NatLTInc morph)) =
  natSliceRunningSum lengths (NatOS m ** NatLTMorphToSucc morph)
NatPrefixFoldAppendStepSum {a} {n} lengths m morph =
  NatPrefixFoldAppendStepSumMorph {a} {n} lengths m morph
    (NatLTInc morph) (NatLTMorphToSucc morph)

public export
NatPrefixFoldAppendStep : {a : Type} -> {n : NatObj} ->
  (lengths : SliceArray n NatObj) ->
  (m : NatObj) -> (morph : NatLTMorph (m, n)) ->
  PrefixArray (lengths (m ** morph)) a ->
  PrefixArray (natSliceRunningSum lengths (m ** NatLTInc morph)) a ->
  PrefixArray (natSliceRunningSum lengths (NatOS m ** NatLTMorphToSucc morph)) a
NatPrefixFoldAppendStep {a} {n} lengths m morph sc ss =
  rewrite sym (NatPrefixFoldAppendStepSum {a} {n} lengths m morph) in
  NatPrefixAppend sc ss

public export
NatPrefixFoldAppend : {a : Type} -> {n : NatObj} ->
  (lengths : SliceArray n NatObj) ->
  (prefixes : (sl : NatOSlice n) -> PrefixArray (lengths sl) a) ->
  PrefixArray (natSliceSum lengths) a
NatPrefixFoldAppend {a} {n} lengths prefixes =
  NatObjBoundedFold
    {a=(\sl => PrefixArray (lengths sl) a)}
    {b=(\sl => PrefixArray (natSliceRunningSum lengths sl) a)}
    prefixes
    (\sl => void $ FromLTZeroContra _ $ snd sl)
    (NatPrefixFoldAppendStep {a} {n} lengths)

public export
prefixMapFromListRev : (n : Nat) -> (l : List Nat) ->
  Maybe (NatOPrefix (MetaToNatObj (length l)) -> NatOPrefix (MetaToNatObj n))
prefixMapFromListRev n [] =
  Just $ \sl => void $ FromLTZeroContra (fst sl) (snd sl)
prefixMapFromListRev n (x :: xs) = case prefixMapFromListRev n xs of
  Just f => case NatOPrefixMaybe {n=(MetaToNatObj n)} (MetaToNatObj x) of
    Just sl =>
      Just $ \sl' => case sl' of
          (m ** morph) =>
            case MorphToStrict (NatLTFromSucc _ _ morph) of
              Left eq => sl
              Right lt => f (m ** lt)
    Nothing => Nothing
  Nothing => Nothing

public export
prefixMapFromList : (n : Nat) -> (l : List Nat) ->
  Maybe (NatOPrefix (MetaToNatObj (length l)) -> NatOPrefix (MetaToNatObj n))
prefixMapFromList n l =
  rewrite sym (reverseLength l) in prefixMapFromListRev n (reverse l)

public export
InitPrefixMap : (n : Nat) ->
  (l : List Nat) -> {auto ok : IsJustTrue (prefixMapFromList n l)} ->
  MetaPrefixMap (length l) n
InitPrefixMap _ _ {ok} = fromIsJust ok

public export
DepPrefixContraMap :
  {domPos, codPos : NatObj} ->
  (domDir : PrefixArray domPos NatObj) ->
  (codDir : PrefixArray codPos NatObj) ->
  (posMap : PrefixMap domPos codPos) ->
  Type
DepPrefixContraMap {domPos} {codPos} domDir codDir posMap =
  (pos : NatOPrefix domPos) -> PrefixMap (codDir (posMap pos)) (domDir pos)

public export
showDepPrefixContraMap :
  {domPos, codPos : NatObj} ->
  (domDir : PrefixArray domPos NatObj) ->
  (codDir : PrefixArray codPos NatObj) ->
  (posMap : PrefixMap domPos codPos) ->
  DepPrefixContraMap domDir codDir posMap ->
  String
showDepPrefixContraMap {domPos} {codPos} domDir codDir posMap dpm =
  NatObjPrefixFold
    {n=domPos}
    {a=(\pos => PrefixMap (codDir (posMap pos)) (domDir pos))}
    {b=(const String)}
    dpm
    "[empty domain]"
    (\m, morph, dirmap, ss =>
      let ss' = if m == NatOZ then "" else ss ++ "; " in
      ss' ++ "codomain[" ++ show (fst (posMap (m ** morph))) ++
      "] -> domain[" ++ show m ++ "]: " ++
      prefixArrayStringFold (show . fst) dirmap)

public export
depPrefixContraMapFromListsRev :
  {domPos, codPos : NatObj} ->
  (domDir : PrefixArray domPos NatObj) ->
  (codDir : PrefixArray codPos NatObj) ->
  (posMap : PrefixMap domPos codPos) ->
  List (List Nat) ->
  Maybe (DepPrefixContraMap {domPos} {codPos} domDir codDir posMap)
depPrefixContraMapFromListsRev {domPos} {codPos} domDir codDir posMap [] =
  case domPos of
    InNat ZeroF => Just $ \sl => void $ FromLTZeroContra _ (snd sl)
    InNat (SuccF _) => Nothing
depPrefixContraMapFromListsRev {domPos} {codPos} domDir codDir posMap (l :: ls) =
  case domPos of
    InNat ZeroF => Nothing
    InNat (SuccF domPos') =>
      case
        depPrefixContraMapFromListsRev
          {domPos=domPos'}
          {codPos}
          (PrefixArrayTruncate domDir)
          codDir
          (PrefixMapTruncate posMap)
          ls of
        Just tlmap =>
          case decEq (length l) (NatObjToMeta $ codDir $ posMap (domPos' ** NatLTMorphToSucc $ NatMorphId domPos')) of
            Yes lenEq =>
              case prefixMapFromList (NatObjToMeta $ domDir (domPos' ** NatLTMorphToSucc $ NatMorphId domPos')) l of
                Just hdmap =>
                  Just $ \pos, coddir => case pos of
                    (posn ** poslt) =>
                      case MorphToStrict (NatLTFromSucc _ _ poslt) of
                        Left Refl => case coddir of
                          (codn ** codlt) =>
                            let
                              morphEq = NatCatThin _ (NatLTMorphToSucc $ NatMorphId posn) poslt
                              codMetaId = NatToMetaId (codDir $ posMap (posn ** NatLTMorphToSucc $ NatMorphId posn))
                              hdmapc = hdmap (codn ** rewrite lenEq in rewrite codMetaId in rewrite morphEq in codlt)
                              domMetaId = NatToMetaId (domDir (posn ** NatLTMorphToSucc $ NatMorphId posn))
                            in
                            replace
                              {p=(\morph' => (m : NatObj ** NatLTStrict m (domDir (posn ** morph'))))}
                              morphEq $
                                replace {p=NatOPrefix} domMetaId hdmapc
                        Right lt =>
                          let teq = PrefixArrayTruncateEq domDir posn lt poslt in
                          let meq = PrefixMapTruncateEq posMap posn lt poslt in
                          rewrite sym teq in
                          tlmap (posn ** lt) $ case coddir of
                            (codn ** codlt) => (codn ** rewrite meq in codlt)
                Nothing => Nothing
            No _ => Nothing
        Nothing => Nothing

public export
depPrefixContraMapFromLists :
  {domPos, codPos : NatObj} ->
  (domDir : PrefixArray domPos NatObj) ->
  (codDir : PrefixArray codPos NatObj) ->
  (posMap : PrefixMap domPos codPos) ->
  List (List Nat) ->
  Maybe (DepPrefixContraMap {domPos} {codPos} domDir codDir posMap)
depPrefixContraMapFromLists domDir codDir posMap =
  depPrefixContraMapFromListsRev domDir codDir posMap . reverse

------------------------------------------
------------------------------------------
---- Types founded in natural numbers ----
------------------------------------------
------------------------------------------

public export
natFoldIdx : {0 x : Type} -> (Nat -> x -> x) -> x -> Nat -> Nat -> x
natFoldIdx op acc idx Z = acc
natFoldIdx op acc idx (S n) = natFoldIdx op (op idx acc) (S idx) n

public export
record NatFoldAlg (0 x : Type) where
  constructor MkNatFold
  nfOp : Nat -> x -> x
  nfZero : x

public export
natFold : {0 x : Type} -> NatFoldAlg x -> Nat -> x
natFold {x} (MkNatFold op z) = natFoldIdx op z Z

--------------------------------
---- Dependent endofunctors ----
--------------------------------

public export
NatDepPredF : (NatObj -> Type) -> NatObj -> Type
NatDepPredF a n = a n -> Type

public export
NatDepPred : (NatObj -> Type) -> Type
NatDepPred a = (n : NatObj) -> NatDepPredF a n

public export
NatDepFunctorStep : (NatObj -> Type) -> Type
NatDepFunctorStep = NatObjInductionStep . NatDepPredF

public export
NatDepFunctorF : (NatObj -> Type) -> NatObj -> Type
NatDepFunctorF a n = NatDepPredF a NatOZ -> NatDepPredF a n

public export
NatDepFunctor : (NatObj -> Type) -> Type
NatDepFunctor a = (n : NatObj) -> NatDepFunctorF a n

public export
DepFunctorIter : {a : NatObj -> Type} ->
  NatDepFunctorStep a -> NatDepFunctor a
DepFunctorIter {a} f n b = NatObjInd (NatDepPredF a) b f n

---------------
---- Lists ----
---------------

public export
data ListF : Type -> Type -> Type where
  NilF : ListF atom carrier
  ConsF : atom -> carrier -> ListF atom carrier

public export
Bifunctor ListF where
  bimap f g NilF = NilF
  bimap f g (ConsF x l) = ConsF (f x) (g l)

public export
showListF : {0 atom, carrier : Type} ->
  (atom -> String) -> (carrier -> String) ->
  ListF atom carrier -> String
showListF sa sc NilF = "[]"
showListF sa sc (ConsF x l) = "(" ++ sa x ++ " :: " ++ sc l ++ ")"

public export
(Show atom, Show carrier) => Show (ListF atom carrier) where
  show = showListF show show

public export
ListAlg : Type -> Type -> Type
ListAlg = Algebra . ListF

public export
FreeList : Type -> Type -> Type
FreeList = FreeMonad . ListF

public export
MuList : Type -> Type
MuList = Mu . ListF

public export
ListCoalg : Type -> Type -> Type
ListCoalg = Coalgebra . ListF

public export
CofreeList : Type -> Type -> Type
CofreeList = CofreeComonad . ListF

public export
NuList : Type -> Type
NuList = Nu . ListF

public export
cataListF : {atom : Type} -> ParamCata $ ListF atom
cataListF v a subst alg (InFree x) = case x of
  TermVar var => subst var
  TermComposite l => alg $ case l of
    NilF => NilF
    ConsF x l' => ConsF x $ cataListF v a subst alg l'

public export
interpListFAlg : {atom : Type} -> ListAlg atom $ List atom
interpListFAlg NilF = []
interpListFAlg (ConsF x l') = x :: l'

public export
interpFreeListF : {atom : Type} -> {v : Type} ->
  (subst : v -> List atom) -> FreeList atom v -> List atom
interpFreeListF {atom} {v} subst = cataListF v (List atom) subst interpListFAlg

public export
interpMuListF : {atom : Type} -> MuList atom -> List atom
interpMuListF {atom} = interpFreeListF {v=Void} (voidF $ List atom)

public export
(atom : Type) => Show atom => Show (MuList atom) where
  show = show . interpMuListF

public export
lengthAlg : {atom : Type} -> NaturalTransformation (ListF atom) NatF
lengthAlg _ NilF = ZeroF
lengthAlg _ (ConsF _ l) = SuccF l

public export
freeLengthAlg : {atom : Type} -> FreeAdjCounit NatF (ListF atom)
freeLengthAlg = natTransFreeAlg lengthAlg

public export
lengthLF : {atom : Type} -> NaturalTransformation (FreeList atom) FreeNat
lengthLF = natTransMapFree cataListF lengthAlg

--------------------------------------------
---- Fixed-width binary natural numbers ----
--------------------------------------------

public export
BinNatF : Type -> Type
BinNatF = ListF Bool

-- Inherited from ListF.
public export
Functor BinNatF

-- Inherited from ListF.
public export
(Show carrier) => Show (BinNatF carrier)

public export
BinNatAlg : Type -> Type
BinNatAlg = Algebra BinNatF

public export
FreeBinNat : Type -> Type
FreeBinNat = FreeMonad BinNatF

public export
MuBinNat : Type
MuBinNat = Mu BinNatF

public export
BinNatCoalg : Type -> Type
BinNatCoalg = Coalgebra BinNatF

public export
CofreeBinNat : Type -> Type
CofreeBinNat = CofreeComonad BinNatF

public export
NuBinNat : Type
NuBinNat = Nu BinNatF

public export
cataBinNatF : ParamCata BinNatF
cataBinNatF = cataListF {atom=Bool}

public export
Show MuBinNat

public export
interpBinNatFListBoolAlg : BinNatAlg $ List Bool
interpBinNatFListBoolAlg = interpListFAlg {atom=Bool}

public export
interpFreeBinNatListBoolF : {v : Type} ->
  (subst : v -> List Bool) -> FreeBinNat v -> List Bool
interpFreeBinNatListBoolF = interpFreeListF {atom=Bool}

public export
interpMuBinNatListBoolF : MuBinNat -> List Bool
interpMuBinNatListBoolF = interpMuListF {atom=Bool}

public export
interpBinNatFBinAlg : BinNatAlg Bin
interpBinNatFBinAlg NilF = []
interpBinNatFBinAlg (ConsF b n) = boolToDigit b :: n

public export
interpMuBinNatBin : MuBinNat -> Bin
interpMuBinNatBin = cataBinNatF Void Bin (voidF Bin) interpBinNatFBinAlg

public export
muBinNatToNat : MuBinNat -> Nat
muBinNatToNat = toNat . interpMuBinNatBin

public export
binNatLengthAlg : NaturalTransformation BinNatF NatF
binNatLengthAlg = lengthAlg {atom=Bool}

public export
binNatLength : FreeMonadNatTrans BinNatF NatF
binNatLength = natTransMapFree cataBinNatF binNatLengthAlg

-----------------------------------------------------
---- Pairs of fixed-width binary natural numbers ----
-----------------------------------------------------

public export
data BinPairF : Type -> Type where
  BinPair : ProductF BinNatF BinNatF carrier -> BinPairF carrier

------------------------------------------------------
------------------------------------------------------
---- Idris sigma, product, and functor categories ----
------------------------------------------------------
------------------------------------------------------

public export
SigmaObject : {a : Type} -> (a -> Type) -> Type
SigmaObject {a} b = DPair a b

public export
SigmaMorphism : {a, a' : Type} ->
  (a -> Type) -> (a' -> Type) -> (a -> a') -> Type
SigmaMorphism {a} b b' f = (x : a) -> b x -> b' (f x)

public export
sigmaCompose : {a, a', a'' : Type} ->
  {b : a -> Type} -> {b' : a' -> Type} -> {b'' : a'' -> Type} ->
  {f' : a' -> a''} -> {f : a -> a'} ->
  SigmaMorphism b' b'' f' ->
  SigmaMorphism b b' f ->
  SigmaMorphism b b'' (f' . f)
sigmaCompose {f} m' m x y = m' (f x) $ m x y

-- The objects of a product category, where the product is represented by
-- a function from an index type (as opposed to by a pair or a list -- the
-- function type allows the assignment of names from a user-selected domain,
-- and the definition of the category of endofunctors on Idris's `Type`
-- by specializing the index to `Type`).
public export
ProductCatObject : Type -> Type
ProductCatObject idx = idx -> Type

public export
FunctorCatObject : Type
FunctorCatObject = ProductCatObject Type

public export
ProductCatMorphism : {idx : Type} ->
  ProductCatObject idx -> ProductCatObject idx -> Type
ProductCatMorphism {idx} dom cod = (i : idx) -> dom i -> cod i

public export
FunctorCatMorphism : FunctorCatObject -> FunctorCatObject -> Type
FunctorCatMorphism = ProductCatMorphism {idx=Type}

public export
ProductCatObjectMap : Type -> Type -> Type
ProductCatObjectMap idx idx' = ProductCatObject idx -> ProductCatObject idx'

public export
FunctorCatObjectMap : Type
FunctorCatObjectMap = ProductCatObjectMap Type Type

public export
ProductCatObjectEndoMap : Type -> Type
ProductCatObjectEndoMap idx = ProductCatObjectMap idx idx

public export
FunctorCatObjectEndoMap : Type
FunctorCatObjectEndoMap = ProductCatObjectEndoMap Type

public export
ProductCatMorphismMap :
  {idx, idx' : Type} -> ProductCatObjectMap idx idx' -> Type
ProductCatMorphismMap {idx} {idx'} objmap =
  (dom, cod : ProductCatObject idx) ->
  (m : ProductCatMorphism dom cod) ->
  ProductCatMorphism (objmap dom) (objmap cod)

public export
FunctorCatMorphismMap : FunctorCatObjectMap -> Type
FunctorCatMorphismMap = ProductCatMorphismMap {idx=Type} {idx'=Type}

public export
ProductCatMorphismEndoMap : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductCatMorphismEndoMap = ProductCatMorphismMap

public export
FunctorCatMorphismEndoMap : FunctorCatObjectEndoMap -> Type
FunctorCatMorphismEndoMap = ProductCatMorphismEndoMap {idx=Type}

public export
ProductCatFunctor : Type -> Type -> Type
ProductCatFunctor idx idx' =
  DPair (ProductCatObjectMap idx idx') ProductCatMorphismMap

public export
FunctorCatFunctor : Type
FunctorCatFunctor = ProductCatFunctor Type Type

public export
ProductCatEndofunctor : Type -> Type
ProductCatEndofunctor idx = ProductCatFunctor idx idx

public export
FunctorCatEndofunctor : Type
FunctorCatEndofunctor = ProductCatEndofunctor Type

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Categorial algebra on sigma, product, and functor categories ----
----------------------------------------------------------------------
----------------------------------------------------------------------

-- The version of `Algebra` for an Idris product category.
public export
ProductCatAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatAlgebra f a = ProductCatMorphism (f a) a

-- The version of `Coalgebra` for an Idris product category.
public export
ProductCatCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatCoalgebra f a = ProductCatMorphism a (f a)

-- The product-category version of `TermFunctor`.  In the case of just two
-- categories, for example, if `F` and `G` are the components of the input
-- functor, each going from the product category to one of the components,
-- and `v` and `w` are the components of the variable type, then this
-- expression becomes:
--
--  `FGvw[x,y] = (v + F[x,y], w + G[x,y])`
public export
data ProductCatTermFunctor : {idx : Type} ->
    ProductCatObjectEndoMap idx ->
    ProductCatObject idx ->
    ProductCatObjectEndoMap idx where
  ProductCatTermVar : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} ->
    {0 v, a : ProductCatObject idx} ->
    {i : idx} ->
    v i -> ProductCatTermFunctor f v a i
  ProductCatTermComposite : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} ->
    {0 v, a : ProductCatObject idx} ->
    {i : idx} ->
    f a i -> ProductCatTermFunctor f v a i

-- The dual of `ProductCatTermFunctor`, also known as the product-category
-- version of `TreeFunctor`.
public export
data ProductCatTreeFunctor : {idx : Type} ->
    ProductCatObjectEndoMap idx ->
    ProductCatObject idx ->
    ProductCatObjectEndoMap idx where
  ProductCatTreeNode : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} ->
    {0 l, a : ProductCatObject idx} ->
    {i : idx} ->
    l i -> f a i -> ProductCatTreeFunctor f l a i

public export
ProductCatTermCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTermCoalgebra f v a =
  ProductCatCoalgebra (ProductCatTermFunctor f v) a

export
treeLabelProduct : ProductCatTreeFunctor f l a i -> l i
treeLabelProduct (ProductCatTreeNode a' _) = a'

export
treeSubtreeProduct : ProductCatTreeFunctor f l a i -> f a i
treeSubtreeProduct (ProductCatTreeNode _ fx) = fx

public export
ProductCatTermAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTermAlgebra f v a =
  ProductCatAlgebra (ProductCatTermFunctor f v) a

public export
ProductCatTreeCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTreeCoalgebra f v a =
  ProductCatCoalgebra (ProductCatTreeFunctor f v) a

public export
ProductCatTreeAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTreeAlgebra f v a =
  ProductCatAlgebra (ProductCatTreeFunctor f v) a

-- The product-category version of `FreeMonad`.
public export
data ProductCatFreeMonad : {idx : Type} ->
    ProductCatObjectEndoMap idx -> ProductCatObjectEndoMap idx where
  InFreeProduct : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} -> {0 a : ProductCatObject idx} ->
    ProductCatTermAlgebra f a (ProductCatFreeMonad f a)

public export
data ProductCatCofreeComonad : {idx : Type} ->
    ProductCatObjectEndoMap idx -> ProductCatObjectEndoMap idx where
  InCofreeProduct : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} -> {l : ProductCatObject idx} ->
    {i : idx} ->
    Inf (ProductCatTreeFunctor f l (ProductCatCofreeComonad f l) i) ->
    ProductCatCofreeComonad f l i

public export
inFreeVarProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {0 a : ProductCatObject idx} ->
  ProductCatCoalgebra (ProductCatFreeMonad f) a
inFreeVarProduct i = InFreeProduct i . ProductCatTermVar

public export
inFreeCompositeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {a : ProductCatObject idx} ->
  ProductCatAlgebra f (ProductCatFreeMonad f a)
inFreeCompositeProduct i = InFreeProduct i . ProductCatTermComposite

public export
outFreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {a : ProductCatObject idx} ->
  ProductCatTermCoalgebra f a (ProductCatFreeMonad f a)
outFreeProduct i (InFreeProduct i x) = x

public export
inCofreeTreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} ->
  {l : ProductCatObject idx} ->
  {i : idx} ->
  l i ->
  f (ProductCatCofreeComonad f l) i ->
  ProductCatCofreeComonad f l i
inCofreeTreeProduct x fx = InCofreeProduct $ ProductCatTreeNode x fx

public export
outCofreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {l : ProductCatObject idx} ->
  {i : idx} ->
  ProductCatCofreeComonad f l i ->
  ProductCatTreeFunctor f l (ProductCatCofreeComonad f l) i
outCofreeProduct (InCofreeProduct x) = x

public export
MuProduct : {idx : Type} -> ProductCatObjectEndoMap idx -> ProductCatObject idx
MuProduct f = ProductCatFreeMonad f (const Void)

public export
NuProduct : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx
NuProduct f = ProductCatCofreeComonad f (const ())

public export
ProductCatParamCata : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductCatParamCata f =
  (v, a : ProductCatObject idx) ->
  ProductCatTermAlgebra f v a ->
  ProductCatMorphism (ProductCatFreeMonad f v) a

public export
ProductCatParamAna : {idx : Type} ->
  ProductCatObjectEndoMap idx ->
  Type
ProductCatParamAna f =
  (v, l : ProductCatObject idx) ->
  ProductCatTreeCoalgebra f v l ->
  ProductCatMorphism (ProductCatCofreeComonad f v) l

public export
ProductCatamorphism : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductCatamorphism {idx} f =
  (a : ProductCatObject idx) ->
  ProductCatAlgebra f a ->
  ProductCatMorphism (MuProduct f) a

public export
ProductAnamorphism : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductAnamorphism {idx} f =
  (a : ProductCatObject idx) ->
  ProductCatCoalgebra f a ->
  ProductCatMorphism a (NuProduct f)

---------------------------------
---------------------------------
---- Finite bicomplete types ----
---------------------------------
---------------------------------

public export
data FiniteTypeF : Type -> Type where
  FinVoidF : FiniteTypeF carrier
  FinUnitF : FiniteTypeF carrier
  FinProductF :
    (FiniteTypeF carrier, FiniteTypeF carrier) -> FiniteTypeF carrier
  FinCoproductF :
    (FiniteTypeF carrier, FiniteTypeF carrier) -> FiniteTypeF carrier

public export
data FiniteType : Type -> Type where
  FinVoid : FiniteType Void
  FinUnit : FiniteType Unit
  FinProduct : {erasedFst, erasedSnd : Type} ->
    FiniteType erasedFst -> FiniteType erasedSnd ->
    FiniteType (erasedFst, erasedSnd)
  FinCoproduct : {erasedL, erasedR : Type} ->
    FiniteType erasedL -> FiniteType erasedR ->
    FiniteType (Either erasedL erasedR)

public export
data FiniteBicompleteType :
    {metaType : Type} -> FiniteType metaType -> Type where
  InFinite : {metaType : Type} ->
    (erased : FiniteType metaType) -> FiniteBicompleteType {metaType} erased

----------------------------------------------------------
----------------------------------------------------------
---- Categories represented by metalanguage functions ----
----------------------------------------------------------
----------------------------------------------------------

-- We define a notion of a type which can be represented by a metalanguage
-- function.

public export
ObjRepresentation : Type -> Type -> Type
ObjRepresentation represented representing =
  represented -> (representing -> representing)

public export
ObjRepresenting : Type -> Type
ObjRepresenting = DPair Type . ObjRepresentation

public export
ObjRepresentedBy : Type -> Type
ObjRepresentedBy = DPair Type . flip ObjRepresentation

-- We may represent functions between function-represented types as
-- ways of translating back and forth between the types underlying
-- the representations of the domain and codomain.  This type
-- defines the representation of one particular function.  Note that
-- this is still non-trivial even if `domRep` and `codRep` are the
-- same -- in that case we might not call it "translating", but it can
-- still be "rearranging".
public export
FunctionRepresentation : (domRep, codRep : Type) -> Type
FunctionRepresentation domRep codRep = (codRep -> domRep, domRep -> codRep)

public export
transformRep : {domain, domRep, codomain, codRep : Type} ->
  (domain -> codomain) ->
  FunctionRepresentation domRep codRep ->
  ObjRepresentation domain domRep ->
  ObjRepresentation domain codRep
transformRep f (codToDom, domToCod) domRepFunc x =
  domToCod . domRepFunc x . codToDom

-- Define a notion of consistency of the representation of a particular function
-- with the representations of its domain and codomain.
public export
FuncRepCommutes : {domain, domRep, codomain, codRep : Type} ->
  (domRepFunc : ObjRepresentation domain domRep) ->
  (codRepFunc : ObjRepresentation codomain codRep) ->
  (domain -> codomain) ->
  FunctionRepresentation domRep codRep -> Type
FuncRepCommutes {domRep} {codRep} domRepFunc codRepFunc f funcRep =
  ExtEq (codRepFunc . f) (transformRep f funcRep domRepFunc)

public export
CommutingFuncRep : {domain, domRep, codomain, codRep : Type} ->
  (domRepFunc : ObjRepresentation domain domRep) ->
  (codRepFunc : ObjRepresentation codomain codRep) ->
  (domain -> codomain) -> Type
CommutingFuncRep domRepFunc codRepFunc f =
  DPair
    (FunctionRepresentation domRep codRep)
    (FuncRepCommutes domRepFunc codRepFunc f)

public export
HomObjRep : {domain, domRep, codomain, codRep : Type} ->
  (domRepFunc : ObjRepresentation domain domRep) ->
  (codRepFunc : ObjRepresentation codomain codRep) ->
  Type
HomObjRep domRepFunc codRepFunc =
  (f : domain -> codomain) -> CommutingFuncRep domRepFunc codRepFunc f

-- We now define a notion of a category with the following properties
-- (together with the standard axioms of category theory):
--  - Every object and morphism has a representation as a metalanguage function
--    (the objects all share a representation, but representations of morphisms
--    with one signature are allowed to differ from those with other signatures)
--  - All of those representations satisfy `FuncRepCommutes` above
--  - All of the representation functions have decidable extensional equalities
--    (this does not only mean that there is a decidable equality for each
--    input value, but rather the stronger condition that we can decide the
--    extensional equality of entire functions)
--  - Equality on objects and morphisms is given by extensional equality of
--    their metalanguage representations
-- We shall call such a category "decidably representable".
public export
record DecRepCat (obj, morph : Type) where
  constructor MkDecRepCat

  -- Each object is represented by an endomorphism on a type
  -- which we call `DecRepObjRepType`.
  DecRepObjRepType : Type
  DecRepObjRep : ObjRepresentation obj DecRepObjRepType

  -- We allow each hom-set to use a different representation.
  -- (The _object_ representation functions for the domain and
  -- codomain are the same, however, because the whole category
  -- shares one object representation function.  The reason for that
  -- is that it creates a monoid on objects, allowing them to be
  -- composed.)
  DecRepMorphRep : obj -> obj -> HomObjRep DecRepObjRep DecRepObjRep

  -- We represent the relationship of objects and morphisms by fibrations,
  -- rather than by dependent types.  That's partly convenient in that it's
  -- more in the style of category theory, but the more fundmental reason is
  -- that we are treating equality of objects and morphisms as quotiented
  -- over the extensional equivalence of the representations.
  -- So we might, for example, be able to compose `g : c -> d` after
  -- `f : a -> b` even if we can't prove that `b = c`, because the
  -- functions which _represent_ `b` and `c` might be extensionally equal.
  DecRepId : obj -> morph
  DecRepCompose : morph -> morph -> morph
  DecRepSignature : morph -> (obj, obj)

-----------------------------------------------------------
-----------------------------------------------------------
---- Interpretations and representations of categories ----
-----------------------------------------------------------
-----------------------------------------------------------

-- First, we define the notion of a category which is interpreted into
-- functions of the metalanguage.
--
-- Interpretation means mapping morphisms of the category into metalanguage
-- functions which correspond to their _meaning_.  A category which can be
-- interpreted into the metalanguage must be no stronger as a logic than the
-- metalanguage.
public export
record MetaCat where
  constructor MkMetaCat
  -- The types of `Type` which represent the objects and morphisms of the
  -- interpreted category.
  MetaObj : Type
  MetaMorphism : MetaObj -> MetaObj -> Type

  -- Identity and composition.
  MetaId : (a : MetaObj) -> MetaMorphism a a
  MetaCompose : (a, b, c : MetaObj) ->
    MetaMorphism b c -> MetaMorphism a b -> MetaMorphism a c

  -- The interpretations of the objects and morphisms of the category.
  MetaObjInterp : MetaObj -> Type
  MetaMorphismInterp : (a, b : MetaObj) ->
    MetaMorphism a b -> MetaObjInterp a -> MetaObjInterp b

public export
record MetaCatCorrect (cat : MetaCat) where
  constructor MkMetaCatCorrect
  -- Correctness conditions (the axioms of category theory), with
  -- equality up to first-order (non-recursive) extensional equality of the
  -- of the morphisms as metalanguage functions.
  MetaLeftId : {a, b : MetaObj cat} ->
    (f : MetaMorphism cat a b) ->
    ExtEq
      (MetaMorphismInterp cat a b (MetaCompose cat a b b (MetaId cat b) f))
      (MetaMorphismInterp cat a b f)
  MetaRightId : {a, b : MetaObj cat} ->
    (f : MetaMorphism cat a b) ->
    ExtEq
      (MetaMorphismInterp cat a b f)
      (MetaMorphismInterp cat a b (MetaCompose cat a a b f (MetaId cat a)))
  MetaAssoc : {a, b, c, d : MetaObj cat} ->
    (h : MetaMorphism cat c d) ->
    (g : MetaMorphism cat b c) ->
    (f : MetaMorphism cat a b) ->
    ExtEq
      (MetaMorphismInterp cat a d
        (MetaCompose cat a c d h (MetaCompose cat a b c g f)))
      (MetaMorphismInterp cat a d
        (MetaCompose cat a b d (MetaCompose cat b c d h g) f))

public export
MorphismEq : {cat : MetaCat} -> {a, b : MetaObj cat} ->
  MetaMorphism cat a b -> MetaMorphism cat a b -> Type
MorphismEq m m' =
  ExtEq (MetaMorphismInterp cat a b m) (MetaMorphismInterp cat a b m')

public export
TypeTensorProd : Type
TypeTensorProd = Type -> Type -> Type

-- Because we are going to enrich further categories over
-- `MetaCat`s, we define a version of `MetaCat` that has a tensor product, whose
-- properties we ensure by requiring that it be interpreted as the
-- product in `Type` (known as `Pair`).
record MonoidalCat (typeProd : TypeTensorProd) (underlying : MetaCat) where
  constructor MkMonoidalCat
  MetaTensorObj : MetaObj underlying -> MetaObj underlying -> MetaObj underlying
  MetaTensorId : MetaObj underlying
  MetaTensorObjInterp : (a, b : MetaObj underlying) ->
    MetaObjInterp underlying (MetaTensorObj a b) ->
    typeProd (MetaObjInterp underlying a) (MetaObjInterp underlying b)
  MetaTensorObjInterpInv : (a, b : MetaObj underlying) ->
    typeProd (MetaObjInterp underlying a) (MetaObjInterp underlying b) ->
    MetaObjInterp underlying (MetaTensorObj a b)
  MetaTensorMorph : {a, b, c, d : MetaObj underlying} ->
    MetaMorphism underlying a c -> MetaMorphism underlying b d ->
    MetaMorphism underlying (MetaTensorObj a b) (MetaTensorObj c d)

public export
record MonoidalCatCorrect
    (typeProd : TypeTensorProd)
    (underlying : MetaCat)
    (monCat : MonoidalCat typeProd underlying) where
  constructor MkMonoidalCatCorrect
  MetaTensorObjInterpCorrect : (a, b : MetaObj underlying) ->
    ExtInverse
      (MetaTensorObjInterpInv monCat a b)
      (MetaTensorObjInterp monCat a b)
  {-
  MetaTensorLeftIdCorrect : ?MetaTensorLeftIdCorrect_hole
  MetaTensorRightIdCorrect : ?MetaTensorRightIdCorrect_hole
  MetaTensorAssociatorCorrect : ?MetaTensorAssociatorCorrect_hole
  -}

public export
CartesianCat : MetaCat -> Type
CartesianCat = MonoidalCat Pair

public export
BiCartesianCat : MetaCat -> Type
BiCartesianCat underlying =
  (CartesianCat underlying, MonoidalCat Either underlying)

public export
HomObj : TypeTensorProd
HomObj a b = a -> b

public export
ExponentialClosedCat : MetaCat -> Type
ExponentialClosedCat = MonoidalCat HomObj

public export
CartesianClosedCat : MetaCat -> Type
CartesianClosedCat underlying =
  (CartesianCat underlying, ExponentialClosedCat underlying)

public export
BicartesianClosedCat : MetaCat -> Type
BicartesianClosedCat underlying =
  (CartesianClosedCat underlying, MonoidalCat Either underlying)

public export
record MetaFunctor (catC, catD : MetaCat) where
  constructor MkMetaFunctor
  MetaFunctorObjMap : MetaObj catC -> MetaObj catD
  MetaFunctorMorphMap : {a, b : MetaObj catC} ->
      MetaMorphism catC a b ->
      MetaMorphism catD (MetaFunctorObjMap a) (MetaFunctorObjMap b)

public export
record MetaFunctorCorrect
    {catC, catD : MetaCat} (functor : MetaFunctor catC catD) where
  -- Correctness conditions.
  MetaFunctorId : (a : MetaObj catC) ->
    MorphismEq
      {cat=catD}
      {a=(MetaFunctorObjMap functor a)} {b=(MetaFunctorObjMap functor a)}
      (MetaFunctorMorphMap functor {a} {b=a} (MetaId catC a))
      (MetaId catD (MetaFunctorObjMap functor a))
  MetaFunctorCompose : {a, b, c : MetaObj catC} ->
    (g : MetaMorphism catC b c) ->
    (f : MetaMorphism catC a b) ->
    MorphismEq
      {cat=catD}
      {a=(MetaFunctorObjMap functor a)} {b=(MetaFunctorObjMap functor c)}
      (MetaFunctorMorphMap functor {a} {b=c} (MetaCompose catC a b c g f))
      (MetaCompose catD
        (MetaFunctorObjMap functor a)
        (MetaFunctorObjMap functor b)
        (MetaFunctorObjMap functor c)
        (MetaFunctorMorphMap functor {a=b} {b=c} g)
        (MetaFunctorMorphMap functor {a} {b} f))

public export
record FunctorEq {catC, catD : MetaCat} (f, g : MetaFunctor catC catD) where
  constructor MkFunctorEq
  ObjMapEq : (a : MetaObj catC) -> MetaFunctorObjMap f a = MetaFunctorObjMap g a
  MorphMapEq : {a, b : MetaObj catC} -> (m : MetaMorphism catC a b) ->
    MorphismEq
      {cat=catD}
      {a=(MetaFunctorObjMap f a)} {b=(MetaFunctorObjMap f b)}
      (MetaFunctorMorphMap f {a} {b} m)
      (replace
        {p=(\a' : MetaObj catD => MetaMorphism catD a' (MetaFunctorObjMap f b))}
        (sym (ObjMapEq a)) $
       replace
        {p=(\b' : MetaObj catD => MetaMorphism catD (MetaFunctorObjMap g a) b')}
        (sym (ObjMapEq b))
        (MetaFunctorMorphMap g {a} {b} m))

public export
IdFunctor : (cat : MetaCat) -> MetaFunctor cat cat
IdFunctor cat = MkMetaFunctor id id

public export
IdFunctorCorrect : (cat : MetaCat) -> MetaFunctorCorrect (IdFunctor cat)
IdFunctorCorrect cat = ?IdFunctorCorrect_hole

public export
ComposeFunctor : {catC, catD, catE : MetaCat} ->
  MetaFunctor catD catE -> MetaFunctor catC catD ->
  MetaFunctor catC catE
ComposeFunctor g f = MkMetaFunctor
  (MetaFunctorObjMap g . MetaFunctorObjMap f)
  (MetaFunctorMorphMap g . MetaFunctorMorphMap f)

public export
ComposeFunctorCorrect : {catC, catD, catE : MetaCat} ->
  (g : MetaFunctor catD catE) -> (f : MetaFunctor catC catD) ->
  MetaFunctorCorrect (ComposeFunctor g f)
ComposeFunctorCorrect g f = ?ComposeFunctorCorrect_hole

public export
MetaFunctorInterp : {catC, catD : MetaCat} -> MetaFunctor catC catD -> Type
MetaFunctorInterp {catC} {catD} f =
  (a : MetaObj catC) ->
  MetaObjInterp catC a ->
  MetaObjInterp catD (MetaFunctorObjMap f a)

public export
MetaEndoFunctor : MetaCat -> Type
MetaEndoFunctor cat = MetaFunctor cat cat

public export
record MetaNatTrans {catC, catD : MetaCat} (f, g : MetaFunctor catC catD) where
  constructor MkMetaNatTrans
  -- Components of the natural transformation.
  MetaNTComponent : (a : MetaObj catC) ->
    MetaMorphism catD (MetaFunctorObjMap f a) (MetaFunctorObjMap g a)

public export
record MetaNatTransCorrect {catC, catD : MetaCat} {f, g : MetaFunctor catC catD}
    (natTrans : MetaNatTrans f g) where
  constructor MkMetaNatTransCorrect
  -- Correctness conditions.
  MetaNTNaturality : (a, b : MetaObj catC) -> (m : MetaMorphism catC a b) ->
    MorphismEq
      {cat=catD} {a=(MetaFunctorObjMap f a)} {b=(MetaFunctorObjMap g b)}
      (MetaCompose catD
        (MetaFunctorObjMap f a)
        (MetaFunctorObjMap f b)
        (MetaFunctorObjMap g b)
        (MetaNTComponent natTrans b)
        (MetaFunctorMorphMap {catC} {catD} {a} {b} f m))
      (MetaCompose catD
        (MetaFunctorObjMap f a)
        (MetaFunctorObjMap g a)
        (MetaFunctorObjMap g b)
        (MetaFunctorMorphMap {catC} {catD} {a} {b} g m)
        (MetaNTComponent natTrans a))

public export
record NatTransEq {catC, catD : MetaCat} {f, f', g, g' : MetaFunctor catC catD}
    (alpha : MetaNatTrans f g) (beta : MetaNatTrans f' g') where
  constructor MkNatTransEq
  ntEqF : FunctorEq f f'
  ntEqG : FunctorEq g g'
  ntEqComponent : (a : MetaObj catC) ->
    MorphismEq
      {cat=catD}
      {a=(MetaFunctorObjMap f a)} {b=(MetaFunctorObjMap g a)}
      (MetaNTComponent alpha a)
      (replace
        {p=(\a' => MetaMorphism catD a' (MetaFunctorObjMap g a))}
        (sym (ObjMapEq ntEqF a)) $
       replace
        {p=(\a' => MetaMorphism catD (MetaFunctorObjMap f' a) a')}
        (sym (ObjMapEq ntEqG a))
        (MetaNTComponent beta a))

public export
IdNatTrans : {catC, catD : MetaCat} -> (f : MetaFunctor catC catD) ->
  MetaNatTrans f f
IdNatTrans {catC} f = MkMetaNatTrans $
  \a => MetaFunctorMorphMap f (MetaId catC a)

public export
IdNatTransCorrect : {catC, catD : MetaCat} -> (f : MetaFunctor catC catD) ->
  MetaNatTransCorrect (IdNatTrans f)
IdNatTransCorrect = ?IdNatTransCorrect_hole

public export
IdNatTransIdF : (c : MetaCat) -> MetaNatTrans (IdFunctor c) (IdFunctor c)
IdNatTransIdF c = MkMetaNatTrans $ \a => MetaId c a

public export
VerticalCompose : {catC, catD : MetaCat} -> {f, g, h : MetaFunctor catC catD} ->
  MetaNatTrans g h -> MetaNatTrans f g -> MetaNatTrans f h
VerticalCompose {catC} {catD} {f} {g} {h} beta alpha = MkMetaNatTrans $
  \a => MetaCompose catD
    (MetaFunctorObjMap f a)
    (MetaFunctorObjMap g a)
    (MetaFunctorObjMap h a)
    (MetaNTComponent beta a)
    (MetaNTComponent alpha a)

public export
VerticalComposeCorrect :
  {catC, catD : MetaCat} ->
  {f, g, h : MetaFunctor catC catD} ->
  (beta : MetaNatTrans g h) -> (alpha : MetaNatTrans f g) ->
  MetaNatTransCorrect (VerticalCompose beta alpha)
VerticalComposeCorrect = ?VerticalComposeCorrect_hole

public export
HorizontalCompose : {catC, catD, catE : MetaCat} ->
  {f, f' : MetaFunctor catC catD} -> {g, g' : MetaFunctor catD catE} ->
  MetaNatTrans g g' ->
  MetaNatTrans f f' ->
  MetaNatTrans (ComposeFunctor g f) (ComposeFunctor g' f')
HorizontalCompose {catC} {catD} {f} {f'} {g} {g'} beta alpha = MkMetaNatTrans $
  \a => MetaCompose catE
    (MetaFunctorObjMap (ComposeFunctor g f) a)
    (MetaFunctorObjMap (ComposeFunctor g f') a)
    (MetaFunctorObjMap (ComposeFunctor g' f') a)
    (MetaNTComponent beta (MetaFunctorObjMap f' a))
    (MetaFunctorMorphMap
      {a=(MetaFunctorObjMap f a)}
      {b=(MetaFunctorObjMap f' a)}
      g
      (MetaNTComponent alpha a))

public export
HorizontalComposeCorrect : {catC, catD, catE : MetaCat} ->
  {f, f' : MetaFunctor catC catD} -> {g, g' : MetaFunctor catD catE} ->
  (beta : MetaNatTrans g g') -> (alpha : MetaNatTrans f f') ->
  MetaNatTransCorrect (HorizontalCompose beta alpha)
HorizontalComposeCorrect = ?HorizontalComposeCorrect_hole

public export
HorizontalComposeConsistent : {catC, catD, catE : MetaCat} ->
  {f, f' : MetaFunctor catC catD} -> {g, g' : MetaFunctor catD catE} ->
  (beta : MetaNatTrans g g') ->
  (alpha : MetaNatTrans f f') ->
  MetaNatTransCorrect beta ->
  MetaNatTransCorrect alpha ->
  (a : MetaObj catC) ->
    MorphismEq
      {cat=catE}
      {a=(MetaFunctorObjMap (ComposeFunctor g f) a)}
      {b=(MetaFunctorObjMap (ComposeFunctor g' f') a)}
      (MetaNTComponent (HorizontalCompose beta alpha) a)
      (MetaCompose catE
        (MetaFunctorObjMap (ComposeFunctor g f) a)
        (MetaFunctorObjMap (ComposeFunctor g' f) a)
        (MetaFunctorObjMap (ComposeFunctor g' f') a)
        (MetaFunctorMorphMap
          {a=(MetaFunctorObjMap f a)}
          {b=(MetaFunctorObjMap f' a)}
          g'
          (MetaNTComponent alpha a))
        (MetaNTComponent beta (MetaFunctorObjMap f a)))
HorizontalComposeConsistent = ?HorizontalComposeConsistent_hole

public export
MetaNatTransInterp : {catC, catD : MetaCat} -> (f, g : MetaFunctor catC catD) ->
  MetaNatTrans f g -> MetaFunctorInterp f -> MetaFunctorInterp g
MetaNatTransInterp _ _ alpha finterp a =
  (MetaMorphismInterp _ _ _ (MetaNTComponent alpha a)) . (finterp a)

public export
WhiskerLeft : {catB, catC, catD : MetaCat} -> {f, g : MetaFunctor catC catD} ->
  (nu : MetaNatTrans f g) -> (k : MetaFunctor catB catC) ->
  MetaNatTrans (ComposeFunctor f k) (ComposeFunctor g k)
WhiskerLeft {catB} {catC} {catD} {f} {g} nu k = MkMetaNatTrans $
  \a => MetaNTComponent nu $ MetaFunctorObjMap k a

public export
WhiskerLeftCorrect :
  {catB, catC, catD : MetaCat} ->
  {f, g : MetaFunctor catC catD} ->
  (nu : MetaNatTrans f g) -> (k : MetaFunctor catB catC) ->
  MetaNatTransCorrect (WhiskerLeft nu k)
WhiskerLeftCorrect = ?WhiskerLeftCorrect_hole

public export
WhiskerRight : {catC, catD, catE : MetaCat} -> {f, g : MetaFunctor catC catD} ->
  (h : MetaFunctor catD catE) -> (nu : MetaNatTrans f g) ->
  MetaNatTrans (ComposeFunctor h f) (ComposeFunctor h g)
WhiskerRight h nu = MkMetaNatTrans $
  \a => MetaFunctorMorphMap h $ MetaNTComponent nu a

public export
WhiskerRightCorrect :
  {catC, catD, catE : MetaCat} ->
  {f, g : MetaFunctor catC catD} ->
  (h : MetaFunctor catD catE) -> (nu : MetaNatTrans f g) ->
  MetaNatTransCorrect (WhiskerRight h nu)
WhiskerRightCorrect = ?WhiskerRightCorrect_hole

public export
record Adjunction (catC, catD : MetaCat) where
  constructor MkAdjunction
  leftAdjoint : MetaFunctor catD catC
  rightAdjoint : MetaFunctor catC catD
  adjUnit :
    MetaNatTrans (IdFunctor catD) (ComposeFunctor rightAdjoint leftAdjoint)
  adjCounit :
    MetaNatTrans (ComposeFunctor leftAdjoint rightAdjoint) (IdFunctor catC)

public export
record AdjunctionCorrect
    {catC, catD : MetaCat} (adj : Adjunction catC catD) where
  constructor MkAdjunctionCorrect
  triangleLeft :
    NatTransEq
      (VerticalCompose
        (WhiskerLeft (adjCounit adj) (leftAdjoint adj))
        (WhiskerRight (leftAdjoint adj) (adjUnit adj)))
      (IdNatTrans (leftAdjoint adj))
  triangleRight :
    NatTransEq
      (VerticalCompose
        (WhiskerRight (rightAdjoint adj) (adjCounit adj))
        (WhiskerLeft (adjUnit adj) (rightAdjoint adj)))
      (IdNatTrans (rightAdjoint adj))

public export
record AdjunctionEq
    {catC, catD : MetaCat} (adj, adj' : Adjunction catC catD) where
  constructor MkAdjunctionEq
  leftAdjointEq : FunctorEq (leftAdjoint adj) (leftAdjoint adj')
  rightAdjointEq : FunctorEq (rightAdjoint adj) (rightAdjoint adj')
  unitEq : NatTransEq (adjUnit adj) (adjUnit adj')
  counitEq : NatTransEq (adjCounit adj) (adjCounit adj')

public export
IdAdjunction : (c : MetaCat) -> Adjunction c c
IdAdjunction c = MkAdjunction
  (IdFunctor c)
  (IdFunctor c)
  (IdNatTransIdF c)
  (IdNatTransIdF c)

public export
IdAdjunctionCorrect : (c : MetaCat) -> AdjunctionCorrect (IdAdjunction c)
IdAdjunctionCorrect = ?IdAdjunctionCorrect_hole

public export
ComposeAdjunction : {catC, catD, catE : MetaCat} ->
  Adjunction catD catE -> Adjunction catC catD -> Adjunction catC catE
ComposeAdjunction {catC} {catD} {catE} adjr adjl = MkAdjunction
  (ComposeFunctor (leftAdjoint adjl) (leftAdjoint adjr))
  (ComposeFunctor (rightAdjoint adjr) (rightAdjoint adjl))
  (VerticalCompose
    (WhiskerRight
      (rightAdjoint adjr) (WhiskerLeft (adjUnit adjl) (leftAdjoint adjr)))
    (adjUnit adjr))
  (VerticalCompose
    (adjCounit adjl)
    (WhiskerLeft
      (WhiskerRight (leftAdjoint adjl) (adjCounit adjr)) (rightAdjoint adjl)))

public export
ComposeAdjunctionCorrect : {c, d, e : MetaCat} ->
  (adjr : Adjunction d e) -> (adjl : Adjunction c d) ->
  AdjunctionCorrect (ComposeAdjunction adjr adjl)
ComposeAdjunctionCorrect {c} {d} {e} adjr adjl = ?ComposeAdjunctionCorrect_hole

public export
LeftAdjunct : {catC, catD : MetaCat} -> (adj : Adjunction catC catD) ->
  {a : MetaObj catD} -> {b : MetaObj catC} ->
  MetaMorphism catC (MetaFunctorObjMap (leftAdjoint adj) a) b ->
  MetaMorphism catD a (MetaFunctorObjMap (rightAdjoint adj) b)
LeftAdjunct {catC} {catD} adj {a} {b} f =
  MetaCompose catD
    a
    (MetaFunctorObjMap
      (rightAdjoint adj) (MetaFunctorObjMap (leftAdjoint adj) a))
    (MetaFunctorObjMap (rightAdjoint adj) b)
    (MetaFunctorMorphMap (rightAdjoint adj) f)
    (MetaNTComponent (adjUnit adj) a)

public export
RightAdjunct : {catC, catD : MetaCat} -> (adj : Adjunction catC catD) ->
  {a : MetaObj catD} -> {b : MetaObj catC} ->
  MetaMorphism catD a (MetaFunctorObjMap (rightAdjoint adj) b) ->
  MetaMorphism catC (MetaFunctorObjMap (leftAdjoint adj) a) b
RightAdjunct {catC} {catD} adj {a} {b} g =
  MetaCompose catC
    (MetaFunctorObjMap (leftAdjoint adj) a)
    (MetaFunctorObjMap
      (leftAdjoint adj) (MetaFunctorObjMap (rightAdjoint adj) b))
    b
    (MetaNTComponent (adjCounit adj) b)
    (MetaFunctorMorphMap (leftAdjoint adj) g)

public export
MetaFunctorCat : MetaCat -> MetaCat -> MetaCat
MetaFunctorCat catC catD =
  MkMetaCat
    (MetaFunctor catC catD)
    MetaNatTrans
    IdNatTrans
    (\f, g, h => VerticalCompose {f} {g} {h})
    MetaFunctorInterp
    MetaNatTransInterp

public export
FunctorCatCorrect : {catC, catD : MetaCat} ->
  MetaCatCorrect catC -> MetaCatCorrect catD ->
  MetaCatCorrect (MetaFunctorCat catC catD)
FunctorCatCorrect {catC} {catD} cC cD = ?FunctorCatCorrect_hole

-- tensor product interpreted as "Either" (in particular for directed colimits)
-- distributive category (with Pair _and_ Either tensor products)
-- functor cat
-- nat trans cat
-- adjunction cat
-- comma cat

-- diagrams

-- A 2-category (or higher) enriched over the metalanguage's `Type`, together
-- with an interpretation into `Type`, with morphism equality defined by
-- (non-recursive) extensional equality of functions.
-- more to it (nat transes, adjunctions)

---------------------------
---------------------------
---- Directed colimits ----
---------------------------
---------------------------

public export
CFunctorIter : {cat : MetaCat} ->
  MetaEndoFunctor cat -> NatObj -> MetaEndoFunctor cat
CFunctorIter f =
  NatObjInd
    (\_ => MetaEndoFunctor cat)
    (IdFunctor cat)
    (\_, f' => ComposeFunctor f f')

public export
CFunctorIterIndBaseCase : {cat : MetaCat} ->
  (MetaEndoFunctor cat -> Type) -> Type
CFunctorIterIndBaseCase {cat} p = p (IdFunctor cat)

public export
CFunctorIterInductionStep : {cat : MetaCat} ->
  (MetaEndoFunctor cat -> Type) -> MetaEndoFunctor cat -> Type
CFunctorIterInductionStep {cat} p f =
  (n : NatObj) ->
  p (CFunctorIter f n) ->
  p (ComposeFunctor f $ CFunctorIter f n)

public export
CFunctorIterInd : {cat : MetaCat} ->
  (0 p : MetaEndoFunctor cat -> Type) ->
  (0 f : MetaEndoFunctor cat) ->
  CFunctorIterIndBaseCase p ->
  CFunctorIterInductionStep p f ->
  (n : NatObj) -> p (CFunctorIter f n)
CFunctorIterInd p f = NatObjInd (p . CFunctorIter f)

public export
MetaFuncInterpPred : {catC, catD : MetaCat} ->
  MetaFunctor catC catD -> MetaObj catC -> Type
MetaFuncInterpPred {catD} f a =
  MetaObjInterp catD (MetaFunctorObjMap f a) -> Type

public export
CFunctorIterInterpPred : {cat : MetaCat} ->
  MetaEndoFunctor cat -> MetaObj cat -> Type
CFunctorIterInterpPred {cat} f a =
  (n : NatObj) -> MetaFuncInterpPred {catC=cat} {catD=cat} (CFunctorIter f n) a

---------------------------------------------------------
---- Coalgebras and coproducts for directed colimits ----
---------------------------------------------------------

----------------------------------------------
----------------------------------------------
---- Polynomial-functor algebra on `Type` ----
----------------------------------------------
----------------------------------------------

--------------------------------------
---- Open terms and labeled trees ----
--------------------------------------

-- For a given functor `F` and object `v`, form the functor `Fv` defined by
-- `Fv[x] = v + F[x]`.  We call it `TermFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing open terms of
-- that datatype with variables drawn from type `v`.
public export
TermFunctor' : (Type -> Type) -> Type -> (Type -> Type)
TermFunctor' f a = CoproductF (ConstF a) f

public export
Functor f => Bifunctor (TermFunctor' f) where
  bimap f' g' (Left x) = Left $ f' x
  bimap f' g' (Right x) = Right $ map g' x

-- For a given functor `F`, form the functor `Fa` defined by
-- `Fa[x] = a * F[x]`.  We call it `TreeFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing potentially infinite
-- trees of that datatype with labels drawn from type `v`.
-- This is the dual of `TermFunctor`.
public export
TreeFunctor' : (Type -> Type) -> Type -> (Type -> Type)
TreeFunctor' f a = ProductF (ConstF a) f

export
Functor f => Bifunctor (TreeFunctor' f) where
  bimap f' g' (x, fx) = (f' x, map g' fx)

-- The free monad of the identity functor.
public export
data FreeMId : Type -> Type where
  InIdVar : {a : Type} -> a -> FreeMId a
  InIdComposite : IdTF (FreeMId a) -> FreeMId a

public export
CoproductAlgTypeNE : (Type -> Type) -> List (Type -> Type) -> Type -> Type
CoproductAlgTypeNE f [] a = Algebra f a
CoproductAlgTypeNE f (f' :: fs) a = (Algebra f a, CoproductAlgTypeNE f' fs a)

public export
CoproductAlgType : List (Type -> Type) -> Type -> Type
CoproductAlgType [] a = Algebra InitialComonad a
CoproductAlgType (f :: fs) a = CoproductAlgTypeNE f fs a

public export
CoproductAlgLNE :
  {f : Type -> Type} -> {l : List (Type -> Type)} -> {a : Type} ->
  CoproductAlgTypeNE f l a -> Algebra (CoproductFLNE f l) a
CoproductAlgLNE {f} {l=[]} alg x = alg x
CoproductAlgLNE {f} {l=(f' :: fs)} (alg, algs) x = case x of
  Left x' => alg x'
  Right x' => CoproductAlgLNE {f=f'} {l=fs} algs x'

public export
CoproductAlgL : {l : List (Type -> Type)} -> {a : Type} ->
  CoproductAlgType l a -> Algebra (CoproductFL l) a
CoproductAlgL {l=[]} algl = \x => void x
CoproductAlgL {l=(f :: fs)} algl = CoproductAlgLNE {f} {l=fs} algl

-----------------------------------
-----------------------------------
---- Godel-numbered categories ----
-----------------------------------
-----------------------------------

--------------------------------
--------------------------------
---- Arrow-category algebra ----
--------------------------------
--------------------------------

-- The components of an object of Idris's arrow category, which is simply a
-- pair of `Type`s with a morphism between them.
public export
record Arrow where
  constructor MkArrow
  arrowTot : Type
  arrowBase : Type
  arrowProj : arrowTot -> arrowBase

-- The components of a morphism in Idris's arrow category.
public export
record ArrowMorphism (a, b : Arrow) where
  constructor MkArrowMorphism
  arrowTotMorphism : arrowTot a -> arrowTot b
  arrowBaseMorphism : arrowBase a -> arrowBase b
  arrowMorphismCommutes :
    ExtEq (arrowProj b . arrowTotMorphism) (arrowBaseMorphism . arrowProj a)

-- The type signature of an arrow functor, which can generate an arrow
-- object from an initial algebra.
public export
record ArrowFunctor where
  constructor ArrowFGen
  arrowBaseChange : Arrow ->
    Type -- change base space
  arrowCobaseChangeOnly : Arrow ->
    Type -- change total space only
  arrowCobaseChangeProj : (a : Arrow) ->
    arrowCobaseChangeOnly a -> arrowBase a
  arrowCobaseChangeDep : (a : Arrow) ->
    (newBase : arrowBaseChange a) -> Type
  arrowProjChange : (a : Arrow) ->
    (newBase : arrowBaseChange a) -> arrowCobaseChangeDep a newBase -> Type

public export
data ArrowTermFunctor : (f : ArrowFunctor) ->
    (v, a : Arrow) -> Type where
  InArrowVar : {f : ArrowFunctor} -> {v, a : Arrow} ->
    (x : arrowTot v) -> ArrowTermFunctor f v a
  InArrowBase : {f : ArrowFunctor} -> {v, a : Arrow} ->
    (base : arrowBaseChange f a) ->
    ArrowTermFunctor f v a
  InArrowCobase : {f : ArrowFunctor} -> {v, a : Arrow} ->
    (tot : arrowCobaseChangeOnly f a) ->
    ArrowTermFunctor f v a
  InArrowBoth : {f : ArrowFunctor} -> {v, a : Arrow} ->
    (newBase : arrowBaseChange f a) ->
    arrowCobaseChangeDep f a newBase ->
    ArrowTermFunctor f v a

{-
mutual
  public export
  FreeArrowTot : (f : ArrowFunctor) -> (a : Arrow) -> Type
  FreeArrowTot f a = FreeArrowTot_hole

  public export
  FreeArrowBase : (f : ArrowFunctor) -> (a : Arrow) -> Type
  FreeArrowBase f a = FreeArrowBase_hole

  public export
  freeArrowProj : (f : ArrowFunctor) -> (a : Arrow) ->
    FreeArrowTot f a -> FreeArrowBase f a
  freeArrowProj f a tot = freeArrowProj_hole

  public export
  data FreeArrowType : ArrowFunctor -> Arrow -> Type where
    InFreeArrow : {f : ArrowFunctor} -> {a : Arrow} ->
      ArrowTermFunctor f a (FreeArrowMonad f a) ->
      FreeArrowType f a

  public export
  FreeArrowMonad : ArrowFunctor -> Arrow -> Arrow
  FreeArrowMonad f a = let type = FreeArrowType f a in FreeArrowMonad_hole
  -}

------------------------------------------
------------------------------------------
---- Polynomial endofunctors in Idris ----
------------------------------------------
------------------------------------------

public export
mapId : {a : Type} -> (x : a) -> map (Prelude.Basics.id {a}) x = x
mapId x = Refl

public export
mapIdTFRefl : (a : Type) ->
  map {f=IdTF} (Prelude.Basics.id {a}) = Prelude.Basics.id {a}
mapIdTFRefl _ = Refl

public export
mapIdTFExtEq : (a : Type) ->
  ExtEq (map {f=IdTF} (Prelude.Basics.id {a})) (Prelude.Basics.id {a})
mapIdTFExtEq a = EqFunctionExt (mapIdTFRefl a)

public export
mapIdTFIdem : (a : Type) ->
  map (map {f=IdTF} (Prelude.Basics.id {a})) =
    map {f=IdTF} (Prelude.Basics.id {a})
mapIdTFIdem _ = Refl

public export
mapIdTFExtIdem : (a : Type) ->
  ExtEq
    (map (map {f=IdTF} (Prelude.Basics.id {a})))
    (map {f=IdTF} (Prelude.Basics.id {a}))
mapIdTFExtIdem a = EqFunctionExt (mapIdTFIdem a)

public export
mapMapIdTFRefl : (a : Type) ->
  map (map {f=IdTF} (Prelude.Basics.id {a})) = Prelude.Basics.id {a}
mapMapIdTFRefl _ = Refl

public export
mapMapIdTFExtEq : (a : Type) ->
  ExtEq (map (map {f=IdTF} (Prelude.Basics.id {a}))) (Prelude.Basics.id {a})
mapMapIdTFExtEq a = EqFunctionExt (mapMapIdTFRefl a)

-- `IdTF` follows the functor laws; this shows that `IdTF` is a
-- functor in the category of the Idris type system.

public export
IdTFunctorialityId : (a : Type) ->
  ExtEq
    (map {f=IdTF} $ Prelude.Basics.id {a})
    (Prelude.Basics.id {a=(IdTF a)})
IdTFunctorialityId _ _ = Refl

public export
IdTFunctorialityCompose : {a, b, c : Type} -> (m : a -> b) -> (m' : b -> c) ->
  ExtEq
    (map {f=IdTF} (m' . m))
    (map {f=IdTF} m' . map {f=IdTF} m)
IdTFunctorialityCompose _ _ _ = Refl

----------------
---- Tuples ----
----------------

public export
TupleF : (natCarrier : Type) -> NatF natCarrier ->
  (carrier : natCarrier -> Type) -> (atom : Type) -> Type
TupleF natCarrier ZeroF carrier = TerminalMonad
TupleF natCarrier (SuccF n) carrier = flip Pair (carrier n)

public export
Tuple : Nat -> Type -> Type
Tuple Z atom = ()
Tuple (S n) atom = PairWithF atom (Tuple n atom)

public export
toTuple : {atom : Type} -> (l : List atom) -> Tuple (length l) atom
toTuple [] = ()
toTuple (x :: xs) = (x, toTuple xs)

public export
foldTuple : {n : Nat} -> {0 a : Type} ->
  (f : b -> a -> b) -> b -> Tuple n a -> b
foldTuple {n} f x t = case n of
  Z => x
  S n' => case t of
    (x', t') => foldTuple f (f x x') t'

public export
sumNTuple : {n : Nat} -> Tuple n Nat -> Nat
sumNTuple = foldTuple (+) 0

public export
TupleProductType : {n : Nat} -> Tuple n Type -> Type
TupleProductType = foldTuple Pair Unit

public export
tupleSumType : {n : Nat} -> Tuple n Type -> Type
tupleSumType = foldTuple Either Void

public export
mapTuple : {n : Nat} -> {0 a : Type} -> (f : a -> b) -> Tuple n a -> Tuple n b
mapTuple {n=Z} f () = ()
mapTuple {n=(S n)} f (x, t) = (f x, mapTuple f {n} t)

public export
(n : Nat) => Functor (Tuple n) where
  map = mapTuple

public export
tupleProj : {n : Nat} -> {atom : Type} -> (i : Nat) -> {auto ok : LT i n} ->
  Tuple n atom -> atom
tupleProj {n=Z} Z {ok} () = void $ succNotLTEzero ok
tupleProj {n=(S n)} Z {ok} (a, t) = a
tupleProj {n=(S n)} (S i) {ok} (a, t) = tupleProj i t {ok=(fromLteSucc ok)}

public export
TupleP : Type -> Type
TupleP = DPair Nat . flip Tuple

public export
TupleIndex : {atom : Type} -> TupleP atom -> Type
TupleIndex (n ** _) = Fin n

public export
TupleElem : {atom : Type} -> (t : TupleP atom) -> TupleIndex {atom} t -> atom
TupleElem {atom} (Z ** _) _ impossible
TupleElem {atom} (S Z ** (x, ())) (FS _) = x
TupleElem {atom} (S (S n) ** (_, _, xs)) (FS (FS i)) = TupleElem (n ** xs) i

public export
mapTupleP : (f : a -> b) -> TupleP a -> TupleP b
mapTupleP f (n ** t) = (n ** mapTuple f t)

-----------------
---- Choices ----
-----------------

public export
ChoiceF : (natCarrier : Type) -> NatF natCarrier ->
  (carrier : natCarrier -> Type) -> (atom : Type) -> Type
ChoiceF natCarrier ZeroF carrier = InitialComonad
ChoiceF natCarrier (SuccF n) carrier = flip Either (carrier n)

public export
Choice : Nat -> Type -> Type
Choice Z atom = Void
Choice (S n) atom = ChoiceBetweenF atom (Choice n atom)

public export
mapChoice : {n : Nat} -> (f : a -> b) -> Choice n a -> Choice n b
mapChoice {n=Z} f v = void v
mapChoice {n=(S n)} f (Left x) = Left (f x)
mapChoice {n=(S n)} f (Right t) = Right (mapChoice f {n} t)

public export
(n : Nat) => Functor (Choice n) where
  map = mapChoice

public export
choiceInj : {n : Nat} -> {atom : Type} -> (i : Nat) -> {auto ok : LT i n} ->
  atom -> Choice n atom
choiceInj {n=Z} Z {ok} a = void $ succNotLTEzero ok
choiceInj {n=(S n)} Z {ok} a = Left a
choiceInj {n=(S n)} (S i) {ok} t = Right $ choiceInj i t {ok=(fromLteSucc ok)}

public export
ChoiceP : Type -> Type
ChoiceP = DPair Nat . flip Choice

-------------------------
---- Lists of tuples ----
-------------------------

public export
TList : Nat -> Type -> Type
TList n atom = Tuple n (TupleP atom)

------------------------------------------
---- S-expressions with fixed arities ----
------------------------------------------

public export
data STuple : {atom : Type} -> (arity : atom -> Nat) -> Type where

-------------------------------------
---- The substitution-0 category ----
-------------------------------------

-- We refer to the category of zeroth-order (non-recursive) non-dependent
-- datatypes as the "substitution-0 category".

public export
Subst0TypeFCases : List (Type -> Type)
Subst0TypeFCases =
  [
    TerminalMonad, -- Unit
    TerminalMonad, -- Void
    ProductMonad, -- Product
    ProductMonad -- Coproduct
  ]

public export
Subst0TypeF : Type -> Type
Subst0TypeF = CoproductFL Subst0TypeFCases

public export
Subst0TypeLimitIter : Type -> Type
Subst0TypeLimitIter = LimitIterF Subst0TypeF

public export
Subst0TypeColimitIter : Type -> Type
Subst0TypeColimitIter = ColimitIterF Subst0TypeF

public export
Subst0TypeAlg : Type -> Type
Subst0TypeAlg = Algebra Subst0TypeF

public export
Subst0TypeCoalg : Type -> Type
Subst0TypeCoalg = Coalgebra Subst0TypeF

public export
MuSubst0Type : Type
MuSubst0Type = Mu Subst0TypeF

public export
NuSubst0Type : Type
NuSubst0Type = Nu Subst0TypeF

public export
FreeSubst0Type : Type -> Type
FreeSubst0Type = FreeMonad Subst0TypeF

public export
CofreeSubst0Type : Type -> Type
CofreeSubst0Type = CofreeComonad Subst0TypeF

-- Parameterized special induction.
public export
subst0TypeCata : ParamCata Subst0TypeF
subst0TypeCata v a subst alg (InFree x) = case x of
  TermVar var => subst var
  TermComposite com => alg $ case com of
    -- Unit
    Left () => Left ()
    Right com' => Right $ case com' of
      -- Void
      Left () => Left ()
      Right com'' => Right $ case com'' of
        -- Product
        Left (p1, p2) =>
          Left
            (subst0TypeCata v a subst alg p1,
             subst0TypeCata v a subst alg p2)
        -- Coproduct
        Right (c1, c2) =>
          Right
            (subst0TypeCata v a subst alg c1,
             subst0TypeCata v a subst alg c2)

-- This algebra interprets the constructors of the substitution-0 category
-- as types in the Idris type system.  This is possible because those
-- types themselves form a category, and there is a faithful functor
-- from the substitution-0 category to that category.  (In other
-- words, the Idris type system contains an initial object, a terminal object,
-- and all products and coproducts, which together inductively comprise all
-- of the objects of the substitution-0 category.)
public export
interpretSubst0Alg : Subst0TypeAlg Type
interpretSubst0Alg = CoproductAlgL {l=Subst0TypeFCases}
  (const (), const Void, ProductAdjunct, CoproductAdjunct)

public export
Subst0Unit : FreeSubst0Type carrier
Subst0Unit = inFreeComposite $ Left ()

public export
Subst0Void : FreeSubst0Type carrier
Subst0Void = inFreeComposite $ Right $ Left ()

public export
Subst0Product :
  FreeSubst0Type carrier -> FreeSubst0Type carrier -> FreeSubst0Type carrier
Subst0Product a b = inFreeComposite $ Right $ Right $ Left (a, b)

public export
Subst0Coproduct :
  FreeSubst0Type carrier -> FreeSubst0Type carrier -> FreeSubst0Type carrier
Subst0Coproduct a b = inFreeComposite $ Right $ Right $ Right (a, b)

public export
data Subst0MorphismF :
    {objCarrier : Type} ->
    (morphCarrier :
      FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier -> Type) ->
    FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier ->
    Type where
  Subst0Id :
    Subst0MorphismF morphCarrier obj obj
  Subst0ToUnit :
    Subst0MorphismF morphCarrier domain Subst0Unit
  Subst0FromVoid :
    Subst0MorphismF morphCarrier Subst0Void codomain
  Subst0TermLeft :
    {objCarrier : Type} -> {a, b, c : FreeSubst0Type objCarrier} ->
    (morphCarrier :
      FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier -> Type) ->
    morphCarrier Subst0Unit a ->
    morphCarrier (Subst0Coproduct a b) c ->
    Subst0MorphismF morphCarrier Subst0Unit c
  Subst0TermRight :
    {objCarrier : Type} -> {a, b, c : FreeSubst0Type objCarrier} ->
    (morphCarrier :
      FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier -> Type) ->
    morphCarrier Subst0Unit b ->
    morphCarrier (Subst0Coproduct a b) c ->
    Subst0MorphismF morphCarrier Subst0Unit c
  Subst0TermPair :
    {objCarrier : Type} -> {a, b, c : FreeSubst0Type objCarrier} ->
    (morphCarrier :
      FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier -> Type) ->
    morphCarrier Subst0Unit a ->
    morphCarrier Subst0Unit b ->
    morphCarrier (Subst0Product a b) c ->
    Subst0MorphismF morphCarrier Subst0Unit c

----------------------------------------
---- The 2x-substitution-0 category ----
----------------------------------------

-- Now we define the types of the product category of the substitution-0
-- category with itself.

----------------------------
---- Refined categories ----
----------------------------

-- 

-- This algebra -- which together with `interpretSubst0Alg` induces
-- a functor in the arrow (sigma) category of the substitution-0 category --
-- generates, for each type generated by `interpretSubst0Alg`, a type
-- of new constraints on those types.
public export
subst0NewConstraintAlg : Subst0TypeAlg Type
subst0NewConstraintAlg = CoproductAlgL {l=Subst0TypeFCases}
  (
    -- The unit type is already as constrained as it can get --
    -- it must have exactly one term.
    const Void,

    -- The void type is already as constrained as it can get --
    -- it must have no terms.
    const Void,

    -- The product type can have either of two constraints:  "must
    -- be equal" and "must be different".
    CoproductAdjunct,

    -- The coproduct type can have either of two constraints:  "must
    -- be left" and "must be right".
    CoproductAdjunct
  )

-- This algebra, given a type of constraints, generates a new
-- type representing compositions of constraints.  Since our constraints
-- are just Boolean predicates, their compositions comprise simply `true`,
-- `false`, `and`, and `or` -- which are isomorphic to the types of
-- the substitution-0 category.  So we can reuse the algebra which
-- _interprets_ objects of the substitution-0 category to _generate_
-- constraint types.  However, we give it a new name because the contexts
-- will be different, and we would like it to be visible in which context
-- this algebra is being used.
subst0ComposeConstraintAlg : Subst0TypeAlg Type
subst0ComposeConstraintAlg = interpretSubst0Alg

public export
record Subst0TypeArrow where
  constructor Subst0Types
  ErasedType : Type
  RefinedType : ErasedType -> Type

public export
data ErasedSubst0TypeF : Subst0TypeArrow -> Type where

public export
data RefinedSubst0TypeF : Subst0TypeArrow -> Type where

--------------------------------------------------------------------
---- The category of zeroth-order Idris polynomial endofunctors ----
--------------------------------------------------------------------

-- This algebra interprets the constructors of the substitution-0 category
-- as functors in the Idris type system.  This is posible because those
-- functors themselves form a category, and there is a faithful functor
-- from the substitution-0 category to that functor category.  (In other
-- words, the functor category contains an initial object, a terminal object,
-- and all products and coproducts, which together inductively comprise all
-- of the objects of the substitution-0 category.)
public export
subst0FunctorAlg : Subst0TypeAlg (Type -> Type)
subst0FunctorAlg = CoproductAlgL {l=Subst0TypeFCases}
  (const TerminalMonad,
   const InitialComonad,
   ProductAdjunctFCat,
   CoproductAdjunctFCat
  )

-- This dependent algebra combines `interpretSubst0Alg` and `Subst0ConstraintF`
-- to create a functor in an arrow category.  (The arrow category is a
-- sub-category of the category of endofunctors on the substitution-0 category.
-- Consequently, it has an initial object in the category of the F-algebras of
-- the functor generated by this dependent algebra, and we will use that initial
-- algebra to define, within the category of all initial algebras of
-- endofunctors of the substitution-0 category, the the object which represents
-- the type of all types of the _refined_ substitution-0 category.)
-- 

-- The functor analogue of `subst0NewConstraintAlg`, as
-- `subst0FunctorAlg` is the functor analogue of `interpretSubst0Alg`.
public export
subst0NewConstraintFunctorAlg : Subst0TypeAlg (Type -> Type)
subst0NewConstraintFunctorAlg = CoproductAlgL {l=Subst0TypeFCases}
  (
    -- The (already-fully-constrained) unit type
    const InitialComonad,

    -- The (already-fully-constrained) void type
    const InitialComonad,

    -- The product type ("must be equal" or "must be different")
    CoproductAdjunctFCat,

    -- The coproduct type ("must be left" or "must be right")
    CoproductAdjunctFCat
  )

----------------------------------------------
---- Category of first-order refined ADTs ----
----------------------------------------------

------------------------------------------------------
------------------------------------------------------
---- Predicates, relations, equivalences in Idris ----
------------------------------------------------------
------------------------------------------------------

--------------------
---- Predicates ----
--------------------

PredicateOn : Type -> Type
PredicateOn type = type -> Type

EmptyPred : (t : Type) -> PredicateOn t
EmptyPred t el = Void

VoidPred : PredicateOn Void
VoidPred v = void v

FullPred : (t : Type) -> PredicateOn t
FullPred t el = ()

UnitPred : PredicateOn Unit
UnitPred = FullPred ()

ProductPred : PredicateOn a -> PredicateOn b -> PredicateOn (a, b)
ProductPred p p' (el, el') = (p el, p' el')

CoproductPred : PredicateOn a -> PredicateOn b -> PredicateOn (Either a b)
CoproductPred p p' (Left el) = p el
CoproductPred p p' (Right el') = p' el'

SubPredicate : {a : Type} -> (sub, super : PredicateOn a) -> Type
SubPredicate {a} sub super = (el : a) -> sub el -> super el

PredEquiv : {a : Type} -> (p, p' : PredicateOn a) -> Type
PredEquiv {a} p p' = (SubPredicate p p', SubPredicate p' p)

PreservesPredicates : {a, b : Type} -> PredicateOn a -> PredicateOn b ->
  (a -> b) -> Type
PreservesPredicates p p' f = (el : a) -> p el -> p' (f el)

PredMorphism : {a, b : Type} -> PredicateOn a -> PredicateOn b -> Type
PredMorphism p p' = DPair (a -> b) (PreservesPredicates p p')

PredFunctor : Type -> Type
PredFunctor t = PredicateOn t -> PredicateOn t

data PredicateTermF : {t: Type} ->
    (f : PredFunctor t) -> (v : PredicateOn t) -> PredFunctor t where
  PredicateVar :
    {t : Type} -> {f : PredFunctor t} ->
    {v, carrier : PredicateOn t} -> {el : t} ->
    v el -> PredicateTermF f {t} v carrier el
  PredicateComposite :
    {t : Type} -> {f : PredFunctor t} ->
    {v, carrier : PredicateOn t} -> {el : t} ->
    f carrier el -> PredicateTermF f v carrier el

data FreeMPredicate :
    {t : Type} -> PredFunctor t -> PredFunctor t where
  InFreePredicate :
    {t : Type} -> {f : PredFunctor t} -> {rel : PredicateOn t} -> {el : t} ->
    PredicateTermF f rel (FreeMPredicate f rel) el ->
    FreeMPredicate f rel el

PredicateMu : {t: Type} -> PredFunctor t -> PredicateOn t
PredicateMu {t} f = FreeMPredicate f $ EmptyPred t

data PredicateTreeF : {t: Type} ->
    (f : PredFunctor t) -> (v : PredicateOn t) -> PredFunctor t where
  PredicateNode :
    {t : Type} -> {f : PredFunctor t} ->
    {v, carrier : PredicateOn t} -> {el : t} ->
    v el -> f carrier el -> PredicateTreeF f v carrier el

data CofreeCMPredicate :
    {t : Type} -> PredFunctor t -> PredFunctor t where
  InCofreePredicate :
    {t : Type} -> {f : PredFunctor t} -> {rel : PredicateOn t} -> {el : t} ->
    Inf (PredicateTreeF f rel (CofreeCMPredicate f rel) el) ->
    CofreeCMPredicate f rel el

PredicateNu : {t: Type} -> PredFunctor t -> PredicateOn t
PredicateNu {t} f = CofreeCMPredicate f $ FullPred t

-------------------
---- Relations ----
-------------------

EmptyRel : (t : Type) -> RelationOn t
EmptyRel t el el' = Void

VoidRel : RelationOn Void
VoidRel v _ = void v

FullRel : (t : Type) -> RelationOn t
FullRel t el el' = ()

UnitRel : RelationOn Unit
UnitRel = FullRel ()

ProductRelation : RelationOn a -> RelationOn b -> RelationOn (a, b)
ProductRelation rel rel' (el1, el1') (el2, el2') = (rel el1 el2, rel' el1' el2')

CoproductRelation : RelationOn a -> RelationOn b -> RelationOn (Either a b)
CoproductRelation rel rel' (Left el1) (Left el2) = rel el1 el2
CoproductRelation rel rel' (Left el1) (Right el2') = Void
CoproductRelation rel rel' (Right el1') (Left el2) = Void
CoproductRelation rel rel' (Right el1') (Right el2') = rel' el1' el2'

SubRelation : {a : Type} -> (sub, super : RelationOn a) -> Type
SubRelation {a} sub super = (el1, el2 : a) -> sub el1 el2 -> super el1 el2

RelationEquiv : {a : Type} -> (r, r' : RelationOn a) -> Type
RelationEquiv r r' = (SubRelation r r', SubRelation r' r)

EqualOverRelations : {a, b : Type} ->
  RelationOn a -> RelationOn b -> (f, g : a -> b) -> Type
EqualOverRelations rel rel' f g =
  (el, el' : a) -> rel el el' -> rel' (f el) (g el')

PreservesRelations : {a, b : Type} ->
  RelationOn a -> RelationOn b -> (a -> b) -> Type
PreservesRelations rel rel' f = EqualOverRelations rel rel' f f

RelMorphism : {a, b : Type} -> RelationOn a -> RelationOn b -> Type
RelMorphism rel rel' = DPair (a -> b) (PreservesRelations rel rel')

RelFunctor : Type -> Type
RelFunctor t = RelationOn t -> RelationOn t

data RelationTermF : {t: Type} ->
    (f : RelFunctor t) -> (v : RelationOn t) -> RelFunctor t where
  RelationVar :
    {t : Type} -> {f : RelFunctor t} ->
    {v, carrier : RelationOn t} -> {el, el' : t} ->
    v el el' -> RelationTermF f {t} v carrier el el'
  RelationComposite :
    {t : Type} -> {f : RelFunctor t} ->
    {v, carrier : RelationOn t} -> {el, el' : t} ->
    f carrier el el' -> RelationTermF f v carrier el el'

data FreeMRelation :
    {t : Type} -> RelFunctor t -> RelFunctor t where
  InFreeRelation :
    {t : Type} -> {f : RelFunctor t} -> {rel : RelationOn t} -> {el, el' : t} ->
    RelationTermF f rel (FreeMRelation f rel) el el' ->
    FreeMRelation f rel el el'

RelationMu : {t: Type} -> RelFunctor t -> RelationOn t
RelationMu {t} f = FreeMRelation f $ EmptyRel t

data RelationTreeF : {t: Type} ->
    (f : RelFunctor t) -> (v : RelationOn t) -> RelFunctor t where
  RelationNode :
    {t : Type} -> {f : RelFunctor t} ->
    {v, carrier : RelationOn t} -> {el, el' : t} ->
    v el el' -> f carrier el el' -> RelationTreeF f v carrier el el'

data CofreeCMRelation :
    {t : Type} -> RelFunctor t -> RelFunctor t where
  InCofreeRelation :
    {t : Type} -> {f : RelFunctor t} -> {rel : RelationOn t} -> {el, el' : t} ->
    Inf (RelationTreeF f rel (CofreeCMRelation f rel) el el') ->
    CofreeCMRelation f rel el el'

RelationNu : {t: Type} -> RelFunctor t -> RelationOn t
RelationNu {t} f = CofreeCMRelation f $ FullRel t

-- Category theory's equalizer, parameterized over a relation on
-- the codomain (which serves as equality on the codomain, allowing
-- the representation of equalizers on types whose equality is not
-- that of the metalanguage (Idris)).
EqualizerRelationGenF : (f, g : a -> b) -> RelationOn b -> RelationOn a
EqualizerRelationGenF f g rel el el' = rel (f el) (g el')

-- Category theory's coequalizer, parameterized over a relation on
-- the domain (which serves as equality on the domain, allowing
-- the representation of coequalizers on types whose equality is not
-- that of the metalanguage (Idris)).
CoequalizerRelationGenF : {a, b: _} ->
  (f, g : a -> b) -> RelationOn a -> RelationOn b
CoequalizerRelationGenF {a} f g rel el el' =
  (elas : (a, a) **
   (rel (fst elas) (snd elas), f (fst elas) = el, g (snd elas) = el'))

----------------------
---- Equivalences ----
----------------------

data EquivGenF : {t : Type} -> RelFunctor t where
  EquivRefl : {t : Type} -> {carrier : RelationOn t} ->
    {el, el' : t} -> el = el' -> EquivGenF carrier el el
  EquivSym : {t : Type} -> {carrier : RelationOn t} -> {el, el' : t} ->
    carrier el el' -> EquivGenF carrier el' el
  EquivTrans : {t : Type} -> {carrier : RelationOn t} ->
    {el, el', el'' : t} ->
    carrier el el' -> carrier el' el'' -> EquivGenF carrier el el''

FreeMEquiv : {t : Type} -> RelFunctor t
FreeMEquiv = FreeMRelation EquivGenF

CofreeCMEquiv : {t : Type} -> RelFunctor t
CofreeCMEquiv = CofreeCMRelation EquivGenF
