module LanguageDef.RefinedADT

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.PolyCat

%default total

------------------------------------------
------------------------------------------
---- Zeroth-order ADTs as polynomials ----
------------------------------------------
------------------------------------------

-----------------------------------------------
---- Algebra formulation with coefficients ----
-----------------------------------------------

public export
record PZPoly where
  constructor MkPZPoly
  -- The maximum power -- whose successor is the number of powers --
  -- in the polynomial
  pzMaxPow : NatObj

  -- The coefficient of each power, or, if the power is the maximum power in
  -- the polynomial and is not zero, the _predecessor_ of the the coefficient
  pzCoeffRep : NatOSlice pzMaxPow -> NatObj

public export
pzPowT : PZPoly -> Type
pzPowT = NatOSlice . pzMaxPow

-- Unless the maximum power is zero, we treat `pzCoeff` of the maximum power
-- as the _predecessor_ of the coefficient.  In other words, we implicitly
-- increment `pzCoeffRep` for the maximum power (and only the maximum power)
-- unless the maximum power is zero.
--
-- The reason we do this is to eliminate representations with leading zeros,
-- and thereby to make equality on polynomials equivalent to structural
-- equality on `PZPoly`.
public export
pzCoeff : (n, i, max : NatObj) -> NatObj
pzCoeff n i max = if i == max && i /= NatOZ then (NatOS n) else n

public export
pzPolyCoeff : (poly : PZPoly) -> pzPowT poly -> NatObj
pzPolyCoeff poly pow = pzCoeff (pzCoeffRep poly pow) (fst pow) (pzMaxPow poly)

public export
Show PZPoly where
  show poly =
    NatObjBoundedMapFold
      {a=(const NatObj)} {b=(const String)} {c=(const String)}
      (const show)
      (pzPolyCoeff poly)
      ""
      (\n', morph, sc, ss =>
        let
          (ss', pow') =
            if n' == NatOZ then
              ("", "")
            else
              (ss ++ " + ", " * n^" ++ show n')
        in
        ss' ++ sc ++ pow')

public export
pzApplyMeta : PZPoly -> Nat -> Nat
pzApplyMeta poly n =
  NatObjBoundedMapFold {a=(const NatObj)} {b=(const Nat)} {c=(const Nat)}
    (const NatObjToMeta)
    (pzPolyCoeff poly)
    Z
    (\pow, lt, coeff, sum => sum + coeff * power n (NatObjToMeta pow))

public export
pzApply : PZPoly -> NatObj -> NatObj
pzApply poly = MetaToNatObj . pzApplyMeta poly . NatObjToMeta

public export
pzSetInitialObj : NatObj
pzSetInitialObj = NatOZ

public export
pzSetTerminalObj : NatObj
pzSetTerminalObj = NatO1

public export
pzPolyInitialObj : PZPoly
pzPolyInitialObj = MkPZPoly NatOZ $ sliceArrayFromList NatOZ []

public export
pzPolyTerminalObj : PZPoly
pzPolyTerminalObj = MkPZPoly NatOZ $ sliceArrayFromList NatO1 []

public export
pzIdentity : PZPoly
pzIdentity = MkPZPoly NatO1 $ sliceArrayFromList NatOZ [NatOZ]

public export
pzIdentityCorrect : (n : NatObj) -> pzApply RefinedADT.pzIdentity n = n
pzIdentityCorrect n = ?pzIdentityCorrect_hole

---------------------------
---- Arena formulation ----
---------------------------

public export
record PZArena where
  constructor MkPZArena
  pzNumPos : NatObj
  pzNumDir : PrefixArray pzNumPos NatObj

public export
pzPosT : PZArena -> Type
pzPosT = NatOPrefix . pzNumPos

public export
pzDirT : (ar : PZArena) -> (pos : pzPosT ar) -> Type
pzDirT ar pos = NatOPrefix (pzNumDir ar pos)

public export
Show PZArena where
  show (MkPZArena n nd) =
    NatObjPrefixMapFold
      {a=(const NatObj)} {b=(const String)} {c=(const String)}
      (const show)
      nd
      "[empty]"
      (\n', morph, sc, ss =>
        let ss' = if n' == NatOZ then "" else ss ++ "; " in
        ss' ++ "#Dirs[" ++ show n' ++ "] = " ++ sc)

public export
OnPosT : PZArena -> PZArena -> Type
OnPosT domain codomain = PrefixMap (pzNumPos domain) (pzNumPos codomain)

public export
OnDirT : {domain, codomain : PZArena} -> OnPosT domain codomain -> Type
OnDirT {domain} {codomain} =
  DepPrefixContraMap
    {domPos=(pzNumPos domain)} {codPos=(pzNumPos codomain)}
    (pzNumDir domain) (pzNumDir codomain)

public export
onDirFromLists : {domain, codomain : PZArena} ->
  (onpos : OnPosT domain codomain) -> List (List Nat) ->
  Maybe (OnDirT {domain} {codomain} onpos)
onDirFromLists {domain} {codomain} =
  depPrefixContraMapFromLists (pzNumDir domain) (pzNumDir codomain)

public export
InitOnDir : {domain, codomain : PZArena} ->
  (onpos : OnPosT domain codomain) -> (l : List (List Nat)) ->
  {auto ok : IsJustTrue (onDirFromLists {domain} {codomain} onpos l)} ->
  OnDirT {domain} {codomain} onpos
InitOnDir _ _ {ok} = fromIsJust ok

public export
record PZLens (domain, codomain : PZArena) where
  constructor MkPZLens
  pzOnPos : OnPosT domain codomain
  pzOnDir : OnDirT {domain} {codomain} pzOnPos

public export
showPZLens : {domain : PZArena} -> {codomain : PZArena} ->
  PZLens domain codomain -> String
showPZLens {domain} {codomain} (MkPZLens op od) =
  "pzOnPos: " ++ showPrefixMap op ++ "; pzOnDir: " ++
  showDepPrefixContraMap (pzNumDir domain) (pzNumDir codomain) op od

public export
pzLensFromLists :
  {domain, codomain : PZArena} ->
  (onpos : OnPosT domain codomain) ->
  List (List Nat) ->
  Maybe (PZLens domain codomain)
pzLensFromLists onpos l with (onDirFromLists onpos l)
  pzLensFromLists onpos l | Just ondir = Just $ MkPZLens onpos ondir
  pzLensFromLists onpos l | Nothing = Nothing

------------------------------------------
---- Algebraic <-> arena translations ----
------------------------------------------

public export
pzSumCoeff : PZPoly -> NatObj
pzSumCoeff poly = natSliceSum (pzPolyCoeff poly)

public export
NatPrefixReplicateMap :
  {n : NatObj} -> (v : SliceArray n NatObj) ->
  (sl : NatOSlice n) -> PrefixArray (v sl) NatObj
NatPrefixReplicateMap {n} v sl = NatPrefixReplicate (v sl) (fst sl)

public export
posPowers : (n : NatObj) ->
  (v : SliceArray n NatObj) ->
  PrefixArray (natSliceSum v) NatObj
posPowers n v = NatPrefixFoldAppend {n} v (NatPrefixReplicateMap {n} v)

public export
pzDirs : (poly : PZPoly) -> NatOPrefix (pzSumCoeff poly) -> NatObj
pzDirs poly = posPowers (pzMaxPow poly) (pzPolyCoeff poly)

public export
pzToArena : PZPoly -> PZArena
pzToArena poly = MkPZArena (pzSumCoeff poly) (pzDirs poly)

-------------------------------
-------------------------------
---- Polynomial categories ----
-------------------------------
-------------------------------

{-
public export
BoundedNatMorphism : NatObj -> NatObj -> Type
BoundedNatMorphism = PrefixMap

public export
BoundedNatId : (n : NatObj) -> BoundedNatMorphism n n
BoundedNatId n = id

public export
BoundedNatCompose :
  {a, b, c : NatObj} ->
  BoundedNatMorphism b c ->
  BoundedNatMorphism a b ->
  BoundedNatMorphism a c
BoundedNatCompose = (.)

public export
BoundedNatInitial : Type
BoundedNatInitial = NatOPrefix NatOZ

public export
BoundedNatFromInitial : (n : NatObj) -> BoundedNatMorphism NatOZ n
BoundedNatFromInitial n (_ ** ltz) = void $ FromLTZeroContra _ ltz

public export
BoundedNatTerminal : Type
BoundedNatTerminal = NatOPrefix NatO1

public export
BoundedNatToTerminal : (n : NatObj) -> BoundedNatMorphism n NatO1
BoundedNatToTerminal n = PrefixArrayConst $ NatOPrefixZ NatOZ

public export
BoundedNatCoproduct : NatObj -> NatObj -> Type
BoundedNatCoproduct m n = NatOPrefix (natObjSum m n)

public export
BoundedNatInjLeft :
  (l, r : NatObj) -> BoundedNatMorphism l (natObjSum l r)
BoundedNatInjLeft dom cod = BoundedNatInjLeft_hole

public export
BoundedNatInjRight :
  (l, r : NatObj) -> BoundedNatMorphism r (natObjSum l r)
BoundedNatInjRight dom cod = BoundedNatInjRight_hole

public export
BoundedNatCase :
  {domL, domR, cod : NatObj} ->
  BoundedNatMorphism domL cod ->
  BoundedNatMorphism domR cod ->
  BoundedNatMorphism (natObjSum domL domR) cod
BoundedNatCase {domL} {domR} {cod} caseL caseR = BoundedNatCase_hole

public export
BoundedNatProduct : NatObj -> NatObj -> Type
BoundedNatProduct m n = NatOPrefix (natObjMul m n)

public export
BoundedNatProjLeft :
  (l, r : NatObj) -> BoundedNatMorphism (natObjMul l r) l
BoundedNatProjLeft dom cod = BoundedNatProjLeft_hole

public export
BoundedNatProjRight :
  (l, r : NatObj) -> BoundedNatMorphism (natObjMul l r) r
BoundedNatProjRight dom cod = BoundedNatProjRight_hole

public export
BoundedNatPair :
  {dom, codL, codR : NatObj} ->
  BoundedNatMorphism dom codL ->
  BoundedNatMorphism dom codR ->
  BoundedNatMorphism dom (natObjMul codL codR)
BoundedNatPair {dom} {codL} {codR} pairL pairR = BoundedNatPair_hole

public export
BoundedNatHomSet : NatObj -> NatObj -> Type
BoundedNatHomSet m n = NatOPrefix (natObjRaiseTo m n)

public export
BoundedNatExponential : NatObj -> NatObj -> Type
BoundedNatExponential = flip BoundedNatHomSet

public export
BoundedNatExponentialCardinality :
  (m, n : NatObj) -> BoundedNatExponential m n = NatOPrefix (natObjPow m n)
BoundedNatExponentialCardinality m n = Refl

public export
BoundedNatEval : (m, n : NatObj) ->
  BoundedNatMorphism (natObjMul (natObjRaiseTo m n) m) n
BoundedNatEval m n = BoundedNatEval_hole

public export
BoundedNatCurry : {m, n, p : NatObj} ->
  BoundedNatMorphism (natObjMul m n) p ->
  BoundedNatMorphism m (natObjRaiseTo n p)
BoundedNatCurry {m} {n} {p} f = BoundedNatCurry_hole
-}

----------------------------------
---- Refined polynomial types ----
----------------------------------

----------------------------------
---- Refined polynomial types ----
----------------------------------

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Polynomials as arenas (following _A General Theory of Interaction_) ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

public export
TypeFamily : Type -> Type
TypeFamily idx = idx -> Type

public export
record Arena where
  constructor MkArena
  pos : Type
  dir : TypeFamily pos

public export
record Lens (domain, codomain : Arena) where
  constructor MkLens
  onPos : (pos domain) -> (pos codomain)
  onDir : (i : pos domain) -> dir codomain (onPos i) -> dir domain i

-------------------------------------------------------------
-------------------------------------------------------------
---- Polynomials in general categories (not just `Type`) ----
-------------------------------------------------------------
-------------------------------------------------------------

public export
record CArena where
  constructor MkCArena
  posCat : MetaCat -- an index category (possibly discrete) of all positions
  dirCat : MetaCat -- a category whose objects can represent sets of directions
  dirFunc : MetaFunctor posCat dirCat

public export
record CLens (domain, codomain : CArena) where
  constructor MkCLens
  cOnPos : MetaFunctor (posCat domain) (posCat codomain)
  cDirDep : MetaFunctor (dirCat domain) (dirCat codomain)
  cOnDir :
    MetaNatTrans
      (ComposeFunctor (dirFunc codomain) cOnPos)
      (ComposeFunctor cDirDep (dirFunc domain))

-------------------------------------------------
-------------------------------------------------
---- Polynomials in terms of natural numbers ----
-------------------------------------------------
-------------------------------------------------

public export
data NatPolyTerm : Type where
  NatCoeffPow : NatObjPair -> NatPolyTerm

public export
Show NatPolyTerm where
  show (NatCoeffPow (c, p)) = show c ++ " * n ^ " ++ show p

public export
natPolyCoeff : NatPolyTerm -> NatObj
natPolyCoeff (NatCoeffPow (c, _)) = c

public export
natPolyPower : NatPolyTerm -> NatObj
natPolyPower (NatCoeffPow (_, p)) = p

public export
NatPolyTermPair : Type
NatPolyTermPair = ProductMonad NatPolyTerm

-- A decidable non-total strict order.
public export
data NatPolyLTP : NatPolyTermPair -> Type where
  NatPolyLTPow : {c, p, c', p' : NatObj} ->
    NatLTStrict p p' -> NatPolyLTP (NatCoeffPow (c, p), NatCoeffPow (c', p'))

public export
decNatPolyLTP : (np : NatPolyTermPair) -> Dec (NatPolyLTP np)
decNatPolyLTP (NatCoeffPow (_, p), NatCoeffPow (_, p')) =
  case NatMorphCompare p p' of
    Left eq => No $ \ltp => case ltp of
      (NatPolyLTPow lt) => case eq of
        Refl => succNotLTEpred $ NatMorphToLTE lt
    (Right (Left ltmn)) => Yes $ NatPolyLTPow ltmn
    (Right (Right ltnm)) => No $ \ltp => case ltp of
      (NatPolyLTPow lt) =>
        let
          ltnm' = NatMorphToLTE ltnm
          lt' = NatMorphToLTE lt
          ltp = NatMorphToLTE $ NatLTSucc p'
        in
        succNotLTEpred $ transitive lt' $ transitive ltp ltnm'

-- A polynomial derived from lists of `(coefficient, power)` pairs.
public export
NatPolyTermList : Type -> Type
NatPolyTermList = ListF NatPolyTerm

public export
NatPolyTermsIter : NatObj -> Type -> Type
NatPolyTermsIter = FunctorIter NatPolyTermList

-----------------------------------------------
-----------------------------------------------
---- Zeroth-order (unrefined) ADT category ----
-----------------------------------------------
-----------------------------------------------

public export
data ADT0ObjF : Type -> Type where
  ADT0Initial : ADT0ObjF carrier
  ADT0Terminal : ADT0ObjF carrier
  ADT0Product : carrier -> carrier -> ADT0ObjF carrier
  ADT0Coproduct : carrier -> carrier -> ADT0ObjF carrier

public export
Functor ADT0ObjF where
  map m ADT0Initial = ADT0Initial
  map m ADT0Terminal = ADT0Terminal
  map m (ADT0Product a b) = ADT0Product (m a) (m b)
  map m (ADT0Coproduct a b) = ADT0Coproduct (m a) (m b)

public export
AlgADT0ObjF : Type -> Type
AlgADT0ObjF = Algebra ADT0ObjF

public export
showADT0FAlg : AlgADT0ObjF String
showADT0FAlg ADT0Initial = "0"
showADT0FAlg ADT0Terminal = "1"
showADT0FAlg (ADT0Product a b) = "(" ++ a ++ " * " ++ b ++ ")"
showADT0FAlg (ADT0Coproduct a b) = "(" ++ a ++ " + " ++ b ++ ")"

public export
Show carrier => Show (ADT0ObjF carrier) where
  show = mapAlg showADT0FAlg show

public export
ADT0ObjChain : NatObj -> Type -> Type
ADT0ObjChain = OmegaChain ADT0ObjF

public export
(n : NatObj) => Functor (ADT0ObjChain n) where
  map {n} m = omegaChainMap {f=ADT0ObjF} m n

public export
(n : NatObj) => Show a => Show (ADT0ObjChain n a) where
  show {n} {a} = omegaChainShow {f=ADT0ObjF} showADT0FAlg n

public export
ADT0ObjColimit : Type -> Type
ADT0ObjColimit = OmegaColimit ADT0ObjF

public export
Functor ADT0ObjColimit where
  map = omegaColimitMap {f=ADT0ObjF}

public export
Show a => Show (ADT0ObjColimit a) where
  show = omegaColimitShow {f=ADT0ObjF} showADT0FAlg

-----------------------------------------------------------
-----------------------------------------------------------
---- Category of non-dependent polynomial endofunctors ----
-----------------------------------------------------------
-----------------------------------------------------------

--------------------------------------
---- Endofunctor-defining functor ----
--------------------------------------

public export
data Subst0EndoF : Type -> Type where
  Subst0EndoCovarRep : carrier -> Subst0EndoF carrier
  Subst0EndoEmpty : Subst0EndoF carrier
  Subst0EndoSum : carrier -> carrier -> Subst0EndoF carrier
  Subst0EndoCompose : carrier -> carrier -> Subst0EndoF carrier

public export
Functor Subst0EndoF where
  map m (Subst0EndoCovarRep f) = Subst0EndoCovarRep (m f)
  map m Subst0EndoEmpty = Subst0EndoEmpty
  map m (Subst0EndoSum f g) = Subst0EndoSum (m f) (m g)
  map m (Subst0EndoCompose g f) = Subst0EndoCompose (m g) (m f)

public export
S0EisF : Functor Subst0EndoF
S0EisF = MkFunctor map

public export
AlgS0EF : Type -> Type
AlgS0EF = Algebra Subst0EndoF

public export
showS0EFAlg : AlgS0EF String
showS0EFAlg (Subst0EndoCovarRep f) = "Hom(" ++ f ++ "[1], _)"
showS0EFAlg Subst0EndoEmpty = "0F"
showS0EFAlg (Subst0EndoSum f g) = "(" ++ f ++ " :+: " ++ g ++ ")"
showS0EFAlg (Subst0EndoCompose g f) = "(" ++ g ++ " . " ++ f ++ ")"

public export
Show carrier => Show (Subst0EndoF carrier) where
  show = mapAlg showS0EFAlg show

public export
interpS0EFAlg : AlgS0EF (Type -> Type)
interpS0EFAlg (Subst0EndoCovarRep fv) x = fv () -> x
interpS0EFAlg Subst0EndoEmpty x = Void
interpS0EFAlg (Subst0EndoSum fv gv) x = Either (fv x) (gv x)
interpS0EFAlg (Subst0EndoCompose gv fv) x = gv $ fv x

-------------------------------------------------------------
---- Natural-number-induction-based endofunctor category ----
-------------------------------------------------------------

public export
S0EIter : NatObj -> Type -> Type
S0EIter = FunctorIter Subst0EndoF

public export
(n : NatObj) => Functor f => Functor (S0EIter n) where
  map {n} = functorIterMap {f=Subst0EndoF} n

public export
(a : Type) => (Show a) => (n : NatObj) => Show (S0EIter n a) where
  show {n} = functorIterShow {f=Subst0EndoF} showS0EFAlg n

public export
S0EStep : Type -> Type
S0EStep = OmegaStep Subst0EndoF

public export
Functor S0EStep where
  map = omegaStepMap {f=Subst0EndoF}

public export
Show a => Show (S0EStep a) where
  show = omegaStepShow {f=Subst0EndoF} showS0EFAlg

public export
S0EChain : NatObj -> Type -> Type
S0EChain = OmegaChain Subst0EndoF

public export
(n : NatObj) => Functor (S0EChain n) where
  map {n} m = omegaChainMap {f=Subst0EndoF} m n

public export
Show a => (n : NatObj) => Show (S0EChain n a) where
  show {n} = omegaChainShow {f=Subst0EndoF} showS0EFAlg n

public export
S0EInitChain : NatObj -> Type
S0EInitChain = InitialChain Subst0EndoF

public export
(n : NatObj) => Show (S0EInitChain n) where
  show {n} = omegaChainShow {f=Subst0EndoF} {a=Void} showS0EFAlg n

public export
S0EColimit : Type -> Type
S0EColimit = OmegaColimit Subst0EndoF

public export
Functor S0EColimit where
  map = omegaColimitMap {f=Subst0EndoF}

public export
(a : Type) => (Show a) => Show (S0EColimit a) where
  show = omegaColimitShow {f=Subst0EndoF} showS0EFAlg

public export
S0EInitColimit : Type
S0EInitColimit = InitialColimit Subst0EndoF

public export
Show S0EInitColimit where
  show = omegaColimitShow {f=Subst0EndoF} {a=Void} showS0EFAlg

public export
FInitAlgS0EF : FInitAlg Subst0EndoF
FInitAlgS0EF Subst0EndoEmpty = colimitConst Subst0EndoEmpty
FInitAlgS0EF (Subst0EndoCovarRep f) = colimitOne Subst0EndoCovarRep f
FInitAlgS0EF (Subst0EndoSum f g) = colimitPair Subst0EndoSum f g
FInitAlgS0EF (Subst0EndoCompose g f) = colimitPair Subst0EndoCompose g f

public export
InitAlgS0EF_Correct : InitAlgCorrect {f=Subst0EndoF} FInitAlgS0EF
InitAlgS0EF_Correct = ?InitAlgS0EF_Correct_hole

public export
interpS0EChain : ChainMapAlgF Subst0EndoF (Type -> Type)
interpS0EChain = chainMapAlgF interpS0EFAlg

public export
interpS0EColimit : ColimitMapAlgF Subst0EndoF (Type -> Type)
interpS0EColimit = colimitMapAlgF interpS0EFAlg

public export
interpS0EInitColimit : S0EInitColimit -> (Type -> Type)
interpS0EInitColimit = colimitCata (Type -> Type) interpS0EFAlg

---------------------------------------------
---- Algebras of polynomial endofunctors ----
---------------------------------------------

public export
FSubst : Type -> Type
FSubst v = v -> Type -> Type

public export
VSubst : FSubst Void
VSubst = voidF (Type -> Type)

public export
interpS0EColimitMapStep : {0 v : Type} -> (fv : FSubst v) ->
  (n : NatObj) ->
  (hyp :
    {0 a, b : Type} ->
    (a -> b) ->
    (c : S0EChain n v) ->
    interpS0EChain v fv n c a ->
    interpS0EChain v fv n c b) ->
  {0 a, b : Type} ->
  (a -> b) ->
  (c : S0EChain (NatOS n) v) ->
  interpS0EChain v fv (NatOS n) c a ->
  interpS0EChain v fv (NatOS n) c b
interpS0EColimitMapStep {a} {b} fv n hyp m (OmegaInj x) =
  hyp m x
interpS0EColimitMapStep {a} {b} fv n hyp m (OmegaIter fx) =
  case fx of
    Subst0EndoCovarRep f' => \hyp => m . hyp
    Subst0EndoEmpty => \v => void v
    Subst0EndoSum f' g' => bimap {f=Either} (hyp m f') (hyp m g')
    Subst0EndoCompose g' f' => hyp (hyp m f') g'

public export
interpS0EColimitMap : {0 v : Type} -> (fv : FSubst v) ->
  (mapv : (x : v) -> {0 a, b : Type} -> fv x a -> fv x b) ->
  {0 a, b : Type} ->
  (f : S0EColimit v) ->
  (a -> b) ->
  interpS0EColimit v fv f a ->
  interpS0EColimit v fv f b
interpS0EColimitMap {v} fv mapv f m =
  ColimitInduction
    (\c =>
      {0 a', b' : Type} -> (a' -> b') ->
      interpS0EColimit v fv c a' -> interpS0EColimit v fv c b')
    (\z, m' =>
      mapv z)
    (\n, hyp, stepn, m' =>
      interpS0EColimitMapStep fv n (\m'', f'' => hyp f'' m'') m' stepn)
    f
    m

public export
interpS0EColimitFunctor :
  {0 v : Type} -> (fv : FSubst v) ->
  (mapv : (x : v) -> {0 a, b : Type} -> fv x a -> fv x b) ->
  (f : S0EColimit v) ->
  Functor (interpS0EColimit v fv f)
interpS0EColimitFunctor fv mapv f = MkFunctor (interpS0EColimitMap fv mapv f)

public export
interpS0EInitColimitFunctor : (f : S0EInitColimit) -> Functor (interpS0EInitColimit f)
interpS0EInitColimitFunctor =
  interpS0EColimitFunctor VSubst (\v => void v)

public export
S0EInterpColimit :
  {v : Type} -> (fv : FSubst v) -> (f : S0EColimit v) -> Type -> Type
S0EInterpColimit {v} fv f = OmegaColimit (interpS0EColimit v fv f)

public export
S0EInterpInitColimit : (f : S0EInitColimit) -> Type -> Type
S0EInterpInitColimit = S0EInterpColimit {v=Void} VSubst

public export
s0EInterpColimitCata :
  {v : Type} -> (fv : FSubst v) ->
  (mapv : (x : v) -> {0 a, b : Type} -> fv x a -> fv x b) ->
  {v', a : Type} ->
  (f : S0EColimit v) ->
  Algebra (interpS0EColimit v fv f) a ->
  (v' -> a) ->
  S0EInterpColimit fv f v' ->
  a
s0EInterpColimitCata {v} fv mapv f =
  colimitMapAlg
    {f=(interpS0EColimit v fv f)} {isF=(interpS0EColimitFunctor fv mapv f)}

public export
s0EInterpInitColimitFreeCata :
  {v', a : Type} ->
  (f : S0EInitColimit) ->
  Algebra (interpS0EInitColimit f) a ->
  (v' -> a) ->
  S0EInterpInitColimit f v' ->
  a
s0EInterpInitColimitFreeCata =
  s0EInterpColimitCata {v=Void} (\v => void v) (\v => void v)

public export
s0EInterpInitColimitCata :
  {a : Type} ->
  (f : S0EInitColimit) ->
  Algebra (interpS0EInitColimit f) a ->
  S0EInterpInitColimit f Void ->
  a
s0EInterpInitColimitCata {a} f alg =
  s0EInterpInitColimitFreeCata {v'=Void} f alg (voidF a)

---------------------------------------------------------------------
---- Morphisms in endofunctor category (natural transformations) ----
---------------------------------------------------------------------

public export
data Subst0EndoNT : MorphFunctor Subst0EndoF where
  Subst0EndoNTInitial :
    {endoCarrier : Type} -> {ntCarrier : MorphCarrier endoCarrier} ->
    (f : Subst0EndoF endoCarrier) ->
    Subst0EndoNT endoCarrier ntCarrier (Subst0EndoEmpty, f)

----------------------------------------
----------------------------------------
---- Representables and polynomials ----
----------------------------------------
----------------------------------------

----------------------------------------------------
---- Representable and corepresentable functors ----
----------------------------------------------------

-- A functor which, given a type of objects and a carrier type of functors,
-- generates a covariant representable functor.
--
-- There is simply one covariant representable functor for each object.
--
-- Examples of representable functors:
--  - The constant functor which takes every object to a terminal object
--    is representable by an initial object
--  - The identity functor is representable by a terminal object
public export
data CovarRepF : Type -> Type -> Type where
  CovarHom : obj -> CovarRepF obj carrier

public export
Bifunctor CovarRepF where
  bimap f g (CovarHom obj) = CovarHom (f obj)

public export
Show obj => Show (CovarRepF obj carrier) where
  show (CovarHom obj) = "Hom(" ++ show obj ++ ", _)"

public export
interpCovarRepF : {obj, carrier : Type} ->
  (obj -> Type) -> CovarRepF obj carrier -> obj -> Type
interpCovarRepF {obj} interpObj (CovarHom x) a =
  interpObj x -> interpObj a

-- A functor which generates a contravariant representable functor.
-- As with covariant representable functors, there's simply one per
-- object -- the only difference between the types is how we interpret
-- them.
public export
data ContravarRepF : Type -> Type -> Type where
  ContravarHom : obj -> ContravarRepF obj carrier

public export
Bifunctor ContravarRepF where
  bimap f g (ContravarHom obj) = ContravarHom (f obj)

public export
Show obj => Show (ContravarRepF obj carrier) where
  show (ContravarHom obj) = "Hom(_, " ++ show obj ++ ")"

public export
interpContravarRepF : {obj, carrier : Type} ->
  (obj -> Type) -> ContravarRepF obj carrier -> obj -> Type
interpContravarRepF {obj} interpObj (ContravarHom x) a =
  interpObj a -> interpObj x

----------------------------------------------------
---- Sums of representables or corepresentables ----
----------------------------------------------------

-- Given a type of objects, a carrier type of representable or corepresentable
-- functors, a generator functor for representable or corepresentable functors,
-- and a carrier type of sums of representables or corepresentables, generate
-- a new type of sums of representables or corepresentables.
public export
data SumRepOrCorepF :
    (Type -> Type -> Type) -> Type -> Type -> Type -> Type where
  SumRepOrCorep :
    ListF (generator obj rep) carrier ->
    SumRepOrCorepF generator obj rep carrier

public export
Functor (SumRepOrCorepF generator obj rep) where
  map f (SumRepOrCorep l) = SumRepOrCorep $ map f l

public export
(Show obj, Show rep, Show carrier, Show (generator obj rep)) =>
    Show (SumRepOrCorepF generator obj rep carrier) where
  show (SumRepOrCorep l) = "Σ" ++ show l

public export
interpSumRepOrCorepF :
  {generator : Type -> Type -> Type} -> {obj, rep, carrier : Type} ->
  (interpObj : obj -> Type) ->
  (interpRep : (obj -> Type) -> generator obj rep -> obj -> Type) ->
  (interpSum : carrier -> obj -> Type) ->
  SumRepOrCorepF generator obj rep carrier -> obj -> Type
interpSumRepOrCorepF interpObj interpRep interpSum (SumRepOrCorep l) a =
  case l of
    NilF => Void
    ConsF r l => Either (interpRep interpObj r a) (interpSum l a)

---------------------------------
---- Polynomial endofunctors ----
---------------------------------

-- A functor which, given types of objects and covariant representables and a
-- carrier type of sums of covariant representables, generates a new type of
-- sums of covariant representables -- that is, polynomial endofunctors.
public export
PolyEndoF : Type -> Type -> Type -> Type
PolyEndoF = SumRepOrCorepF CovarRepF

public export
interpPolyEndoF : {obj, rep, carrier : Type} ->
  (interpObj : obj -> Type) ->
  (interpSum : carrier -> obj -> Type) ->
  PolyEndoF obj rep carrier -> obj -> Type
interpPolyEndoF interpObj interpSum =
  interpSumRepOrCorepF interpObj interpCovarRepF interpSum

--------------------------------
---- Dirichlet endofunctors ----
--------------------------------

-- A functor which, given types of objects and contravariant representables and
-- a carrier type of sums of contravariant representables, generates a new type
-- of sums of contravariant representables -- that is, Dirichlet endofunctors.
public export
DirichletEndoF : Type -> Type -> Type -> Type
DirichletEndoF = SumRepOrCorepF ContravarRepF

public export
interpDirichletEndoF : {obj, rep, carrier : Type} ->
  (interpObj : obj -> Type) ->
  (interpSum : carrier -> obj -> Type) ->
  DirichletEndoF obj rep carrier -> obj -> Type
interpDirichletEndoF interpObj interpSum =
  interpSumRepOrCorepF interpObj interpContravarRepF interpSum

---------------------------------------------------
---- Fixed points (object of all endofunctors) ----
---------------------------------------------------

public export
FreeS0EF : Type -> Type
FreeS0EF = FreeMonad Subst0EndoF

public export
MuS0EF : Type
MuS0EF = Mu Subst0EndoF

public export
pCataS0EF : ParamCata Subst0EndoF
pCataS0EF v a subst alg (InFree x) = case x of
  TermVar var => subst var
  TermComposite com => alg $ case com of
    Subst0EndoCovarRep f => Subst0EndoCovarRep $ pCataS0EF v a subst alg f
    Subst0EndoEmpty => Subst0EndoEmpty
    Subst0EndoSum f g =>
      Subst0EndoSum (pCataS0EF v a subst alg f) (pCataS0EF v a subst alg g)
    Subst0EndoCompose g f =>
      Subst0EndoCompose (pCataS0EF v a subst alg f) (pCataS0EF v a subst alg g)

public export
cataS0EF : Catamorphism Subst0EndoF
cataS0EF = cataFromParam pCataS0EF

public export
showFreeS0EF : {v : Type} -> (v -> String) -> FreeS0EF v -> String
showFreeS0EF subst = pCataS0EF v String subst showS0EFAlg

public export
Show MuS0EF where
  show = cataS0EF String showS0EFAlg

------------------
---- Notation ----
------------------

-- The void-valued constant endofunctor -- the sum of no endofunctors.
public export
(!+) : FreeS0EF v
(!+) = inFreeComposite Subst0EndoEmpty

-- The representable endofunctor represented by a given object -- in the
-- endofunctor category, that is, by some endofunctor, which implicitly
-- means that endofunctor applied to the terminal object.
prefix 11 :>:
public export
(:>:) : FreeS0EF v -> FreeS0EF v
(:>:) a = inFreeComposite $ Subst0EndoCovarRep a

-- The unit-valued constant endofunctor -- represented by the initial object
-- (Void), and hence in the endofunctor category by the void-valued constant
-- endofunctor.
public export
(!*) : FreeS0EF v
(!*) = :>: (!+)

-- The sum of two endofunctors.  (In particular, any sum of representables
-- is a polynomial; so, therefore, is any sum of polynomials.)
infixl 7 :+:
public export
(:+:) : FreeS0EF v -> FreeS0EF v -> FreeS0EF v
a :+: b = inFreeComposite $ Subst0EndoSum a b

-----------------------------------------------------------------------
---- Interpretation of MuS0EF as monoid of polynomial endofunctors ----
-----------------------------------------------------------------------

public export
interpFreeS0EF : {v : Type} -> (v -> Type -> Type) -> FreeS0EF v -> Type -> Type
interpFreeS0EF subst = pCataS0EF v (Type -> Type) subst interpS0EFAlg

public export
interpMuS0EF : MuS0EF -> (Type -> Type)
interpMuS0EF = cataS0EF (Type -> Type) interpS0EFAlg

---------------------------------------------
---- Algebras of polynomial endofunctors ----
---------------------------------------------

public export
AlgS0E : MuS0EF -> Type -> Type
AlgS0E = Algebra . interpMuS0EF

public export
FreeS0E : MuS0EF -> Type -> Type
FreeS0E = FreeMonad . interpMuS0EF

public export
MuS0E : MuS0EF -> Type
MuS0E = Mu . interpMuS0EF

-------------------------------------------------------------
-------------------------------------------------------------
---- Unrefined zero-order category ("assembly language") ----
-------------------------------------------------------------
-------------------------------------------------------------

public export
data FinSubstF : Type -> Type where
  FSVoid : FinSubstF carrier
  FSUnit : FinSubstF carrier
  FSCoproduct : carrier -> carrier -> FinSubstF carrier
  FSHomObj : carrier -> carrier -> FinSubstF carrier

public export
Functor FinSubstF where
  map f FSVoid = FSVoid
  map f FSUnit = FSUnit
  map f (FSCoproduct a b) = FSCoproduct (f a) (f b)
  map f (FSHomObj a b) = FSHomObj (f a) (f b)

public export
showFSF : {0 carrier : Type} ->
  (carrier -> String) -> FinSubstF carrier -> String
showFSF s FSVoid = show 0
showFSF s FSUnit = show 1
showFSF s (FSCoproduct a b) = "(" ++ s a ++ " + " ++ s b ++ ")"
showFSF s (FSHomObj a b) = "(" ++ s a ++ " -> " ++ s b ++ ")"

public export
Show carrier => Show (FinSubstF carrier) where
  show = showFSF show

public export
data FinSubstObj : Type where
  InFS : FinSubstF FinSubstObj -> FinSubstObj

public export
FinSubstAlg : Type -> Type
FinSubstAlg a = FinSubstF a -> a

public export
cataFS : {a : Type} -> FinSubstAlg a -> FinSubstObj -> a
cataFS alg (InFS x) = alg $ case x of
  FSVoid => FSVoid
  FSUnit => FSUnit
  FSCoproduct a b => FSCoproduct (cataFS alg a) (cataFS alg b)
  FSHomObj a b => FSHomObj (cataFS alg a) (cataFS alg b)

public export
showFSAlg : FinSubstAlg String
showFSAlg = showFSF id

public export
showFS : FinSubstObj -> String
showFS = cataFS showFSAlg

public export
Show FinSubstObj where
  show = showFS

public export
interpFinSubstF : {obj, carrier : Type} ->
  (interpObj : obj -> Type) ->
  (interpCarrier : carrier -> obj -> Type) ->
  FinSubstF carrier -> obj -> Type
interpFinSubstF interpObj interpCarrier FSVoid a =
  Void
interpFinSubstF interpObj interpCarrier FSUnit a =
  Unit
interpFinSubstF interpObj interpCarrier (FSCoproduct x y) a =
  Either (interpCarrier x a) (interpCarrier y a)
interpFinSubstF interpObj interpCarrier (FSHomObj x y) a =
  interpCarrier x a -> interpCarrier y a

-------------------------------------------------
-------------------------------------------------
---- Substitution category from endofunctors ----
-------------------------------------------------
-------------------------------------------------

----------------------------------
----------------------------------
---- Geb term representations ----
----------------------------------
----------------------------------

public export
data RepresentationF : (repCarrier : Type) -> Type where

public export
data InterpTypeF : {repCarrier : Type} ->
    (interpTypeCarrier : repCarrier -> Type) ->
    RepresentationF repCarrier -> Type where

public export
data ErrorTypeF : {repCarrier : Type} ->
    (errorTypeCarrier : repCarrier -> Type) ->
    RepresentationF repCarrier -> Type where

public export
checkRepF :
  {repCarrier : Type} ->
  {interpTypeCarrier : repCarrier -> Type} ->
  {errorTypeCarrier : repCarrier -> Type} ->
  (checkCarrier :
    (rep : repCarrier) ->
      Either
        (interpTypeCarrier rep)
        (errorTypeCarrier rep)) ->
  (repF : RepresentationF repCarrier) ->
    Either
      (InterpTypeF interpTypeCarrier repF)
      (ErrorTypeF errorTypeCarrier repF)
checkRepF checkCarrier rep impossible

-----------------------------------------
-----------------------------------------
---- Attempt at big mutual recursion ----
-----------------------------------------
-----------------------------------------

public export
data GebTypeFamily : Type where
  GEB_HIGHER_CATEGORY : GebTypeFamily
  GEB_CATEGORY : GebTypeFamily
  GEB_OBJECT : GebTypeFamily
  GEB_MORPHISM : GebTypeFamily
  GEB_POLY_ENDOFUNCTOR : GebTypeFamily
  GEB_DIRICHLET_ENDOFUNCTOR : GebTypeFamily
  GEB_FUNCTOR : GebTypeFamily
  GEB_CARTESIAN_TRANS : GebTypeFamily
  GEB_NAT_TRANS : GebTypeFamily
  GEB_ADJUNCTION : GebTypeFamily

public export
GebCarrier : GebTypeFamily -> Type
GebCarrier GEB_HIGHER_CATEGORY = Type
GebCarrier GEB_CATEGORY = Type
GebCarrier GEB_OBJECT = {cat : Type} -> cat -> Type
GebCarrier GEB_MORPHISM = {obj : Type} -> obj -> obj -> Type
GebCarrier GEB_POLY_ENDOFUNCTOR = {cat : Type} -> cat -> Type
GebCarrier GEB_DIRICHLET_ENDOFUNCTOR = {cat : Type} -> cat -> Type
GebCarrier GEB_FUNCTOR = {cat : Type} -> cat -> cat -> Type
GebCarrier GEB_CARTESIAN_TRANS = {functor : Type} -> functor -> functor -> Type
GebCarrier GEB_NAT_TRANS = {functor : Type} -> functor -> functor -> Type
GebCarrier GEB_ADJUNCTION = {functor : Type} -> functor -> functor -> Type

----------------------------------------------------
----------------------------------------------------
---- Endofunctors of unrefined 0-order category ----
----------------------------------------------------
----------------------------------------------------

public export
FinSubstSig : Type
FinSubstSig = (FinSubstObj, FinSubstObj)

public export
FinSubstMorphType : Type
FinSubstMorphType = FinSubstSig -> Type

public export
data FinSubstMorphF : FinSubstMorphType -> FinSubstMorphType where
  FSMFromVoid : {carrier : FinSubstMorphType} -> {codomain : FinSubstObj} ->
    FinSubstMorphF carrier (InFS FSVoid, codomain)
  FSMToUnit : {carrier : FinSubstMorphType} -> {domain : FinSubstObj} ->
    FinSubstMorphF carrier (domain, InFS FSUnit)
  FSMCase : {carrier : FinSubstMorphType} ->
    {domain, domain', codomain : FinSubstObj} ->
    carrier (domain, codomain) -> carrier (domain', codomain) ->
    FinSubstMorphF carrier (InFS $ FSCoproduct domain domain', codomain)
  FSMMorphTerm : {carrier : FinSubstMorphType} ->
    {domain, codomain : FinSubstObj} ->
    carrier (domain, codomain) ->
    FinSubstMorphF carrier (InFS FSUnit, InFS $ FSHomObj domain codomain)

public export
data FinSubstMorph : FinSubstMorphType where
  InFSM : {sig : FinSubstSig} ->
    FinSubstMorphF FinSubstMorph sig -> FinSubstMorph sig

public export
FinSubstMorphAlg : (a : FinSubstSig -> Type) -> Type
FinSubstMorphAlg a = {sig : FinSubstSig} -> FinSubstMorphF a sig -> a sig

{-
public export
cataFSM : {a : FinSubstSig -> Type} ->
  FinSubstMorphAlg a -> {sig : FinSubstSig} -> FinSubstMorph sig -> a sig
cataFSM {a} alg (InFSM m) = alg $ case m of
  FSMFromVoid => FSMFromVoid
  FSMToUnit => FSMToUnit
  FSMCase x y => FSMCase (cataFSM alg x) (cataFSM alg y)
  FSMMorphTerm f => FSMMorphTerm (cataFSM alg f)

public export
showFSMAlg : FinSubstMorphAlg (const String)
showFSMAlg {sig=(InFS FSVoid, codomain)} FSMFromVoid = "(void->" ++ show codomain ++ ")"
showFSMAlg {sig=(domain, InFS FSUnit)} FSMToUnit = "(" ++ show domain ++ "->unit)"
showFSMAlg (FSMMorphTerm f) = "('" ++ show f ++ "')"
showFSMAlg (FSMCase x y) = "('" ++ show x ++ " :+: " ++ show y ++ "')"

public export
showFSM : {sig : FinSubstSig} -> FinSubstMorph sig -> String
showFSM = cataFSM showFSMAlg

public export
(sig : FinSubstSig) => Show (FinSubstMorph sig) where
  show = showFSM
  -}

{-
public export
data TermFinSubstF : Type -> Type -> Type where
  TFSVar : var -> TermFinSubstF var carrier
  TFSComposite : FinSubstF carrier -> TermFinSubstF var carrier

public export
TermFinSubstAlg : Type -> Type -> Type
TermFinSubstAlg var a = TermFinSubstF var a -> a

public export
(Show var, Show carrier) => Show (TermFinSubstF var carrier) where
  show (TFSVar v) = show "(v = " ++ show v ++ ")"
  show (TFSComposite com) = show "(com = " ++ show com ++ ")"

public export
termFinSubstShowAlg : Show var => TermFinSubstAlg var String
termFinSubstShowAlg = show

public export
data FreeFinSubst : Type -> Type where
  FSIn : TermFinSubstF var (FreeFinSubst var) -> FreeFinSubst var

public export
cataFinSubst : {var, a : Type} -> TermFinSubstAlg var a -> FreeFinSubst var -> a
cataFinSubst {var} {a} alg (FSIn x) = alg $ case x of
  TFSVar v => TFSVar v
  TFSComposite com => TFSComposite $ case com of
    FSVoid => FSVoid
    FSUnit => FSUnit
    FSProduct a b => FSProduct (cataFinSubst alg a) (cataFinSubst alg b)
    FSCoproduct a b => FSCoproduct (cataFinSubst alg a) (cataFinSubst alg b)
    FSHomObj a b => FSHomObj (cataFinSubst alg a) (cataFinSubst alg b)

public export
(var : Type) => Show var => Show (FreeFinSubst var) where
  show = cataFinSubst termFinSubstShowAlg

public export
data FinSubstMorphF : {var : Type} ->
    (carrier : FreeFinSubst var -> FreeFinSubst var -> Type) ->
    FreeFinSubst var -> FreeFinSubst var -> Type where
  FSFromVoid : {b : FreeFinSubst var} ->
    FinSubstMorphF carrier (FSIn (TFSComposite FSVoid)) b
  FSToUnit : {a : FreeFinSubst var} ->
    FinSubstMorphF carrier a (FSIn (TFSComposite FSUnit))
    -}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- Natural numbers:  finitary Robinson and elementary-function arithmetic ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Robinson number.
public export
data RNatF : Type -> Type where
  RNat0 : RNatF carrier
  RNat1 : RNatF carrier
  RNatSum : carrier -> carrier -> RNatF carrier
  RNatProduct : carrier -> carrier -> RNatF carrier

public export
Functor RNatF where
  map f RNat0 = RNat0
  map f RNat1 = RNat1
  map f (RNatSum m n) = RNatSum (f m) (f n)
  map f (RNatProduct m n) = RNatProduct (f m) (f n)

public export
RNatAlg : Type -> Type
RNatAlg = Algebra RNatF

public export
RNatCoalg : Type -> Type
RNatCoalg = Coalgebra RNatF

public export
TermRNat : Type -> Type -> Type
TermRNat = TermFunctor RNatF

public export
TreeRNat : Type -> Type -> Type
TreeRNat = TreeFunctor RNatF

public export
LimitRNat : Type -> Type
LimitRNat = LimitIterF RNatF

public export
ColimitRNat : Type -> Type
ColimitRNat = ColimitIterF RNatF

public export
TRNat0 : TermRNat v a
TRNat0 = TermComposite RNat0

public export
TRNat1 : TermRNat v a
TRNat1 = TermComposite RNat1

public export
TRNatSum : a -> a -> TermRNat v a
TRNatSum m n = TermComposite (RNatSum m n)

public export
TRNatProduct : a -> a -> TermRNat v a
TRNatProduct m n = TermComposite (RNatProduct m n)

public export
FreeRNatF : Type -> Type
FreeRNatF = FreeMonad RNatF

public export
CofreeRNatF : Type -> Type
CofreeRNatF = CofreeComonad RNatF

public export
MuRNatF : Type
MuRNatF = Mu RNatF

public export
NuRNatF : Type
NuRNatF = Nu RNatF

public export
cataRNatF : ParamCata RNatF
cataRNatF v a subst alg (InFree x) = case x of
  TermVar var => subst var
  TermComposite n => alg $ case n of
    RNat0 => RNat0
    RNat1 => RNat1
    RNatSum m n =>
      RNatSum (cataRNatF v a subst alg m) (cataRNatF v a subst alg n)
    RNatProduct m n =>
      RNatProduct (cataRNatF v a subst alg m) (cataRNatF v a subst alg n)

public export
interpRNatFAlg : RNatAlg Nat
interpRNatFAlg RNat0 = 0
interpRNatFAlg RNat1 = 1
interpRNatFAlg (RNatSum m n) = m + n
interpRNatFAlg (RNatProduct m n) = m * n

public export
interpFreeRNatF : {v : Type} -> (subst : v -> Nat) -> FreeRNatF v -> Nat
interpFreeRNatF {v} subst = cataRNatF v Nat subst interpRNatFAlg

public export
interpMuRNatF : MuRNatF -> Nat
interpMuRNatF = interpFreeRNatF {v=Void} (voidF Nat)

public export
data ENatF : Type -> Type where
  ENatR : RNatF carrier -> ENatF carrier
  ENatExp : carrier -> carrier -> ENatF carrier

public export
ENatAlg : Type -> Type
ENatAlg = Algebra ENatF

public export
ENatCoalg : Type -> Type
ENatCoalg = Coalgebra ENatF

public export
FreeENatF : Type -> Type
FreeENatF = FreeMonad ENatF

public export
CofreeENatF : Type -> Type
CofreeENatF = CofreeComonad ENatF

public export
MuENatF : Type
MuENatF = Mu ENatF

public export
NuENatF : Type
NuENatF = Nu ENatF

public export
cataENatF : ParamCata ENatF
cataENatF v a subst alg (InFree x) = case x of
  TermVar var => subst var
  TermComposite n => alg $ case n of
    ENatR n => ENatR $ case n of
      RNat0 => RNat0
      RNat1 => RNat1
      RNatSum m' n' =>
        RNatSum (cataENatF v a subst alg m') (cataENatF v a subst alg n')
      RNatProduct m' n' =>
        RNatProduct (cataENatF v a subst alg m') (cataENatF v a subst alg n')
    ENatExp m n =>
      ENatExp (cataENatF v a subst alg m) (cataENatF v a subst alg n)

public export
interpENatFAlg : ENatAlg Nat
interpENatFAlg (ENatR n) = interpRNatFAlg n
interpENatFAlg (ENatExp m n) = power m n

public export
interpFreeENatF : {v : Type} -> (subst : v -> Nat) -> FreeENatF v -> Nat
interpFreeENatF {v} subst = cataENatF v Nat subst interpENatFAlg

public export
interpMuENatF : MuENatF -> Nat
interpMuENatF = interpFreeENatF {v=Void} (voidF Nat)

public export
data FOrder : Type where
  OrderN : Nat -> FOrder
  OrderHigh : FOrder
  OrderComplete : FOrder

public export
Eq FOrder where
  (==) (OrderN m) (OrderN n) = m == n
  (==) OrderHigh OrderHigh = True
  (==) OrderComplete OrderComplete = True
  (==) _ _ = False

public export
Ord FOrder where
  (<) (OrderN m) (OrderN n) = m < n
  (<) (OrderN _) OrderHigh = True
  (<) (OrderN _) OrderComplete = True
  (<) OrderHigh OrderComplete = True
  (<) _ _ = False

--------------------------------------------------------------------------
--------------------------------------------------------------------------
---- Category of ranges of natural numbers with order-preserving maps ----
--------------------------------------------------------------------------
--------------------------------------------------------------------------

public export
record FinNERangeObj where
  constructor MkFinRange
  frStart : Nat
  frPredLength : Nat

public export
finNERangeLast : FinNERangeObj -> Nat
finNERangeLast (MkFinRange s pl) = pl + s

public export
finNERangeLength : FinNERangeObj -> Nat
finNERangeLength = S . frPredLength

public export
Show FinNERangeObj where
  show r =
    "[" ++ show (frStart r) ++ ".." ++ show (finNERangeLast r) ++ "](" ++
    show (finNERangeLength r) ++ ")"

public export
Eq FinNERangeObj where
  (==) (MkFinRange s1 pl1) (MkFinRange s2 pl2) =
    s1 == s2 && pl1 == pl2

public export
Ord FinNERangeObj where
  compare (MkFinRange s1 pl1) (MkFinRange s2 pl2) =
    case compare s1 s2 of
      EQ => compare pl1 pl2
      LT => LT
      GT => GT

public export
boundedBelow : Nat -> List Nat -> Type
boundedBelow min [] = ()
boundedBelow min (x :: xs) = (LTE min x, boundedBelow min xs)

public export
boundedAbove : Nat -> List Nat -> Type
boundedAbove max [] = ()
boundedAbove max (x :: xs) = (LTE x max, boundedAbove max xs)

public export
ordered : List Nat -> Type
ordered [] = ()
ordered [x] = ()
ordered (x :: x' :: xs) = (LTE x x', ordered (x' :: xs))

public export
boundedBelowSucc : {n : Nat} -> {l : List Nat} ->
  boundedBelow (S n) l -> boundedBelow n l
boundedBelowSucc {l=[]} _ = ()
boundedBelowSucc {l=(x :: xs)} (b, bs) = (lteSuccLeft b, boundedBelowSucc bs)

public export
record ListIsBoundedAndOrdered (predLen, start : Nat) (l : List Nat) where
  constructor BoundedOrderedListConditions
  validLength : length l = S predLen
  validLower : boundedBelow start l
  validUpper : boundedAbove (predLen + start) l
  validOrder : ordered l

public export
validIncList : (predLen : Nat) -> (start : Nat) ->
  (l : List Nat ** ListIsBoundedAndOrdered predLen start l)
validIncList Z s =
  ([s] **
   BoundedOrderedListConditions
    Refl
    (reflexive, ())
    (reflexive, ())
    ())
validIncList (S pl) s with (validIncList pl (S s))
  validIncList (S pl) s |
    (l ** BoundedOrderedListConditions validLen below above ord) =
      (s :: l **
       BoundedOrderedListConditions
        (cong S validLen)
        (reflexive, boundedBelowSucc below)
        (lteSuccRight $ lteAddLeft pl s,
         rewrite plusSuccRightSucc pl s in above)
        (case l of
          [] => ()
          x :: xs => (lteSuccLeft $ fst below, ord)))

public export
incList : (predLen : Nat) -> (start : Nat) -> List Nat
incList predLen start = fst $ validIncList predLen start

public export
incListLen :
  (predLen : Nat) -> (start : Nat) -> length (incList predLen start) = S predLen
incListLen predLen start = validLength $ snd $ validIncList predLen start

public export
incListBoundedBelow : (predLen : Nat) -> (start : Nat) ->
  boundedBelow start (incList predLen start)
incListBoundedBelow predLen start =
  validLower $ snd $ validIncList predLen start

public export
incListBoundedAbove : (predLen : Nat) -> (start : Nat) ->
  boundedAbove (predLen + start) (incList predLen start)
incListBoundedAbove predLen start =
  validUpper $ snd $ validIncList predLen start

public export
incListOrdered : (predLen : Nat) -> (start : Nat) ->
  ordered (incList predLen start)
incListOrdered predLen start =
  validOrder $ snd $ validIncList predLen start

public export
record FinNERangeMorph where
  constructor MkFinNERangeMorph
  frDomain : FinNERangeObj
  frCodomain : FinNERangeObj
  frMap : List Nat

public export
record FinNERangeMorphIsValid (morph : FinNERangeMorph) where
  constructor FinNERangeMorphConditions
  frValidLen : length morph.frMap = (finNERangeLength morph.frDomain)
  frBoundedBelow : boundedBelow (frStart morph.frCodomain) morph.frMap
  frBoundedAbove : boundedAbove (finNERangeLast morph.frCodomain) morph.frMap
  frOrdered : ordered morph.frMap

public export
ValidFinNERangeMorph : Type
ValidFinNERangeMorph = DPair FinNERangeMorph FinNERangeMorphIsValid

public export
Show FinNERangeMorph where
  show (MkFinNERangeMorph dom cod map) =
    "[" ++ show dom ++ "->" ++ show cod ++ ":" ++ show map ++ "]"

public export
Eq FinNERangeMorph where
  (==)
    (MkFinNERangeMorph dom1 cod1 map1)
    (MkFinNERangeMorph dom2 cod2 map2) =
      dom1 == dom2 && cod1 == cod2 && map1 == map2

public export
Ord FinNERangeMorph where
  compare
    (MkFinNERangeMorph dom1 cod1 map1)
    (MkFinNERangeMorph dom2 cod2 map2) =
      case compare dom1 dom2 of
        EQ => case compare cod1 cod2 of
          EQ => compare map1 map2
          LT => LT
          GT => GT
        LT => LT
        GT => GT

public export
finNERangeId : FinNERangeObj -> ValidFinNERangeMorph
finNERangeId r@(MkFinRange s pl) =
  (MkFinNERangeMorph r r (incList pl s) **
   (FinNERangeMorphConditions
    (incListLen pl s)
    (incListBoundedBelow pl s)
    (incListBoundedAbove pl s)
    (incListOrdered pl s)))

public export
Composable : FinNERangeMorph -> FinNERangeMorph -> Type
Composable g f = g.frDomain = f.frCodomain

{-
public export
composeFinNERange :
  (g, f : ValidFinNERangeMorph) ->
  Composable g.fst f.fst ->
  (gf : ValidFinNERangeMorph **
   (gf.fst.frDomain = f.fst.frDomain,
    gf.fst.frCodomain = g.fst.frCodomain))
composeFinNERange g f c with (f.fst.frMap) proof pf
  composeFinNERange g f c | [] =
    let
      vl = f.snd.frValidLen
      vl' = replace {p=(\x => length x = finNERangeLength f.fst.frDomain)} pf vl
    in
    case vl' of Refl impossible
  composeFinNERange g f c | (i :: l) = composeFinNERange_hole
  -}

---------------------------------------------------
---------------------------------------------------
---- Simplex (augmented/algebraist's) category ----
---------------------------------------------------
---------------------------------------------------

----------------------------------
---- Simplex category objects ----
----------------------------------

-- The finite ordinal of the size equal to the natural number
-- that represents it.  We will treat it as an object of the
-- "augmented" or "algebraist's" version of the "simplex category",
-- known as `FinOrd`.  It is the category whose objects are finite ordinals
-- and whose morphisms are order-preserving maps.
--
-- Thus, 0 represents empty, and for all `n`, `S n` represents
-- [0..n] inclusive.
public export
FinOrdObj : Type
FinOrdObj = Nat

------------------------------------
---- Simplex category morphisms ----
------------------------------------

-- A representation of an order-preserving mapping from the ranges of natural
-- numbers [m..n] -> [m'..n'] (inclusive).
public export
data NatRangeMap : (m, n, m', n' : Nat) -> Type where
  NatRangeMapOne : (m, m', n', i : Nat) ->
    {auto mlti : LTE m' i} -> {auto iltn : LTE i n'} ->
    NatRangeMap m m m' n'
  NatRangeMapMulti : (m, n, m', n', i : Nat) ->
    {auto mltn : LT m n} ->
    {auto mlti : LTE m' i} -> {auto iltn : LTE i n'} ->
    NatRangeMap (S m) n i n' ->
    NatRangeMap m n m' n'

public export
natRangeToList : {0 m, n, m', n' : Nat} -> NatRangeMap m n m' n' -> List Nat
natRangeToList (NatRangeMapOne _ _ _ i) = [i]
natRangeToList (NatRangeMapMulti _ _ _ _ i rmap) = i :: natRangeToList rmap

public export
Show (NatRangeMap m n m' n') where
  show (NatRangeMapOne m m' n' i) =
    show m ++ "/" ++ show m ++ "->" ++ show i ++ "/" ++ show n'
  show (NatRangeMapMulti m n m' n' i rmap) =
    show m ++ "/" ++ show n ++ "->" ++ show i ++ "/" ++ show n' ++ ", " ++
    show rmap

public export
listToNatRange :
  (m, n, m', n' : Nat) -> Nat -> List Nat -> Maybe (NatRangeMap m n m' n')
listToNatRange m n m' n' i [] =
  case (decEq m n, isLTE m' i, isLTE i n') of
    (Yes Refl, Yes _, Yes _) => Just (NatRangeMapOne m m' n' i)
    (_, _) => Nothing
listToNatRange m n m' n' i (i' :: is) =
  case (isLT m n, isLTE m' i, isLTE i n', listToNatRange (S m) n i n' i' is) of
    (Yes _, Yes _, Yes _, Just rmap) => Just (NatRangeMapMulti m n m' n' i rmap)
    (_, _, _) => Nothing

public export
MkNatRange : (m, n, m', n', i : Nat) -> (l : List Nat) ->
  {auto valid : isJust (listToNatRange m n m' n' i l) = True} ->
  NatRangeMap m n m' n'
MkNatRange m n m' n' i l {valid} with (listToNatRange m n m' n' i l)
  MkNatRange m n m' n' i l {valid=Refl} | Just rng = rng
  MkNatRange m n m' n' i l {valid=Refl} | Nothing impossible

public export
natRangeLeftBounds : NatRangeMap m n m' n' -> LTE m n
natRangeLeftBounds (NatRangeMapOne _ _ _ _) = reflexive
natRangeLeftBounds (NatRangeMapMulti {mltn} _ _ _ _ _ _) = lteSuccLeft mltn

public export
natRangeRightBounds : NatRangeMap m n m' n' -> LTE m' n'
natRangeRightBounds (NatRangeMapOne {mlti} {iltn} _ _ _ _) =
  transitive mlti iltn
natRangeRightBounds (NatRangeMapMulti {mlti} {iltn} _ _ _ _ _ _) =
  transitive mlti iltn

public export
natRangeExtendCodomainBelow : NatRangeMap m n (S m') n' -> NatRangeMap m n m' n'
natRangeExtendCodomainBelow
  (NatRangeMapOne m (S m') n' i {mlti} {iltn}) =
    NatRangeMapOne
      m m' n' i
      {mlti=(lteSuccLeft mlti)}
      {iltn}
natRangeExtendCodomainBelow
  (NatRangeMapMulti m n (S m') n' i {mltn} {mlti} {iltn} nrm) =
    NatRangeMapMulti
      m n m' n' i nrm
      {mltn}
      {mlti=(lteSuccLeft mlti)}
      {iltn}

-- A diagonally-increasing mapping from [n..i+n] to [n..i+n].
public export
natRangeId : (n, i : Nat) -> NatRangeMap n (i + n) n (i + n)
natRangeId n 0 = NatRangeMapOne n n n n {mlti=reflexive} {iltn=reflexive}
natRangeId n (S i) =
  let ialn = lteAddLeft i n in
  NatRangeMapMulti
    n (S i + n) n (S i + n) n
    {mltn=(LTESucc ialn)}
    {mlti=reflexive}
    {iltn=(lteSuccRight ialn)}
    $
    rewrite plusSuccRightSucc i n in
    natRangeExtendCodomainBelow $ natRangeId (S n) i

public export
natRangeEval : {m, n, m', n' : Nat} -> NatRangeMap m n m' n' -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} -> Nat
natRangeEval (NatRangeMapOne _ _ _ i') _ = i'
natRangeEval {mlti} {iltn}
  (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i =
    case decEq m i of
      Yes Refl => i'
      No neq => natRangeEval rng i {mlti=(lteTolt mlti neq)} {iltn}

public export
natRangeEvalGT : {m, n, m', n' : Nat} ->
  (rng : NatRangeMap m n m' n') -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} ->
  LTE m' (natRangeEval rng i {mlti} {iltn})
natRangeEvalGT (NatRangeMapOne {mlti=mlti'} _ _ _ _) _ = mlti'
natRangeEvalGT {mlti} {iltn}
  (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i
  with (decEq m i)
    natRangeEvalGT {mlti} {iltn}
      (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} i n m' n' i' rng) i
      | Yes Refl = mlti'
    natRangeEvalGT {mlti} {iltn}
      (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i
      | No neq =
        transitive mlti' $ natRangeEvalGT rng i {mlti=(lteTolt mlti neq)}

public export
natRangeEvalLT : {m, n, m', n' : Nat} ->
  (rng : NatRangeMap m n m' n') -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} ->
  LTE (natRangeEval rng i {mlti} {iltn}) n'
natRangeEvalLT (NatRangeMapOne {iltn=iltn'} _ _ _ _) _ = iltn'
natRangeEvalLT {mlti} {iltn}
  (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i
  with (decEq m i)
    natRangeEvalLT {mlti} {iltn}
      (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} i n m' n' i' rng) i
      | Yes Refl = iltn'
    natRangeEvalLT {mlti} {iltn}
      (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i
      | No neq = natRangeEvalLT rng i {mlti=(lteTolt mlti neq)}

public export
natRangeEvalCert : {m, n, m', n' : Nat} ->
  (rng : NatRangeMap m n m' n') -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} ->
  (ev : Nat ** (LTE m' ev, LTE ev n'))
natRangeEvalCert rng i =
  (natRangeEval rng i ** (natRangeEvalGT rng i, natRangeEvalLT rng i))

public export
natRangeConstInc : (m, p, m', n', i : Nat) ->
  {auto mlti : LTE m' i} -> {auto iltn : LTE i n'} ->
  NatRangeMap m (p + m) m' n'
natRangeConstInc m 0 m' n' i {mlti} {iltn} =
  NatRangeMapOne m m' n' i
natRangeConstInc m (S p) m' n' i {mlti} {iltn} =
  NatRangeMapMulti m (S p + m) m' n' i
  {mltn=(LTESucc $ lteAddLeft p m)}
  {mlti}
  {iltn}
  $
  rewrite plusSuccRightSucc p m in
  natRangeConstInc (S m) p i n' i {mlti=reflexive}

public export
natRangeConst : (m, n, m', n', i : Nat) ->
  {auto mltn : LTE m n} ->
  {auto mlti : LTE m' i} -> {auto iltn : LTE i n'} ->
  NatRangeMap m n m' n'
natRangeConst m n m' n' i {mltn} {mlti} {iltn} =
  rewrite sym (plusMinusLte m n mltn) in
  natRangeConstInc m (minus n m) m' n' i

public export
natRangeSlice : {m, n, m', n' : Nat} -> NatRangeMap m n m' n' -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} ->
  (i' : Nat ** (LTE m' i', LTE i' n', NatRangeMap i n i' n'))
natRangeSlice {mlti} {iltn}
  (NatRangeMapOne {mlti=mlti'} {iltn=iltn'} _ _ _ i') i =
    (i' **
     (mlti', iltn',
      natRangeConst i n i' n' i' {mltn=(iltn)} {iltn=(iltn')} {mlti=reflexive}))
natRangeSlice {mlti} {iltn}
  (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} {mltn=mltn'} m n m' n' i' rng) i =
    case decEq m i of
      Yes Refl =>
        (i' **
         (mlti', iltn',
          NatRangeMapMulti
            {mlti=reflexive} {iltn=iltn'} {mltn=mltn'}
            m n i' n' i' rng))
      No neq =>
        let
          (i'' ** (ltmi'', ltin'', rng'')) =
            natRangeSlice rng i {mlti=(lteTolt mlti neq)} {iltn}
        in
        (i'' ** (transitive mlti' ltmi'', ltin'', rng''))

-- Compose a mapping from [m'..n'] to [m''..n''] after a mapping from
-- [m..n] to [m'..n'] to produce a mapping from [m..n] to [m''..n''].
public export
natRangeCompose : {m, n, m', n', m'', n'' : Nat} ->
  NatRangeMap m' n' m'' n'' -> NatRangeMap m n m' n' -> NatRangeMap m n m'' n''
natRangeCompose {m} {n} {m'} {n'} {m''} {n''} rng' rng =
  case rng of
    NatRangeMapOne p q r i {mlti} {iltn} =>
      let (ev' ** (evgt', evlt')) = natRangeEvalCert rng' i {mlti} {iltn} in
      NatRangeMapOne p m'' n'' ev' {mlti=evgt'} {iltn=evlt'}
    NatRangeMapMulti {mltn} {mlti} {iltn} p q r s j rngint =>
      let
        (i'' ** (ltmi'', ltin'', rng'')) = natRangeSlice rng' j
      in
      NatRangeMapMulti
        p q m'' n'' i''
        {mltn}
        {mlti=ltmi''}
        {iltn=ltin''}
        $
        natRangeCompose rng'' rngint

-- A morphism in the augmented simplex category, namely, an
-- order-preserving map.
public export
data FinOrdMorph : FinOrdObj -> FinOrdObj -> Type where
  FinOrdFromVoid : (n : Nat) -> FinOrdMorph 0 n
  FinOrdRange : NatRangeMap 0 n 0 n' -> FinOrdMorph (S n) (S n')

public export
finOrdMorphToList : {0 m, n : Nat} -> FinOrdMorph m n -> List Nat
finOrdMorphToList (FinOrdFromVoid _) = []
finOrdMorphToList (FinOrdRange rmap) = natRangeToList rmap

public export
Show (FinOrdMorph m n) where
  show (FinOrdFromVoid 0) = "([]->[])"
  show (FinOrdFromVoid (S n)) = "([]->[0.." ++ show n ++ "])"
  show (FinOrdRange rmap) = "(" ++ show rmap ++ ")"

public export
listToFinOrdMorph : (m, n : Nat) -> List Nat -> Maybe (FinOrdMorph m n)
listToFinOrdMorph 0 n [] = Just $ FinOrdFromVoid n
listToFinOrdMorph 0 _ (_ :: _) = Nothing
listToFinOrdMorph _ 0 (_ :: _) = Nothing
listToFinOrdMorph (S _) _ [] = Nothing
listToFinOrdMorph _ (S _) [] = Nothing
listToFinOrdMorph (S n) (S n') (i :: l) = case listToNatRange 0 n 0 n' i l of
  Just rmap => Just (FinOrdRange rmap)
  Nothing => Nothing

public export
MkFinOrdMorph : (m, n : Nat) -> (l : List Nat) ->
  {auto valid : IsJustTrue (listToFinOrdMorph m n l)} -> FinOrdMorph m n
MkFinOrdMorph m n l {valid} with (listToFinOrdMorph m n l)
  MkFinOrdMorph m n l {valid=Refl} | Just morph = morph
  MkFinOrdMorph m n l {valid=Refl} | Nothing impossible

public export
finOrdId : (n : Nat) -> FinOrdMorph n n
finOrdId 0 = FinOrdFromVoid 0
finOrdId (S n) =
  FinOrdRange $ rewrite sym (plusZeroRightNeutral n) in natRangeId 0 n

public export
finOrdCompose : {m, n, p : Nat} ->
  FinOrdMorph n p -> FinOrdMorph m n -> FinOrdMorph m p
finOrdCompose {m=0} {n} {p} _ (FinOrdFromVoid n) = FinOrdFromVoid p
finOrdCompose {m=(S m)} {n=0} (FinOrdFromVoid _) _ impossible
finOrdCompose {m=(S m)} {n=(S n)} {p=0} _ _ impossible
finOrdCompose {m=(S m)} {n=(S n)} {p=(S p)} (FinOrdFromVoid _) _ impossible
finOrdCompose {m=(S m)} {n=(S n)} {p=(S p)} _ (FinOrdFromVoid _) impossible
finOrdCompose {m=(S m)} {n=(S n)} {p=(S p)}
  (FinOrdRange np) (FinOrdRange mn) = FinOrdRange $ natRangeCompose np mn

---------------------
---------------------
---- Finite ADTs ----
---------------------
---------------------

public export
data FinADTObj : Type where
  FinADTOrd : FinADTObj
  FinProduct : List FinADTObj -> FinADTObj
  FinCoproduct : List FinADTObj -> FinADTObj

mutual
  public export
  interpFinADTObj : FinADTObj -> Type
  interpFinADTObj FinADTOrd = FinOrdObj
  interpFinADTObj (FinProduct l) = interpFinProduct l
  interpFinADTObj (FinCoproduct l) = interpFinCoproduct l

  public export
  interpFinNEProduct : FinADTObj -> List FinADTObj -> Type
  interpFinNEProduct t [] =
    interpFinADTObj t
  interpFinNEProduct t (t' :: ts) =
    Pair (interpFinADTObj t) $ interpFinNEProduct t' ts

  public export
  interpFinProduct : List FinADTObj -> Type
  interpFinProduct [] = Unit
  interpFinProduct (t :: ts) = interpFinNEProduct t ts

  public export
  interpFinCoproduct : List FinADTObj -> Type
  interpFinCoproduct [] = Void
  interpFinCoproduct (t :: ts) = interpFinNECoproduct t ts

  public export
  interpFinNECoproduct : FinADTObj -> List FinADTObj -> Type
  interpFinNECoproduct t [] =
    interpFinADTObj t
  interpFinNECoproduct t (t' :: ts) =
    Either (interpFinADTObj t) $ interpFinNECoproduct t' ts

public export
data FinADTMorph : FinADTObj -> FinADTObj -> Type where

public export
data FinADTFunctor : Type where
  FinIdF : FinADTFunctor
  FinComposeF : FinADTFunctor -> FinADTFunctor -> FinADTFunctor
  FinProductF : List FinADTFunctor -> FinADTFunctor
  FinCoproductF : List FinADTFunctor -> FinADTFunctor

-------------------------------------
-------------------------------------
---- S-expressions made of pairs ----
-------------------------------------
-------------------------------------

public export
SExpBaseF : Type -> Type
SExpBaseF = ProductMonad

public export
SExpAlg : Type -> Type
SExpAlg = Algebra SExpBaseF

public export
SExpCoalg : Type -> Type
SExpCoalg = Coalgebra SExpBaseF

public export
SExpTermF : Type -> Type -> Type
SExpTermF = TermFunctor SExpBaseF

public export
SExpTreeF : Type -> Type -> Type
SExpTreeF = TreeFunctor SExpBaseF

public export
SExpTermAlg : Type -> Type -> Type
SExpTermAlg = TermAlgebra SExpBaseF

public export
SExpTreeCoalg : Type -> Type -> Type
SExpTreeCoalg = TreeCoalgebra SExpBaseF

public export
FreeSExp : Type -> Type
FreeSExp = FreeMonad SExpBaseF

public export
CofreeSExp : Type -> Type
CofreeSExp = CofreeComonad SExpBaseF

public export
SPairF : Type -> Type -> Type
SPairF var carrier = ProductMonad (SExpTermF var carrier)

public export
SPairTermF : Type -> Type -> Type
SPairTermF var = TermFunctor (ProductMonad . SExpTermF var) var

public export
SPairTreeF : Type -> Type -> Type
SPairTreeF var = TreeFunctor (ProductMonad . SExpTermF var) var

---------------------
---------------------
---- Finite ADTs ----
---------------------
---------------------

public export
data ADTObjF : Type -> Type where
  ADTF : TupleP (TupleP carrier) -> ADTObjF carrier

public export
ADTObjAlgebra : Type -> Type
ADTObjAlgebra = Algebra ADTObjF

public export
ADTObjCoalgebra : Type -> Type
ADTObjCoalgebra = Coalgebra ADTObjF

public export
FreeADTObj : Type -> Type
FreeADTObj = FreeMonad ADTObjF

public export
CofreeADTObj : Type -> Type
CofreeADTObj = CofreeComonad ADTObjF

public export
MuADTObj : Type
MuADTObj = Mu ADTObjF

public export
NuADTObj : Type
NuADTObj = Nu ADTObjF

public export
adtCases : {carrier : Type} -> ADTObjF carrier -> TupleP (TupleP carrier)
adtCases (ADTF t) = t

public export
adtIndex : {carrier : Type} -> ADTObjF carrier -> Type
adtIndex = TupleIndex . adtCases

public export
adtConstructor :
  {carrier : Type} -> (adt : ADTObjF carrier) -> adtIndex adt -> TupleP carrier
adtConstructor adt i = TupleElem (adtCases adt) i

public export
adtCase :
  {carrier : Type} -> (adt : ADTObjF carrier) -> adtIndex adt -> TupleP carrier

public export
record ADTMorphCarrier (objCarrier : Type) where
  constructor MkADTMorphCarrier
  morphObj : Type
  morphSignature : morphObj -> (TupleP objCarrier, objCarrier)

-- Given a `carrier` tuple constant types in a product category, `ADTObjF`
-- is a polynomial ADT comprising coproducts of products of types drawn
-- from the tuple of input (carrier) types.
public export
data ADTObjProjF : TupleP Type -> Type where
  ADT : {carrier : TupleP Type} ->
    TupleP (TupleP (TupleIndex {atom=Type} carrier)) -> ADTObjProjF carrier

public export
ADTProductObjF : TupleP Type -> TupleP Type
ADTProductObjF t = mapTupleP (const $ ADTObjProjF t) t

public export
LengthEquals : (carrier : Type) -> (Nat, List carrier) -> Type
LengthEquals _ (n, l) = n = length l

-- A list paired with its length (effectively, storing its length together
-- with the list at "runtime").
public export
ListN : Type -> Type
ListN carrier = (nl : (Nat, List carrier) ** LengthEquals carrier nl)

-- A finite-dimensional "matrix" with variable numbers of elements per row.
-- The parameter is the dimension minus one.
public export
VarMatrixD : (predDimension : Nat) -> Type -> Type
VarMatrixD Z carrier = ListN carrier
VarMatrixD (S n) carrier = ListN (VarMatrixD n carrier)

-- A finite-dimensional matrix of natural numbers.
-- The parameter is the dimension minus one.
VarMatrixN : (predDimension : Nat) -> Type
VarMatrixN = flip VarMatrixD Nat

public export
record FiniteShape where
  constructor MkFiniteShape
  numObjects : Nat
  numMorphisms : Nat
  domains : Vect numMorphisms (Fin numObjects)
  codomains : Vect numMorphisms (Fin numObjects)

-------------------------------
-------------------------------
---- Refined S-expressions ----
-------------------------------
-------------------------------

-- We define a category inductively through applications of the
-- following type constructors:
--
--  - `Atom` (for some given metalanguage atom type, which must be isomorphic
--  -         to the natural numbers or some subset of them, which in particular
--  -         means that they have a decidable equality)
--  - `Nat`
--  - `RefinedList` (indexed by number of atoms in the list)
--  - `RefinedSexp` (indexed by total number of atoms in the expression)
--
-- We define the category by treating the type constructors as
-- monads and comonads, and the function definitions as natural
-- transformations, which in turn are derived from compositions of
-- the units and counits of adjunctions.

public export
record RefinedSexpCarrier where
  constructor MkRefinementSexpCarrier
  RefinedSexpFunctorCarrier : Type
  RefinedSexpNatTransCarrier : Type
  RefinedSexpNatTransSignatureCarrier :
    RefinedSexpNatTransCarrier ->
    (RefinedSexpFunctorCarrier, RefinedSexpFunctorCarrier)

public export
data RefinedSexpFunctorF : (atom : Type) -> RefinedSexpCarrier -> Type where

public export
data RefinedSexpNatTransF : (atom : Type) -> RefinedSexpCarrier -> Type where

public export
RefinedSexpNatTransSignatureF : {atom : Type} ->
  (carrier : RefinedSexpCarrier) ->
  RefinedSexpNatTransF atom carrier ->
  (RefinedSexpNatTransF atom carrier, RefinedSexpNatTransF atom carrier)
RefinedSexpNatTransSignatureF {atom} carrier newNatTrans impossible

mutual
  public export
  data RefinedSexpFunctor : (atom : Type) -> Type where
    InRSF :
      RefinedSexpFunctorF atom (RefinedSexpData atom) ->
      RefinedSexpFunctor atom

  public export
  data RefinedSexpNatTrans : (atom : Type) -> Type where
    InRSNT :
      RefinedSexpNatTransF atom (RefinedSexpData atom) ->
      RefinedSexpNatTrans atom

  public export
  RefinedSexpNatTransSignature : {atom : Type} ->
    RefinedSexpNatTrans atom ->
    (RefinedSexpFunctor atom, RefinedSexpFunctor atom)
  RefinedSexpNatTransSignature (InRSNT _) impossible

  public export
  RefinedSexpData : (atom : Type) -> RefinedSexpCarrier
  RefinedSexpData atom =
    MkRefinementSexpCarrier
      (RefinedSexpFunctor atom)
      (RefinedSexpNatTrans atom)
      (RefinedSexpNatTransSignature {atom})

--------------------
--------------------
---- Core types ----
--------------------
--------------------

-----------------------
---- S-expressions ----
-----------------------

public export
data SexpClass : Type where
  SEXP : SexpClass
  SLIST : SexpClass

public export
SexpObject : Type
SexpObject = ProductCatObject SexpClass

public export
SexpObjectMap : Type
SexpObjectMap = ProductCatObjectEndoMap SexpClass

public export
data SexpFunctor :
    (atom : Type) -> (carrier : SexpObject) -> SexpObject where
  SexpF :
    atom -> carrier SLIST -> SexpFunctor atom carrier SEXP
  SlistF :
    ListF (carrier SEXP) (carrier SLIST) ->
    SexpFunctor atom carrier SLIST

public export
SexpAlg : Type -> SexpObject -> Type
SexpAlg = ProductCatAlgebra {idx=SexpClass} . SexpFunctor

public export
FreeSexp : Type -> SexpObject -> SexpObject
FreeSexp atom = ProductCatFreeMonad {idx=SexpClass} (SexpFunctor atom)

public export
MuSexp : Type -> SexpObject
MuSexp atom = MuProduct {idx=SexpClass} (SexpFunctor atom)

public export
Sexp : Type -> Type
Sexp = flip MuSexp SEXP

public export
Slist : Type -> Type
Slist = flip MuSexp SLIST

public export
SexpCoalg : Type -> SexpObject -> Type
SexpCoalg = ProductCatCoalgebra {idx=SexpClass} . SexpFunctor

public export
CofreeSexp : Type -> SexpObject -> SexpObject
CofreeSexp atom = ProductCatCofreeComonad {idx=SexpClass} (SexpFunctor atom)

public export
NuSexp : Type -> SexpObject
NuSexp atom = NuProduct {idx=SexpClass} (SexpFunctor atom)

-------------------------------------------------
-------------------------------------------------
---- The category of polynomial endofunctors ----
-------------------------------------------------
-------------------------------------------------

public export
record FinNatPoly where
  constructor MkFinNatPoly
  numTerms : Nat
  coefficients : LList Nat numTerms
  trimmed : Not (head' (llList coefficients) = Just 0)

public export
Show FinNatPoly where
  show (MkFinNatPoly _ c _) = show c

public export
InitFinNatPoly :
  (l : List Nat) -> {auto ok : (head' l /= Just 0) = True} -> FinNatPoly
InitFinNatPoly l {ok} = MkFinNatPoly (length l) (InitLList l) $
  \isz =>
    case replace {p=(\hl => (hl /= Just 0) = True)} isz ok of Refl impossible

public export
interpretFinNatPoly : FinNatPoly -> Nat -> Nat
interpretFinNatPoly (MkFinNatPoly d cs _) n =
  llCata (MkLLAlg Z (\i, c, acc => acc + c * (power n i))) cs

public export
record MultiVarTerm (constant, variable : Type) where
  PolyTerm : (constant, variable)

public export
mvConst : MultiVarTerm constant variable -> constant
mvConst = fst . PolyTerm

public export
mvVar : MultiVarTerm constant variable -> variable
mvVar = snd . PolyTerm

public export
record MultiVarPoly (constant, variable : Type) where
  PolyTerms : List (MultiVarTerm constant variable)

public export
numTerms : MultiVarPoly constant variable -> Nat
numTerms = length . PolyTerms

public export
mvNth :
  (mvp : MultiVarPoly constant variable) -> (n : Nat) ->
  {auto ok : InBounds n (PolyTerms mvp)} ->
  MultiVarTerm constant variable
mvNth mvp n = index n (PolyTerms mvp)

---------------
---------------
---- Paths ----
---------------
---------------

public export
EdgeProjectionType : Type -> Type -> Type
EdgeProjectionType vertex edge = edge -> (vertex, vertex)

public export
record PathCarrier (vertex : Type) where
  constructor EdgeFibration
  EdgeTotal : Type
  EdgeProjection : EdgeProjectionType vertex EdgeTotal

public export
edgeSource : {carrier : PathCarrier vertex} -> EdgeTotal carrier -> vertex
edgeSource {carrier} = fst . EdgeProjection carrier

public export
edgeTarget : {carrier : PathCarrier vertex} -> EdgeTotal carrier -> vertex
edgeTarget {carrier} = snd . EdgeProjection carrier

public export
data PathTotalF :
    (vEq : vertex -> vertex -> Type) -> PathCarrier vertex -> Type where
  LoopF :
    {carrier : PathCarrier vertex} ->
    vertex ->
    PathTotalF vEq carrier
  ConcatF :
    {carrier : PathCarrier vertex} ->
    (tail, head : EdgeTotal carrier) ->
    {auto valid :
      vEq (edgeSource {carrier} tail) (edgeTarget {carrier} head)} ->
    PathTotalF vEq carrier

public export
PathDomainF :
  {vertex : Type} ->
  {vEq : vertex -> vertex -> Type} ->
  (carrier : PathCarrier vertex) ->
  PathTotalF vEq carrier ->
  vertex
PathDomainF carrier (LoopF v) = v
PathDomainF carrier (ConcatF tail head) = edgeSource {carrier} head

public export
PathCodomainF :
  {vertex : Type} ->
  {vEq : vertex -> vertex -> Type} ->
  (carrier : PathCarrier vertex) ->
  PathTotalF vEq carrier ->
  vertex
PathCodomainF carrier (LoopF v) = v
PathCodomainF carrier (ConcatF tail head) = edgeTarget {carrier} tail

public export
PathProjectionF :
  {vertex : Type} ->
  {vEq : vertex -> vertex -> Type} ->
  (carrier : PathCarrier vertex) ->
  EdgeProjectionType vertex (PathTotalF vEq carrier)
PathProjectionF carrier edge =
  (PathDomainF carrier edge, PathCodomainF carrier edge)

public export
PathF : {vertex : Type} ->
  (vertex -> vertex -> Type) ->
  PathCarrier vertex ->
  PathCarrier vertex
PathF vEq carrier =
  EdgeFibration (PathTotalF vEq carrier) (PathProjectionF {vEq} carrier)

----------------------------
----------------------------
---- Geb terms in Idris ----
----------------------------
----------------------------

-- Geb itself is a pure specification.  `GebTerm` is an Idris type whose
-- terms represent various concepts of Geb.  Because a term of `GebTerm`
-- might represent any of several different concepts, the type is indexed
-- by a type of atoms which classify which concept a given term represents.
-- This makes `GebTerm` a type family; it's effectively simulating a
-- definition by a large mutual recursion, but using an index intead of many
-- different Idris types allows us to interpret Geb in Idris by interpreting
-- just that one type.  I find it less confusing and more convenient than a big
-- mutual recursion.

-------------------------
---- Term definition ----
-------------------------

-- We define `GebTerm` -- an Idris type -- as a fixed point of a
-- polynomial endofunctor of Idris, in the same style in which we will define
-- types of Geb itself.  In particular, that will allow us to write a homoiconic
-- representation of `GebTerm` _as_ a term of `GebTerm` in a way
-- which parallels the Idris definition of `GebTerm`.
--
-- Because `GebTerm`, as described above, represents a number of different
-- concepts, we can view it as an object in a finite product category, where
-- each concept -- which we call a "class" in the context of defining
-- `GebTerm` -- is one of the categories.
--
-- So we first define `GebTermF`, a (polynomial) endofunctor in the product
-- category of all the classes.  Having defined that functor, we'll take a
-- fixed point of it (which we will be able to do because it is polynomial),
-- and then we'll have a `GebTerm` which comprises the Idris
-- representation of terms of Geb.
--
-- Below is the product category in which `GebTerm` lives; therefore it's
-- the category on which we will build an endofunctor, `GebTermF`, from
-- which we will derive `GebTerm` as a fixpoint (initial algebra).
--
-- We represent the product category as a function from a finite
-- index type rather than as, say, nested pairs or a list -- those are all
-- isomorphic, but I feel that the function representation produces the most
-- readable code.
--
-- The aspects of the product category that we define are its objects, its
-- morphisms, and its endofunctors.

public export
GebTermProductCatObject : Type
GebTermProductCatObject = ProductCatObject GebAtom

-- A morphism in a product category is a product of morphisms.
-- (In an Idris category, morphisms are functions.)
public export
GebTermProductCatMorphism :
  GebTermProductCatObject -> GebTermProductCatObject -> Type
GebTermProductCatMorphism = ProductCatMorphism {idx=GebAtom}

-- An endofunctor on the Idris product category in which Geb terms are defined
-- is a function on objects of the product category together with a function
-- on morphisms that respects it.

public export
GebTermProductCatObjectMap : Type
GebTermProductCatObjectMap = ProductCatObjectEndoMap GebAtom

public export
GebTermProductCatMorphismMap : GebTermProductCatObjectMap -> Type
GebTermProductCatMorphismMap = ProductCatMorphismEndoMap

public export
GebTermProductCatEndofunctor : Type
GebTermProductCatEndofunctor = ProductCatEndofunctor GebAtom

------------------------------------------
---- Term-checking and interpretation ----
------------------------------------------


---------------------------------
---------------------------------
---- Metalanguage fibrations ----
---------------------------------
---------------------------------

-----------------------------
-----------------------------
---- Metalanguage arrows ----
-----------------------------
-----------------------------

-- We refer to a pair of a pair of vertices in a directed graph and an edge
-- from the first vertex in the pair to the second vertex in the pair as an
-- "arrow".

----------------------------
----------------------------
---- Generalized arrows ----
----------------------------
----------------------------

-- We refer to a pair of a pair of vertices in a directed graph and an edge
-- from the first vertex in the pair to the second vertex in the pair as an
-- "arrow".

{-
public export
ArrowSig : Type -> Type
ArrowSig vertexType = (vertexType, vertexType)

public export
EdgeType : Type -> Type
EdgeType vertexType = ArrowSig vertexType -> Type

public export
Arrow : {vertexType : Type} -> EdgeType vertexType -> Type
Arrow {vertexType} arrowType = DPair (ArrowSig vertexType) arrowType

public export
arrowSig : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  Arrow arrowType -> ArrowSig vertexType
arrowSig (sig ** _) = sig

public export
arrowEdge : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  (arrow : Arrow arrowType) -> arrowType (arrowSig arrow)
arrowEdge (_ ** edge) = edge

public export
arrowSource : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  Arrow arrowType -> vertexType
arrowSource = fst . arrowSig

public export
arrowTarget : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  Arrow arrowType -> vertexType
arrowTarget = snd . arrowSig
-}

----------------------------------------
----------------------------------------
---- Equivalence and term rewriting ----
----------------------------------------
----------------------------------------

------------------------------------
---- Free equivalence relations ----
------------------------------------

-- A type which represents witnesses to an equivalence relation.
-- A term of this type may be used as a rewrite rule.

public export
data FreeEquivF : Type -> Type -> Type where
  -- `EqRefl` represents the equivalence between some term `x` of type `a`
  -- and itself.  The reason it has _two_ parameters of type `a` is that
  -- a free generator of witnesses to an equivalence relation is in effect,
  -- and will be used as, a rewrite rule.  Asserting `EqRefl` between `x`
  -- and `y` is a claim that there is a _decidable_ equality between the two
  -- which can be decided when the term is validated (typechecked).
  EqRefl : a -> a -> FreeEquivF a carrier
  -- Given a term of `carrier`, which represents an equivalence bewteen
  -- terms `x` and `y` of `a`, `EqSym` represents an equivalence between
  -- `y` and `x`.
  EqSym : a -> a -> carrier -> FreeEquivF a carrier
  -- Given terms `eq` and `eq'` of type `carrier`, which respectively
  -- represent the equivalences of `x` and `y` and of `y` and `z` of type `a`,
  -- `EqTrans` represents the equivalence of `x` and `z`.
  EqTrans : a -> a -> a -> carrier -> carrier -> FreeEquivF a carrier

public export
Bifunctor FreeEquivF where
  bimap f _ (EqRefl x y) = EqRefl (f x) (f y)
  bimap f g (EqSym x y eq) = EqSym (f x) (f y) $ g eq
  bimap f g (EqTrans x y z eq eq') = EqTrans (f x) (f y) (f z) (g eq) (g eq')

-- Tests for the validity of a witness to an equivalence relation,
-- and if it is valid, returns which terms are being witnessed to be equivalent.
public export
checkFreeEquiv :
  Eq a =>
  ((a, a) -> Maybe (a, a)) ->
  FreeEquivF a (a, a) -> Maybe (a, a)
checkFreeEquiv eqa (EqRefl x y) =
  case eqa (x, y) of
    Just (x', y') => if x == x' && y == y' then Just (x, y) else Nothing
    Nothing => Nothing
checkFreeEquiv eqa (EqSym x y eq) =
  case eqa eq of
    Just (x', y') => if x == x' && y == y' then Just (y, x) else Nothing
    Nothing => Nothing
checkFreeEquiv eqa (EqTrans x y z eq eq') =
  case (eqa eq, eqa eq') of
    (Just (x', y'), Just (y'', z')) =>
      if x == x' && y == y' && y' == y'' && z == z' then
        Just (x, z)
      else
        Nothing
    (Nothing, _) => Nothing
    (_, Nothing) => Nothing

--------------------------
---- Rewritable terms ----
--------------------------

-- A rewritable term type is a term type accompanied with a (free) equivalence
-- relation, a witness to which may be used _as_ a term.
public export
data RewritableTermF : Type -> Type where
  Rewrite : FreeEquivF carrier carrier -> RewritableTermF carrier

-------------------------
-------------------------
---- Free categories ----
-------------------------
-------------------------

-- When freely generating categories, we are producing _three_ types:
--
--  - Objects
--  - Morphisms
--  - Equalities
--
-- The equalities come from the identity and associativity laws.  When we
-- define categories in the usual way by proving that existing constructs
-- satisfy the axioms, we must supply proofs of those equalities.  But when
-- we freely generate a category, we must freely generate those equalities
-- to _make_ the generated category satisfy the axioms.
--
-- Consequently, throughout the rest of the development of expressions, the
-- algebras which typecheck objects and morphisms will _not_ use metalanguage
-- equalities -- they will use (and update) carrier types representing
-- free equivalence relations (see `FreeEquivF` above).  This must include
-- the expressions representing objects and morphisms -- our free generation
-- may produce some objects indirectly via morphisms, and since morphisms
-- may exhibit free equalities, objects may as well, unlike in traditional
-- category theory.  The typechecking of morphisms must respect a carrier
-- free equivalence on _objects_, because an equivalence of objects may allow a
-- composition which would not have been allowed by intensional equality
-- (meaning that the domain of the following morphism was not intensionally
-- equal to the codomain of the preceding morphism).
public export
data MorphismF : Type -> Type -> Type where
  -- An identity morphism is labeled by the object which is its
  -- domain and codomain.
  IdentityF :
    object -> MorphismF object carrier
  -- A composition is labeled by its source, intermediate object, and
  -- target, followed by the two morphisms being composed, with the
  -- following morphism listed first, as in usual mathematical notation.
  ComposeF :
    object -> object -> object -> carrier -> carrier -> MorphismF object carrier

public export
checkMorphism :
  (Eq object, Eq carrier) =>
  (object -> Maybe object) ->
  (carrier -> Maybe (object, object)) ->
  (MorphismF object carrier -> Maybe (object, object))
checkMorphism checkObj checkMorph (IdentityF obj) =
  case checkObj obj of
    Just obj' => Just (obj', obj')
    Nothing => Nothing
checkMorphism checkObj checkMorph (ComposeF a b c g f) =
  case (checkObj a, checkObj b, checkObj c, checkMorph g, checkMorph f) of
    (Just a', Just b', Just c', Just (domg, codg), Just (domf, codf)) =>
      if a' == domf && b' == codf && b' == domg && c' == codg then
        Just (a', c')
      else
        Nothing
    _ => Nothing

public export
Bifunctor MorphismF where
  bimap f _ (IdentityF v) = IdentityF $ f v
  bimap f g (ComposeF s i t q p) = ComposeF (f s) (f i) (f t) (g q) (g p)

-- Free categories produce a free equivalence on morphisms, correpsonding to
-- the identity and associativity laws.
public export
data MorphismEqF : Type -> Type where
  -- Rewrite the morphism `(id . f)` to `f`.
  RewriteIDLeft : morphism -> MorphismEqF morphism
  -- Rewrite the morphism `(f . id)` to `f`.
  RewriteIDRight : morphism -> MorphismEqF morphism
  -- Rewrite the morphism `(f . g) . h` to `f . (g . h)`.
  RewriteAssoc : morphism -> morphism -> morphism -> MorphismEqF morphism

-- Generate the free equivalence relation from the identity and associativity
-- laws.
public export
CoequalizedMorphismF : Type -> Type
CoequalizedMorphismF carrier = FreeEquivF (MorphismEqF carrier) carrier

-- Generate the refined type of morphisms quotiented by the rewrite rules
-- (which are the axioms of category theory).
public export
data RefinedMorphismF : Type -> Type -> Type where
  RawMorphism :
    MorphismF object carrier -> RefinedMorphismF object carrier
  CoequalizedMorphism :
    CoequalizedMorphismF (RefinedMorphismF object carrier) ->
    RefinedMorphismF object carrier

----------------------------------
----------------------------------
---- Term-building categories ----
----------------------------------
----------------------------------

-- These are the categories we need in order to define the objects
-- and morphisms of the refined first-order ADT category -- the smallest one
-- in which there is an object which we can interpret in Idris as
-- `RefinedADTCat`.

-- Generate objects for a category which can support at least
-- substitution:  initial and terminal objects, and products and coproducts.
public export
data SubstCatObjF : Type -> Type where
  SubstInitial : SubstCatObjF carrier
  SubstTerminal : SubstCatObjF carrier
  SubstProduct : carrier -> carrier -> SubstCatObjF carrier
  SubstCoproduct : carrier -> carrier -> SubstCatObjF carrier

-- Generate morphisms for a category which can support at least substitution.
public export
data SubstCatMorphismF : Type -> Type -> Type where
  -- The left adjoint of the unique functor from the substitution category
  -- to the terminal category (which is the discrete one-object category).
  SubstFromInitial : object -> SubstCatMorphismF object carrier

  -- The right adjoint of the unique functor from the substitution category
  -- to the terminal category.
  SubstToTerminal : object -> SubstCatMorphismF object carrier

  -- The right adjoint of the diagonal functor (the diagonal functor goes
  -- from the substitution category to the product category, so its adjoints
  -- go from the product category to the substitution category).
  SubstProductIntro : (dom, cod, cod' : object) ->
    carrier -> carrier -> SubstCatMorphismF object carrier

  -- The left projection of the counit of the product adjunction
  -- (which is a morphism in the substitution category).
  SubstProductElimLeft : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  -- The right projection of the counit of the product adjunction.
  SubstProductElimRight : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  SubstCoproductIntroLeft : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  SubstCoproductIntroRight : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  SubstCoproductElim : (dom, dom', cod : object) ->
    carrier -> carrier -> SubstCatMorphismF object carrier

public export
data RefinedSubstObjF : Type -> Type -> Type where
  SubstEqualizer : object -> object -> morphism -> morphism ->
    RefinedSubstObjF object morphism

  SubstCoequalizer : object -> object -> morphism -> morphism ->
    RefinedSubstObjF object morphism

public export
data RefinedSubstMorphismF : Type -> Type -> Type where

public export
SubstCatObjFree : Type -> Type
SubstCatObjFree = FreeMonad SubstCatObjF

public export
SubstCatObj : Type
SubstCatObj = Mu SubstCatObjF

-----------------------------------------------------------
-----------------------------------------------------------
---- Substitution category in the metalanguage (Idris) ----
-----------------------------------------------------------
-----------------------------------------------------------

-- public export
-- data MetaSubstCatObjAlg : Type -> Type) where

----------------------------------
----------------------------------
----- Polynomial endofunctors ----
----------------------------------
----------------------------------

-- Expressions are drawn from four categories determined by the presence
-- or absence of each of the following pairs of universal properties:
--
--  - Equalizers & coequalizers
--    (Categories with them are called "refined"; those without are "unrefined")
--  - Initial algebras & terminal coalgebras
--    (Categories with them are "first-order"; those without are "zeroth-order")
--
-- The zeroth-order categories may also be called "substitution" categories.
--
-- All four categories have each of the following pairs of universal properties:
--
--  - Initial objects & terminal objects
--  - Products & coproducts
--
-- All the types until the end of the `Expression` section are zeroth-order,
-- even though they _have_ initial algebras and terminal coalgebras, because
-- they are all defined in the style of "datatypes à la carte" -- in effect,
-- this means that we are programming in the category of polynomial functors
-- of the zeroth-order categories.  At the end of the `Expression` section,
-- we generate the full forms of expressions by taking the fixpoints and
-- cofixpoints of the datatypes previously defined; those types live only in
-- the first-order categories.

----------------------------------
----------------------------------
----- Polynomial endofunctors ----
----------------------------------
----------------------------------

public export
data PolynomialFunctorF : Type -> Type -> Type where
  -- See https://ncatlab.org/nlab/show/polynomial+functor#definition :
  --
  -- In a category `C`, objects `W`, `X`, `Y`, `Z` and morphisms:
  --
  --  `f`: `X -> W`
  --  `g`: `X -> Y`
  --  `h`: `Y -> Z`
  --
  -- determine a polynomial endofunctor from `C/W` to `C/Z` comprised of
  -- the composition (domain to codomain):
  --
  --  `f*`: `C/W -> C/X` (pullback (or "base change") functor of `f`)
  --  `Pi(g)`: `C/X -> C/Y` (dependent product)
  --  `Sigma(h)`: `C/Y -> C/Z` (dependent sum)
  --
  -- (This is an endofunctor iff `W==Z`, and a non-dependent endofunctor
  -- iff furthermore `W==Z==1` (where `1` is the terminal object of `C`).
  PolyFunctorFromMorphisms : (w, x, y, z : object) -> (f, g, h : morphism) ->
    PolynomialFunctorF object morphism

public export
data CartesianTransformationF : Type -> Type -> Type -> Type where
  -- See
  -- https://ncatlab.org/nlab/show/equifibered%20natural%20transformation#properties:
  --
  -- Given a category `C` with a terminal object, a category `D` with all
  -- pullbacks, and a functor `G : C -> D`, then an object `F1` of `C` and
  -- a morphism `F[F1] -> G[1]` (where `1` is the terminal object of `C`)
  -- determine a functor `F : C -> D` and a natural transformation `F -> G`
  -- which is "equifibered" (also called "cartesian"), meaning that all of
  -- its naturality squares are pullbacks.  (The functor `F` itself is
  -- generated by taking pullbacks.)
    CartesianTransformationFromMorphism:
      (f1 : object) -> (f : morphism) -> (g : functor) ->
      CartesianTransformationF object morphism functor

public export
data AdjunctionF : Type -> Type -> Type where
  AdjunctionFromUnits : (l, r : functor) -> (unit, counit : natTrans) ->
    AdjunctionF functor natTrans

public export
data ConjugateNatTransF : Type -> Type where
  -- See
  -- https://unapologetic.wordpress.com/2007/07/30/transformations-of-adjoints/
  -- for the definition of "conjugate natural transformations" and how
  -- they can be used to transform adjoints.
  ConjugateNatTransFromPair :
    natTrans -> natTrans -> ConjugateNatTransF natTrans

-- Expressions are drawn from four categories determined by the presence
-- or absence of each of the following pairs of universal properties:
--
--  - Equalizers & coequalizers
--    (Categories with them are called "refined"; those without are "unrefined")
--  - Initial algebras & terminal coalgebras
--    (Categories with them are "first-order"; those without are "zeroth-order")
--
-- The zeroth-order categories may also be called "substitution" categories.
--
-- All four categories have each of the following pairs of universal properties:
--
--  - Initial objects & terminal objects
--  - Products & coproducts
--
-- All the types until the end of the `Expression` section are zeroth-order,
-- even though they _have_ initial algebras and terminal coalgebras, because
-- they are all defined in the style of "datatypes à la carte" -- in effect,
-- this means that we are programming in the category of polynomial functors
-- of the zeroth-order categories.  At the end of the `Expression` section,
-- we generate the full forms of expressions by taking the fixpoints and
-- cofixpoints of the datatypes previously defined; those types live only in
-- the first-order categories.

--------------------
---- Core types ----
--------------------

-- These types are members of at least the refined first-order category
-- (in some cases they are members of other categories as well).  They
-- may be used to help _define_ even categories which they are not themselves
-- objects of, because the _definitions_ all occur in the refined first-order
-- category.  (In particular, they all have initial algebras and terminal
-- coalgebras, which are present in the first-order categories but not the
-- zeroth-order categories.)

---------------------------------------
---- Refined substitution category ----
---------------------------------------

-- Generate objects of the refined substitution category.
public export
data RSubstObjF :
    (obj, morph : Type) -> (domain, codomain : morph -> obj) -> Type where
  RSubstObjInitial : RSubstObjF obj morph domain codomain

public export
data RefinedExpClass : Type where
  RECl_Object : RefinedExpClass
  RECl_Morphism : RefinedExpClass
  RECl_PolyEndo : RefinedExpClass
  RECl_PolyNatTrans : RefinedExpClass

public export
record RefinedExpCategory_Obj where
  constructor RefinedExpClassTypes

  RECat_Object : Type
  RECat_Morphism : Type
  RECat_PolyEndo : Type
  RECat_PolyNatTrans : Type

  RECat_Morphism_Domain : RECat_Morphism -> RECat_Object
  RECat_Morphism_Codomain : RECat_Morphism -> RECat_Object
  RECat_PolyNatTrans_Domain : RECat_PolyNatTrans -> RECat_PolyEndo
  RECat_PolyNatTrans_Codomain : RECat_PolyNatTrans -> RECat_PolyEndo

public export
record RefinedExpCategory_Equiv (recat : RefinedExpCategory_Obj) where
  constructor RefinedExpCategory_Equivalences

  RECat_Object_Equiv : Type
  RECat_Morphism_Equiv : Type
  RECat_PolyEndo_Equiv : Type
  RECat_PolyNatTrans_Equiv : Type

  RECat_ObjectEquiv_Left :
    RECat_Object_Equiv -> RECat_Object recat
  RECat_ObjectEquiv_Right :
    RECat_Object_Equiv -> RECat_Object recat
  RECat_MorphismEquiv_Left :
    RECat_Morphism_Equiv -> RECat_Morphism recat
  RECat_MorphismEquiv_Right :
    RECat_Morphism_Equiv -> RECat_Morphism recat
  RECat_PolyEndoEquiv_Left :
    RECat_PolyEndo_Equiv -> RECat_PolyEndo recat
  RECat_PolyEndoEquiv_Right :
    RECat_PolyEndo_Equiv -> RECat_PolyEndo recat
  RECat_PolyNatTransEquiv_Left :
    RECat_PolyNatTrans_Equiv -> RECat_PolyNatTrans recat
  RECat_PolyNatTransEquiv_Right :
    RECat_PolyNatTrans_Equiv -> RECat_PolyNatTrans recat

public export
ObjectTypeInterpretation : Type -> Type
ObjectTypeInterpretation obj = obj -> Type

public export
TermTypeInterpretation : {obj : Type} -> ObjectTypeInterpretation obj -> Type
TermTypeInterpretation {obj} objInterp = (a : obj) -> () -> objInterp a

public export
MorphismTypeInterpretation : {obj : Type} -> ObjectTypeInterpretation obj ->
  (morph : Type) -> (domain, codomain : morph -> obj) -> Type
MorphismTypeInterpretation objInterp morph domain codomain =
  (m : morph) -> objInterp (domain m) -> objInterp (codomain m)

public export
MorphHasSig : {obj, morph : Type} ->
  (domain : morph -> obj) -> (codomain : morph -> obj) ->
  morph -> (obj, obj) -> Type
MorphHasSig domain codomain m (a, b) = (domain m = a, codomain m = b)

public export
FunctorObjmap : Type -> Type
FunctorObjmap obj = obj -> obj

public export
FunctorMorphmap : {obj, morph : Type} ->
  (domain : morph -> obj) -> (codomain : morph -> obj) ->
  FunctorObjmap obj -> Type
FunctorMorphmap {obj} {morph} domain codomain objmap =
  (m : morph) ->
  (fm : morph **
   MorphHasSig domain codomain fm (objmap (domain m), objmap (codomain m)))

public export
FunctorTypeInterpretation : {obj, morph : Type} ->
  {domain, codomain : morph -> obj} ->
  (objInterp : ObjectTypeInterpretation obj) ->
  MorphismTypeInterpretation objInterp morph domain codomain ->
  Type -> Type
FunctorTypeInterpretation {obj} {domain} {codomain}
  objInterp morphInterp functor =
    functor ->
      (objmap : FunctorObjmap obj ** FunctorMorphmap domain codomain objmap)

public export
record RefinedExpInterpretation (recat : RefinedExpCategory_Obj) where
  constructor RefinedExpInterpretations
  REInt_Object : ObjectTypeInterpretation (RECat_Object recat)
  REInt_Term : TermTypeInterpretation REInt_Object
  REInt_Morphism :
    MorphismTypeInterpretation
      REInt_Object (RECat_Morphism recat)
      (RECat_Morphism_Domain recat) (RECat_Morphism_Codomain recat)
  REInt_PolyEndo :
    FunctorTypeInterpretation REInt_Object REInt_Morphism (RECat_PolyEndo recat)

public export
record RefinedExpCategoryType where
  constructor RefinedExpCategoryComponents
  REC_Obj : RefinedExpCategory_Obj
  REC_Int : RefinedExpInterpretation REC_Obj

-------------------------------
-------------------------------
---- "Fixed" S-expressions ----
-------------------------------
-------------------------------

public export
ArityMap : Type -> Type
ArityMap atom = atom -> Nat

public export
data FSexpF : {atom : Type} -> ArityMap atom -> Type -> Type where
  FSop : {atom : Type} -> {arity : ArityMap atom} -> {carrier : Type} ->
    (a : atom) -> Tuple (arity a) carrier -> FSexpF {atom} arity carrier

public export
FSexpAlg : {atom : Type} -> ArityMap atom -> Type -> Type
FSexpAlg = Algebra . FSexpF

public export
FreeFSexp : {atom : Type} -> ArityMap atom -> Type -> Type
FreeFSexp = FreeMonad . FSexpF

public export
FreeFSalg : {atom : Type} -> ArityMap atom -> Type -> Type
FreeFSalg = FreeAlgebra . FSexpF

public export
MuFSexp : {atom : Type} -> ArityMap atom -> Type
MuFSexp = Mu . FSexpF

public export
FSexpCoalg : {atom : Type} -> ArityMap atom -> Type -> Type
FSexpCoalg = Coalgebra . FSexpF

public export
CofreeFSexp : {atom : Type} -> ArityMap atom -> Type -> Type
CofreeFSexp = CofreeComonad . FSexpF

public export
CofreeFScoalg : {atom : Type} -> ArityMap atom -> Type -> Type
CofreeFScoalg = CofreeCoalgebra . FSexpF

public export
NuFSexp : {atom : Type} -> ArityMap atom -> Type
NuFSexp = Nu . FSexpF

public export
record FSexpMorphCarrier {atom : Type} (arity : ArityMap atom) where
  constructor FSexpMorphBundle
  FSexpMorph : Type
  FSexpObj : Type
  FSexpDomain : FSexpMorph -> TupleP FSexpObj
  FSexpCodomain : FSexpMorph -> FSexpObj

{-
public export
data FSexpMorphF : {atom : Type} -> {arity : ArityMap atom} ->
    (expCarrier : Type) -> (morphCarrier : Type) ->
    (signature : morphCarrier -> (TupleP expCarrier, expCarrier))
    -}

--------------------------
--------------------------
---- The topos FinSet ----
--------------------------
--------------------------

public export
record FSTCarrier where

-----------------------------------------
---- Refined S-expressions and lists ----
-----------------------------------------

public export
FSexpRefinementAlg : {atom : Type} -> ArityMap atom -> Type -> Type -> Type
FSexpRefinementAlg {atom} arity carrier right =
  FSexpF arity (FSexpF arity carrier) -> Either (FreeFSexp arity carrier) right

public export
FSexpRefinement : {atom : Type} -> ArityMap atom -> Type -> Type -> Type
FSexpRefinement arity carrier right =
  FreeFSexp arity carrier -> Either (FreeFSexp arity carrier) right

public export
FreeFSexpRefinementAlg : {atom : Type} -> ArityMap atom ->
  Type -> Type -> Type -> Type
FreeFSexpRefinementAlg arity leftIn leftOut right =
  FreeFSexp arity leftIn -> Either (FreeFSexp arity leftOut) right

-------------------------------------------------
---- S-expressions with natural number atoms ----
-------------------------------------------------

public export
data NSexpClass : Type where
  NSexpNat : NSexpClass
  NSEXP : NSexpClass
  NSLIST : NSexpClass

public export
NSexpObject : Type
NSexpObject = ProductCatObject NSexpClass

public export
data NSexpFunctor : (carrier : NSexpObject) -> NSexpObject where
  NSatomF :
    NatF (carrier NSexpNat) ->
    NSexpFunctor carrier NSexpNat
  NSexpF :
    carrier NSexpNat -> carrier NSLIST ->
    NSexpFunctor carrier NSEXP
  NSlistF :
    ListF (carrier NSEXP) (carrier NSLIST) ->
    NSexpFunctor carrier NSLIST

public export
NSexpType : NSexpClass -> Type
NSexpType = MuProduct NSexpFunctor

public export
NSNat : Type
NSNat = NSexpType NSexpNat

public export
NSexp : Type
NSexp = NSexpType NSEXP

public export
NSList : Type
NSList = NSexpType NSLIST

public export
nsexpCata : ProductCatParamCata NSexpFunctor
nsexpCata v carrier alg type (InFreeProduct type term) = alg type $ case type of
  NSexpNat => nsexpCataNat term
  NSEXP => nsexpCataExp term
  NSLIST => nsexpCataList term
  where
  mutual
    nsexpCataNat :
      ProductCatTermFunctor
        NSexpFunctor v
        (ProductCatFreeMonad NSexpFunctor v) NSexpNat
        ->
      ProductCatTermFunctor NSexpFunctor v carrier NSexpNat
    nsexpCataNat (ProductCatTermVar t) = ProductCatTermVar t
    nsexpCataNat (ProductCatTermComposite com) = ProductCatTermComposite $
      case com of
        NSatomF a => NSatomF $ case a of
          ZeroF => ZeroF
          SuccF n => case n of
            InFreeProduct NSexpNat n =>
              SuccF $ alg NSexpNat $ nsexpCataNat n

    nsexpCataExp :
      ProductCatTermFunctor
        NSexpFunctor v
        (ProductCatFreeMonad NSexpFunctor v) NSEXP
        ->
      ProductCatTermFunctor NSexpFunctor v carrier NSEXP
    nsexpCataExp (ProductCatTermVar v) = ProductCatTermVar v
    nsexpCataExp (ProductCatTermComposite com) = ProductCatTermComposite $
      case com of
        NSexpF (InFreeProduct NSexpNat n) l =>
          case l of
            InFreeProduct NSLIST l' =>
              NSexpF
                (alg NSexpNat $ nsexpCataNat n) (alg NSLIST $ nsexpCataList l')

    nsexpCataList :
      ProductCatTermFunctor
        NSexpFunctor v
        (ProductCatFreeMonad NSexpFunctor v) NSLIST
        ->
      ProductCatTermFunctor NSexpFunctor v carrier NSLIST
    nsexpCataList (ProductCatTermVar v) = ProductCatTermVar v
    nsexpCataList (ProductCatTermComposite com) = ProductCatTermComposite $
      case com of
        NSlistF l => NSlistF $ case l of
          NilF => NilF
          ConsF (InFreeProduct NSEXP x) l' =>
            case l' of
              InFreeProduct NSLIST l'' =>
                ConsF
                  (alg NSEXP $ nsexpCataExp x)
                  (alg NSLIST $ nsexpCataList l'')

---------------------------------------------------------
---------------------------------------------------------
---- Interpretation of S-expressions into categories ----
---------------------------------------------------------
---------------------------------------------------------

public export
data UniversalProperty : Type where
  -- Equalizers and coequalizers.
  ConnectedLimits : UniversalProperty
  -- Initial algebras and terminal coalgebras of polynomial endofunctors.
  InductiveTypes : UniversalProperty

public export
data SexpCategory : Type where
  SubstCat : SexpCategory
  RefinedSubstCat : SexpCategory
  ADTCat : SexpCategory
  RefinedADTCat : SexpCategory

public export
hasProperty : UniversalProperty -> SexpCategory -> Bool
hasProperty ConnectedLimits SubstCat = False
hasProperty ConnectedLimits RefinedSubstCat = True
hasProperty ConnectedLimits ADTCat = False
hasProperty ConnectedLimits RefinedADTCat = True
hasProperty InductiveTypes SubstCat = False
hasProperty InductiveTypes RefinedSubstCat = False
hasProperty InductiveTypes ADTCat = True
hasProperty InductiveTypes RefinedADTCat = True

public export
SMorphismInterpretation : Type
SMorphismInterpretation =
  (domain : Type ** codomain : Type ** domain -> codomain)

public export
NatTransInterpretation : Type
NatTransInterpretation =
  (f : Type -> Type ** g : Type -> Type ** (x : Type) -> f x -> g x)

public export
data SexpInterpretation : NSexpClass -> Type where
  SnatAsNat : Nat -> SexpInterpretation NSexpNat
  SexpAsObject : Type -> SexpInterpretation NSEXP
  SexpAsMorphism : SMorphismInterpretation -> SexpInterpretation NSEXP
  SexpAsFunctor : (Type -> Type) -> SexpInterpretation NSEXP
  SexpAsNatTrans : NatTransInterpretation -> SexpInterpretation NSEXP
  SlistAsObjects : List Type -> SexpInterpretation NSLIST
  SlistAsMorphisms :
    List SMorphismInterpretation -> SexpInterpretation NSLIST
  SlistAsFunctors : List (Type -> Type) -> SexpInterpretation NSLIST
  SlistAsNatTrans : List NatTransInterpretation -> SexpInterpretation NSLIST

public export
record SexpCheckResult (inputType : NSexpClass) where
  constructor SexpInterpretations
  Input : NSexpType inputType
  InputInterpretation : Maybe (SexpInterpretation inputType)
  AllInterpretations :
    (type : NSexpClass) -> NSexpType type -> Maybe (SexpInterpretation type)

---------------------
---- Polynomials ----
---------------------

-- A univariate, finite-degree power.
public export
data PowerF : Type -> Type -> Type where
  FactorsF :
    ListF (coefficient, NatF carrier) carrier ->
    PowerF coefficient carrier

public export
Bifunctor PowerF where
  bimap f g (FactorsF l) = FactorsF $ bimap (bimap f $ map g) g l

export
powerFactors :
  PowerF coefficient carrier ->
  ListF (coefficient, NatF carrier) carrier
powerFactors (FactorsF l) = l

-- A univariate, finite-degree polynomial.
public export
data PolynomialF : Type -> Type -> Type where
  PolyTermsF :
    ListF (PowerF coefficient carrier) carrier ->
    PolynomialF coefficient carrier

public export
Bifunctor PolynomialF where
  bimap f g (PolyTermsF t) = PolyTermsF $ bimap (bimap f g) g t

export
polyTerms :
  PolynomialF coefficient carrier ->
  ListF (PowerF coefficient carrier) carrier
polyTerms (PolyTermsF t) = t

export
polyFactors :
  PolynomialF coefficient carrier ->
  ListF (ListF (coefficient, NatF carrier) carrier) carrier
polyFactors = mapFst powerFactors . polyTerms

-- Next, we introduce a way of interpreting polynomials as datatypes.
-- A polynomial endofunctor may be viewed as simply a polynomial, and
-- may be factored into one, but when representing types with
-- endofunctors, we may wish to factor out commonality amongst types
-- and compose them from smaller components. Such types could theoretically
-- be fully distributed into flat polynomials like `PolynomialF`, but
-- when using polynomials as types, we can gain expressivity with explicit
-- composition.
public export
data PolyTypeF : Type -> Type -> Type where
  PolyTypeComposeF : functor -> functor -> PolyTypeF type functor
  PolyTypeADTF : PolynomialF type functor -> PolyTypeF type functor

-- Next, we perform another recursion.  A programming language might define
-- an ADT as an initial algebra of a polynomial endofunctor.  So, we will
-- treat PolynomialF as representative of polynomial endofunctors, and
-- therefore potentially of ADTs.  To turn a polynomial endofunctor
-- which represents a non-recursive datatype into one which represents a
-- recursive type, we apply the above-defined higher-order functor,
-- `FreeMonad` (AKA `F*`).  So to generate polynomial _recursive_ types, we add
-- to `PolynomialF` the option of applying `FreeMonad` to an existing polynomial
-- type.
public export
data PolyRecTypeF : Type -> Type -> Type where
  PolyTypeFreeF :
    functor -> PolyRecTypeF type functor
  PolyRecTypeADTF :
    PolyTypeF type functor -> PolyRecTypeF type functor
