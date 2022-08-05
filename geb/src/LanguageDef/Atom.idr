module LanguageDef.Atom

import Library.IdrisUtils

%default total

-- This module implements decidable equality, ordering, and string
-- representation on an enumerated type, the one used within Geb
-- s-expressions; these are the kinds of things that a `deriving`
-- mechanism would provide automatically.

---------------------------------
---------------------------------
---- Atoms used in `GebTerm` ----
---------------------------------
---------------------------------

public export
data GebAtom : Type where
  PRODUCT : GebAtom
  COPRODUCT : GebAtom

  -- Must be last.
  NATVAL : Nat -> GebAtom

public export
gaEncode : GebAtom -> Nat
gaEncode PRODUCT = 0
gaEncode COPRODUCT = 1
gaEncode (NATVAL n) = 2 + n

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just PRODUCT
gaDecode 1 = Just COPRODUCT
gaDecode (S (S n)) = Just $ NATVAL n

public export
gaDecodeEncodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaDecodeEncodeIsJust PRODUCT = Refl
gaDecodeEncodeIsJust COPRODUCT = Refl
gaDecodeEncodeIsJust (NATVAL n) = Refl

public export
gaToString : GebAtom -> String
gaToString PRODUCT = ":*:"
gaToString COPRODUCT = ":+:"
gaToString (NATVAL n) = ":" ++ show n ++ ":"

public export
Show GebAtom where
  show a = gaToString a

public export
gaEq : GebAtom -> GebAtom -> Bool
gaEq a a' = gaEncode a == gaEncode a'

public export
Eq GebAtom where
  (==) = gaEq

public export
Ord GebAtom where
  a < a' = gaEncode a < gaEncode a'

public export
gaDecEq : (a, a' : GebAtom) -> Dec (a = a')
gaDecEq = encodingDecEq gaEncode gaDecode gaDecodeEncodeIsJust decEq

public export
DecEq GebAtom where
  decEq = gaDecEq
