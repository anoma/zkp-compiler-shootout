module LanguageDef.Test.PolyCatTest

import Test.TestLibrary
import LanguageDef.PolyCat

%default total

testBN0 : BoundedNat 7
testBN0 = MkBoundedNat 5

testNT0 : NTuple Nat 3
testNT0 = MkNTuple [11, 0, 5]

testBL0 : BoundedList String 4
testBL0 = MkBoundedList []

testBL1 : BoundedList String 4
testBL1 = MkBoundedList ["a"]

testBL2 : BoundedList String 4
testBL2 = MkBoundedList ["a", "b"]

testBL3 : BoundedList String 4
testBL3 = MkBoundedList ["a", "b", "c"]

testBL4 : BoundedList String 4
testBL4 = MkBoundedList ["a", "b", "c", "d"]

testPolyS0 : PolyShape
testPolyS0 = [(5, 3), (4, 11), (2, 1)]

testPolyS1 : PolyShape
testPolyS1 = [(5, 3), (4, 11), (4, 1)]

testPolyS2 : PolyShape
testPolyS2 = [(5, 3), (1, 11), (6, 1)]

testPolyS3 : PolyShape
testPolyS3 = [(5, 3), (1, 11), (0, 3)]

testPolyS4 : PolyShape
testPolyS4 = [(5, 3)]

testPolyS5 : PolyShape
testPolyS5 = []

testPolyS6 : PolyShape
testPolyS6 = [(3, 4), (1, 2), (0, 3)]

testPolyS7 : PolyShape
testPolyS7 = [(10, 1), (9, 3), (4, 2), (3, 1), (0, 2)]

testPolyS8 : PolyShape
testPolyS8 = [(4, 2), (2, 3), (0, 2)]

testPolyS9 : PolyShape
testPolyS9 = [(1, 1), (0, 1)]

poly0Valid : Assertion
poly0Valid = Assert $ validPoly testPolyS0 == True

poly1Valid : Assertion
poly1Valid = Assert $ validPoly testPolyS1 == False

poly2Valid : Assertion
poly2Valid = Assert $ validPoly testPolyS2 == False

poly3Valid : Assertion
poly3Valid = Assert $ validPoly testPolyS3 == True

poly4Valid : Assertion
poly4Valid = Assert $ validPoly testPolyS4 == True

poly5Valid : Assertion
poly5Valid = Assert $ validPoly testPolyS5 == True

poly6Valid : Assertion
poly6Valid = Assert $ validPoly testPolyS6 == True

testPoly0 : Polynomial
testPoly0 = MkPolynomial testPolyS0

testPoly3 : Polynomial
testPoly3 = MkPolynomial testPolyS3

testPoly4 : Polynomial
testPoly4 = MkPolynomial testPolyS4

testPoly5 : Polynomial
testPoly5 = MkPolynomial testPolyS5

testPoly6 : Polynomial
testPoly6 = MkPolynomial testPolyS6

testPoly7 : Polynomial
testPoly7 = MkPolynomial testPolyS7

testPoly8 : Polynomial
testPoly8 = MkPolynomial testPolyS8

testPoly9 : Polynomial
testPoly9 = MkPolynomial testPolyS9

poly0Degree : Assertion
poly0Degree = Assert $ degree testPoly0 == 5

poly5Degree : Assertion
poly5Degree = Assert $ degree testPoly5 == 0

poly0SumCoeff : Assertion
poly0SumCoeff = Assert $ sumCoeff testPoly0 == 15

poly3SumCoeff : Assertion
poly3SumCoeff = Assert $ sumCoeff testPoly3 == 17

poly4SumCoeff : Assertion
poly4SumCoeff = Assert $ sumCoeff testPoly4 == 3

poly5SumCoeff : Assertion
poly5SumCoeff = Assert $ sumCoeff testPoly5 == 0

poly6SumCoeff : Assertion
poly6SumCoeff = Assert $ sumCoeff testPoly6 == 9

poly7SumCoeff : Assertion
poly7SumCoeff = Assert $ sumCoeff testPoly7 == 9

poly7SumDir : Assertion
poly7SumDir = Assert $ sumPolyDir testPoly7 == 48

poly6Idx0 : Assertion
poly6Idx0 = Assert $ psIdx testPolyS6 0 == 3

poly6Idx1 : Assertion
poly6Idx1 = Assert $ psIdx testPolyS6 1 == 3

poly6Idx2 : Assertion
poly6Idx2 = Assert $ psIdx testPolyS6 2 == 3

poly6Idx3 : Assertion
poly6Idx3 = Assert $ psIdx testPolyS6 3 == 3

poly6Idx4 : Assertion
poly6Idx4 = Assert $ psIdx testPolyS6 4 == 1

poly6Idx5 : Assertion
poly6Idx5 = Assert $ psIdx testPolyS6 5 == 1

poly6Idx6 : Assertion
poly6Idx6 = Assert $ psIdx testPolyS6 6 == 0

poly6Idx7 : Assertion
poly6Idx7 = Assert $ psIdx testPolyS6 7 == 0

poly6Idx8 : Assertion
poly6Idx8 = Assert $ psIdx testPolyS6 8 == 0

poly6Idx9 : Assertion
poly6Idx9 = Assert $ psIdx testPolyS6 9 == 0

poly6Idx10 : Assertion
poly6Idx10 = Assert $ psIdx testPolyS6 10 == 0

poly1Idx0 : Assertion
poly1Idx0 = Assert $ psIdx testPolyS1 0 == 5

poly1Idx14 : Assertion
poly1Idx14 = Assert $ psIdx testPolyS1 14 == 4

poly1Idx15 : Assertion
poly1Idx15 = Assert $ psIdx testPolyS1 15 == 0

poly6Interp : Assertion
poly6Interp = Assert $ polyInterpNat testPoly6 7 == 1389

powerByMultsTestTerm : PolyTerm
powerByMultsTestTerm = (6, 5)

powerByMultsTest : Assertion
powerByMultsTest = Assert $
  ptInterpNat powerByMultsTestTerm 2 ==
  ptInterpNatByMults powerByMultsTestTerm 2

polyS0Scaled : PolyShape
polyS0Scaled = scaleMonPolyShape (2, 3) testPolyS0

testPoly0Scale : Assertion
testPoly0Scale = Assert $ polyS0Scaled == [(7, 9), (6, 33), (4, 3)]

testPoly0ScaleZero : Assertion
testPoly0ScaleZero = Assert $ scaleMonPolyShape (4, 0) testPolyS0 == []

testPolyS0p7 : PolyShape
testPolyS0p7 = addPolyShape testPolyS0 testPolyS7

testPolyS0m7 : PolyShape
testPolyS0m7 = mulPolyShape testPolyS0 testPolyS7

testPolyS0p7Correct : Assertion
testPolyS0p7Correct = Assert $
  testPolyS0p7 == [(10, 1), (9, 3), (5, 3), (4, 13), (3, 1), (2, 1), (0, 2)]

testPolyS0m7Correct : Assertion
testPolyS0m7Correct = Assert $
  testPolyS0m7 ==
    [(15, 3), (14, 20), (13, 33), (12, 1), (11, 3), (9, 6), (8, 25),
     (7, 11), (6, 2), (5, 7), (4, 22), (2, 2)]

poly0p7Valid : Assertion
poly0p7Valid = Assert $ validPoly testPolyS0p7 == True

poly0m7Valid : Assertion
poly0m7Valid = Assert $ validPoly testPolyS0m7 == True

testPoly0p7 : Polynomial
testPoly0p7 = MkPolynomial testPolyS0p7

testPoly0m7 : Polynomial
testPoly0m7 = MkPolynomial testPolyS0m7

testPolyS9exp4 : PolyShape
testPolyS9exp4 = expNPolyShape 4 testPolyS9

testPoly9exp4 : Polynomial
testPoly9exp4 = MkPolynomial testPolyS9exp4

testMulPolyNat0 : Assertion
testMulPolyNat0 = Assert $
  mulPolyShapeList [ expNPolyShape 3 testPolyS9, testPolyS0 ] ==
    mulPolyShapeList [ testPolyS9, testPolyS0, testPolyS9, testPolyS9 ]

testPolyNat : PolyShape
testPolyNat = [ (1, 1), (0, 1) ]

testPolyNatIter : Nat -> PolyShape
testPolyNatIter n = iterNPolyShape n testPolyNat

testParProdPolyList0 : Assertion
testParProdPolyList0 = Assert $
  parProdPolyShapeList [ testPolyS7, testPolyS8, testPolyS9 ] ==
    parProdPolyShape (parProdPolyShape testPolyS7 testPolyS8) testPolyS9

polyEx58p : PolyShape
polyEx58p = [ (2, 1), (1, 1) ]

polyEx58q : PolyShape
polyEx58q = [ (3, 1), (0, 1) ]

polyEx58_1 : Assertion
polyEx58_1 = Assert $
  composePolyShape (homNPolyShape 2) polyEx58q == [(6, 1), (3, 2), (0, 1)]

polyEx58_2 : Assertion
polyEx58_2 = Assert $
  composePolyShape (homNPolyShape 1) polyEx58q == [(3, 1), (0, 1)]

polyEx58_3 : Assertion
polyEx58_3 = Assert $ composePolyShape
  (addPolyShape (homNPolyShape 2) (homNPolyShape 1)) polyEx58q ==
    [(6, 1), (3, 3), (0, 2)]

polyShapeExpTo1 : Assertion
polyShapeExpTo1 = Assert $
  polyShapeExponential testPolyS7 terminalPolyShape == testPolyS7

polyShape1ToExp : Assertion
polyShape1ToExp = Assert $
  polyShapeExponential terminalPolyShape testPolyS7 == terminalPolyShape

polyEx293p : PolyShape
polyEx293p = [ (2, 2), (1, 3) ]

polyEx293q : PolyShape
polyEx293q = [ (4, 1), (3, 3) ]

ex378_6 : Assertion
ex378_6 = Assert $
  parProdClosureShape [(2, 1), (1,2)] [(3, 2), (0, 3)] ==
    [(9, 64), (6, 204), (3, 180), (0, 27)]

sumViaMu : Nat -> Nat -> Nat
sumViaMu m n = muToNat $ natSum (natToMu m) (natToMu n)

mulViaMu : Nat -> Nat -> Nat
mulViaMu m n = muToNat $ natMul (natToMu m) (natToMu n)

powViaMu : Nat -> Nat -> Nat
powViaMu m n = muToNat $ natPow (natToMu m) (natToMu n)

testMuNatSum0 : Assertion
testMuNatSum0 = Assert $ sumViaMu 0 0 == 0

testMuNatSum1 : Assertion
testMuNatSum1 = Assert $ sumViaMu 0 1 == 1

testMuNatSum2 : Assertion
testMuNatSum2 = Assert $ sumViaMu 1 0 == 1

testMuNatSum3 : Assertion
testMuNatSum3 = Assert $ sumViaMu 1 1 == 2

testMuNatSum4 : Assertion
testMuNatSum4 = Assert $ sumViaMu 1 2 == 3

testMuNatSum5 : Assertion
testMuNatSum5 = Assert $ sumViaMu 2 1 == 3

testMuNatSum6 : Assertion
testMuNatSum6 = Assert $ sumViaMu 2 2 == 4

testMuNatSum7 : Assertion
testMuNatSum7 = Assert $ sumViaMu 12 7 == 19

testMuNatMul0 : Assertion
testMuNatMul0 = Assert $ mulViaMu 0 0 == 0

testMuNatMul1 : Assertion
testMuNatMul1 = Assert $ mulViaMu 0 1 == 0

testMuNatMul2 : Assertion
testMuNatMul2 = Assert $ mulViaMu 1 0 == 0

testMuNatMul3 : Assertion
testMuNatMul3 = Assert $ mulViaMu 1 1 == 1

testMuNatMul4 : Assertion
testMuNatMul4 = Assert $ mulViaMu 1 2 == 2

testMuNatMul5 : Assertion
testMuNatMul5 = Assert $ mulViaMu 2 1 == 2

testMuNatMul6 : Assertion
testMuNatMul6 = Assert $ mulViaMu 2 2 == 4

testMuNatMul7 : Assertion
testMuNatMul7 = Assert $ mulViaMu 12 7 == 84

testMuNatPow0 : Assertion
testMuNatPow0 = Assert $ powViaMu 0 0 == 1

testMuNatPow1 : Assertion
testMuNatPow1 = Assert $ powViaMu 0 1 == 0

testMuNatPow2 : Assertion
testMuNatPow2 = Assert $ powViaMu 1 0 == 1

testMuNatPow3 : Assertion
testMuNatPow3 = Assert $ powViaMu 1 1 == 1

testMuNatPow4 : Assertion
testMuNatPow4 = Assert $ powViaMu 1 2 == 1

testMuNatPow5 : Assertion
testMuNatPow5 = Assert $ powViaMu 2 1 == 2

testMuNatPow6 : Assertion
testMuNatPow6 = Assert $ powViaMu 2 2 == 4

testMuNatPow7 : Assertion
testMuNatPow7 = Assert $ powViaMu 2 3 == 8

testMuNatPow8 : Assertion
testMuNatPow8 = Assert $ powViaMu 3 2 == 9

testMuNatPow9 : Assertion
testMuNatPow9 = Assert $ powViaMu 4 2 == 16

testMuNatPow10 : Assertion
testMuNatPow10 = Assert $ powViaMu 2 4 == 16

testMuNatPow11 : Assertion
testMuNatPow11 = Assert $ powViaMu 2 5 == 32

testMuNatPow12 : Assertion
testMuNatPow12 = Assert $ powViaMu 5 2 == 25

testMuNatPow13 : Assertion
testMuNatPow13 = Assert $ powViaMu 5 3 == 125

testPre0 : NatPreMeta 1
testPre0 = metaToPre 0 1

testPre1 : NatPreMeta 2
testPre1 = metaToPre 0 2

testPre2 : NatPreMeta 2
testPre2 = metaToPre 1 2

testPre3 : NatPreMeta 4
testPre3 = metaToPre 1 4

testPre4 : NatPreMeta 4
testPre4 = metaToPre 2 4

testPre5 : NatPreMeta 4
testPre5 = metaToPre 3 4

--------------------------------------
---- RangedNat and RangedNatMorph ----
--------------------------------------

testRNMPolyS0 : PolyShape
testRNMPolyS0 = [ (4, 2), (3, 1), (0, 7) ]

testRNMPolyS0Valid : Assertion
testRNMPolyS0Valid = Assert $ validPoly testRNMPolyS0

testRNMPolyS1 : PolyShape
testRNMPolyS1 = [(1, 1), (0, 1)]

testRNMPolyS1Valid : Assertion
testRNMPolyS1Valid = Assert $ validPoly testRNMPolyS1

testRNM0 : MuRNM
testRNM0 = RNMPoly (2, 5) testRNMPolyS0

testRNM0Codomain : Assertion
testRNM0Codomain = Assert $ rnmCheck testRNM0 == Just ((2, 5), (47, 1382))

testRNM0Apply3 : Assertion
testRNM0Apply3 = Assert $ interpRNM testRNM0 3 == 196

testRNM0Apply4 : Assertion
testRNM0Apply4 = Assert $ interpRNM testRNM0 4 == 583

testRNM2 : MuRNM
testRNM2 = RNMPoly (6, 10) [ (1, 1), (0, 41) ]

testRNM2Apply6 : Assertion
testRNM2Apply6 = Assert $ interpRNM testRNM2 6 == 47

testRNM2Apply10 : Assertion
testRNM2Apply10 = Assert $ interpRNM testRNM2 10 == 51

testRNM2Sig : Assertion
testRNM2Sig = Assert $ rnmCheck testRNM2 == Just ((6, 10), (47, 51))

testRNM3 : MuRNM
testRNM3 = RNMSwitch 6 testRNM0 testRNM2

testRNM3Sig : Assertion
testRNM3Sig = Assert $ rnmCheck testRNM3 == Nothing

testRNM4 : MuRNM
testRNM4 = RNMExtendCodAbove testRNM2 1382

testRNM4Sig : Assertion
testRNM4Sig = Assert $ rnmCheck testRNM4 == Just ((6, 10), (47, 1382))

testRNM5 : MuRNM
testRNM5 = RNMSwitch 6 testRNM0 testRNM4

testRNM5Sig : Assertion
testRNM5Sig = Assert $ rnmCheck testRNM5 == Just ((2, 10), (47, 1382))

testRNM5Apply2 : Assertion
testRNM5Apply2 = Assert $ interpRNM testRNM5 2 == 47

testRNM5Apply3 : Assertion
testRNM5Apply3 = Assert $ interpRNM testRNM5 3 == 196

testRNM5Apply4 : Assertion
testRNM5Apply4 = Assert $ interpRNM testRNM5 4 == 583

testRNM5Apply5 : Assertion
testRNM5Apply5 = Assert $ interpRNM testRNM5 5 == 1382

testRNM5Apply6 : Assertion
testRNM5Apply6 = Assert $ interpRNM testRNM5 6 == 47

testRNM5Apply10 : Assertion
testRNM5Apply10 = Assert $ interpRNM testRNM5 10 == 51

testRNM6 : MuRNM
testRNM6 = RNMExtendCodBelow testRNM5 46

testRNM6Sig : Assertion
testRNM6Sig = Assert $ rnmCheck testRNM6 == Just ((2, 10), (46, 1382))

testRNM6Apply2 : Assertion
testRNM6Apply2 = Assert $ interpRNM testRNM6 2 == 47

testRNM7 : MuRNM
testRNM7 = RNMDiv (122, 401) 7

testRNM7Sig : Assertion
testRNM7Sig = Assert $ rnmCheck testRNM7 == Just ((122, 401), (17, 57))

testRNM7Apply122 : Assertion
testRNM7Apply122 = Assert $ interpRNM testRNM7 122 == 17

testRNM7Apply200 : Assertion
testRNM7Apply200 = Assert $ interpRNM testRNM7 200 == 28

testRNM7Apply210 : Assertion
testRNM7Apply210 = Assert $ interpRNM testRNM7 210 == 30

testRNM7Apply401 : Assertion
testRNM7Apply401 = Assert $ interpRNM testRNM7 401 == 57

testRNM8 : MuRNM
testRNM8 = RNMMod (122, 401) 7

testRNM8Sig : Assertion
testRNM8Sig = Assert $ rnmCheck testRNM8 == Just ((122, 401), (0, 6))

testRNM8Apply122 : Assertion
testRNM8Apply122 = Assert $ interpRNM testRNM8 122 == 3

testRNM8Apply200 : Assertion
testRNM8Apply200 = Assert $ interpRNM testRNM8 200 == 4

testRNM8Apply210 : Assertion
testRNM8Apply210 = Assert $ interpRNM testRNM8 210 == 0

testRNM8Apply401 : Assertion
testRNM8Apply401 = Assert $ interpRNM testRNM8 401 == 2

testRNM8Apply202 : Assertion
testRNM8Apply202 = Assert $ interpRNM testRNM8 202 == 6

testRNM9 : MuRNM
testRNM9 = rnmId (37, 122)

testRNM9Sig : Assertion
testRNM9Sig = Assert $ rnmCheck testRNM9 == Just ((37, 122), (37, 122))

testRNM9Apply100 : Assertion
testRNM9Apply100 = Assert $ interpRNM testRNM9 100 == 100

testRNM10 : MuRNM
testRNM10 = RNMPoly (45, 1382) [ (1, 2) ]

testRNM10Sig : Assertion
testRNM10Sig = Assert $ rnmCheck testRNM10 == Just ((45, 1382), (90, 2764))

testRNM11 : MuRNM
testRNM11 = RNMCompose testRNM10 testRNM6

testRNM11Sig : Assertion
testRNM11Sig = Assert $ rnmCheck testRNM11 == Nothing

testRNM12 : MuRNM
testRNM12 = RNMPoly (46, 1382) [ (1, 2) ]

testRNM12Sig : Assertion
testRNM12Sig = Assert $ rnmCheck testRNM12 == Just ((46, 1382), (92, 2764))

testRNM13 : MuRNM
testRNM13 = RNMCompose testRNM12 testRNM6

testRNM13Sig : Assertion
testRNM13Sig = Assert $ rnmCheck testRNM13 == Just ((2, 10), (92, 2764))

testRNM13Apply2 : Assertion
testRNM13Apply2 = Assert $ interpRNM testRNM13 2 == 94

testRNM13Apply4 : Assertion
testRNM13Apply4 = Assert $ interpRNM testRNM13 4 == 1166

testRNM13Apply10 : Assertion
testRNM13Apply10 = Assert $ interpRNM testRNM13 10 == 102

testRNM14 : MuRNM
testRNM14 = RNMRestrictDomAbove testRNM13 8

testRNM14Sig : Assertion
testRNM14Sig = Assert $ rnmCheck testRNM14 == Just ((2, 8), (92, 2764))

testRNM15 : MuRNM
testRNM15 = RNMRestrictDomBelow testRNM14 4

testRNM15Sig : Assertion
testRNM15Sig = Assert $ rnmCheck testRNM15 == Just ((4, 8), (92, 2764))

testRNM15Apply6 : Assertion
testRNM15Apply6 = Assert $ interpRNM testRNM15 6 == interpRNM testRNM13 6

---------------------------------------
---- Augmented range-nat morphisms ----
---------------------------------------

testARNM0 : AugRNM
testARNM0 = Right $ RNMPoly (0, 0) [ (0, 0), (1, 0) ]

testARNM0Sig : Assertion
testARNM0Sig = Assert $ arnmCheck testARNM0 == Nothing

testARNM1 : AugRNM
testARNM1 = Left Nothing

testARNM1Sig : Assertion
testARNM1Sig = Assert $ arnmCheck testARNM1 == Just (Nothing, Nothing)

testARNM2 : AugRNM
testARNM2 = Left (Just (5, 10))

testARNM2Sig : Assertion
testARNM2Sig = Assert $ arnmCheck testARNM2 == Just (Nothing, Just (5, 10))

testARNM3 : AugRNM
testARNM3 = Right testRNM15

testARNM3Sig : Assertion
testARNM3Sig = Assert $
  arnmCheck testARNM3 == Just (Just (4, 8), Just (92, 2764))

-----------------------
-----------------------
---- Nat as object ----
-----------------------
-----------------------

bbt1 : Assertion
bbt1 = Assert $ BoundedBy 4 0

bbt2 : Assertion
bbt2 = Assert $ BoundedBy 4 3

bbt3 : Assertion
bbt3 = Assert $ NotBoundedBy 4 4

bbt4 : Assertion
bbt4 = Assert $ NotBoundedBy 4 5

but1 : BUNat 4
but1 = Left ()

bat1 : BANat 4
bat1 = u2a but1

bat2 : BANat 4
bat2 = MkBANat 3

but2 : BUNat 4
but2 = a2u bat2

tbut21 : Assertion
tbut21 = Assert $ MkBUNat {n=4} 3 == but2

tbut22 : Assertion
tbut22 = Assert $ u2a but2 == bat2

bnclm0 : BNCListMorph
bnclm0 = [ 3, 1, 5, 0 ]

bnclm1 : BNCListMorph
bnclm1 = [ 6, 1 ]

bnclm2 : BNCListMorph
bnclm2 = []

bnclmt0 : Assertion
bnclmt0 = Assert $ checkVBNCLM 4 6 bnclm0

bncvlm0 : VBNCLM 4 6
bncvlm0 = MkVBNCLM bnclm0

bnclmt1 : Assertion
bnclmt1 = Assert $ not $ checkVBNCLM 4 5 bnclm0

bnclmt2 : Assertion
bnclmt2 = Assert $ checkVBNCLM 4 7 bnclm0

bnclmt3 : Assertion
bnclmt3 = Assert $ not $ checkVBNCLM 3 6 bnclm0

bnclmt4 : Assertion
bnclmt4 = Assert $ not $ checkVBNCLM 5 6 bnclm0

bnclmt5 : Assertion
bnclmt5 = Assert $ not $ checkVBNCLM 2 7 bnclm0

bnclmt6 : Assertion
bnclmt6 = Assert $ checkVBNCLM 2 7 bnclm1

bnclmt7 : Assertion
bnclmt7 = Assert $ checkVBNCLM 0 0 bnclm2

bnclmt8 : Assertion
bnclmt8 = Assert $ checkVBNCLM 0 1 bnclm2

bnclmt9 : Assertion
bnclmt9 = Assert $ not $ checkVBNCLM 1 0 bnclm2

bnclmt10 : Assertion
bnclmt10 = Assert $ not $ checkVBNCLM 1 1 bnclm2
-- bnclm0 = [ 3, 1, 5, 0 ]

bnclmt11 : Assertion
bnclmt11 = Assert $ bncLMANN bncvlm0 0 == 3

bnclmt12 : Assertion
bnclmt12 = Assert $ bncLMANN bncvlm0 1 == 1

bnclmt13 : Assertion
bnclmt13 = Assert $ bncLMANN bncvlm0 2 == 5

bnclmt14 : Assertion
bnclmt14 = Assert $ bncLMANN bncvlm0 3 == 0

bncpm0 : BNCPolyM
bncpm0 = #| 4 #+ #| 2 #* PI #^ 3 #+ PI #^ 4

bncpm0mod200 : BANat 200 -> BANat 200
bncpm0mod200 = baPolyM bncpm0

bncpm0mod100 : BANat 200 -> BANat 100
bncpm0mod100 = baPolyM bncpm0

bncpm1 : BNCPolyM
bncpm1 = (PI #+ #| 1) #^ 3

bncpmt0 : Assertion
bncpmt0 = Assert $ metaBNCPolyM 200 bncpm0 0 == 4

bncpmt1 : Assertion
bncpmt1 = Assert $ metaBNCPolyM 200 bncpm1 0 == 1

bncpmt2 : Assertion
bncpmt2 = Assert $ metaBNCPolyM 200 bncpm0 1 == 7

bncpmt3 : Assertion
bncpmt3 = Assert $ metaBNCPolyM 200 bncpm1 1 == 8

bncpmt4 : Assertion
bncpmt4 = Assert $ metaBNCPolyM 200 bncpm0 2 == 36

bncpmt5 : Assertion
bncpmt5 = Assert $ metaBNCPolyM 200 bncpm1 2 == 27

bncpmt6 : Assertion
bncpmt6 = Assert $ metaBNCPolyM 200 bncpm0 3 == 139

bncpmt7 : Assertion
bncpmt7 = Assert $ metaBNCPolyM 200 bncpm1 3 == 64

bncpmt8 : Assertion
bncpmt8 = Assert $ metaBNCPolyM 100 bncpm0 3 == 38

bncpmt9 : Assertion
bncpmt9 = Assert $ fst0 (bncpm0mod200 (MkBANat 3)) == 139

bncpmt10 : Assertion
bncpmt10 = Assert $ fst0 (bncpm0mod100 (MkBANat 3)) == 39

bncpmt11 : Assertion
bncpmt11 = Assert $ metaBNCPolyM 200 (bncpm0 #- bncpm1) 3 == 75

bncpmt12 : Assertion
bncpmt12 = Assert $ metaBNCPolyM 200 (bncpm1 #- bncpm0) 3 == -75

bncpmt13 : Assertion
bncpmt13 = Assert $ metaBNCPolyM 200 (bncpm0 #/ bncpm1) 3 == 2

bncpmt14 : Assertion
bncpmt14 = Assert $ metaBNCPolyM 200 (bncpm1 #/ bncpm0) 3 == 0

bncpmt15 : Assertion
bncpmt15 = Assert $ metaBNCPolyM 200 (bncpm0 #% bncpm1) 3 == 11

bncpmt16 : Assertion
bncpmt16 = Assert $ metaBNCPolyM 200 (bncpm1 #% bncpm0) 3 == 64

bncpmt17 : Assertion
bncpmt17 = Assert $
  metaBNCPolyM 200 (IfZero (bncpm0 #/ bncpm1) bncpm0 bncpm1) 3 == 64

bncpmt18 : Assertion
bncpmt18 = Assert $
  metaBNCPolyM 200 (IfZero (bncpm1 #/ bncpm0) bncpm0 bncpm1) 3 == 139

bncpmt19 : Assertion
bncpmt19 = Assert $
  metaBNCPolyM 100 (IfZero (bncpm0 #/ bncpm1) bncpm0 bncpm1) 3 == 64

bncpmt20 : Assertion
bncpmt20 = Assert $
  metaBNCPolyM 100 (IfZero (bncpm1 #/ bncpm0) bncpm0 bncpm1) 3 == 38

bncpmt21 : Assertion
bncpmt21 = Assert $ metaBNCPolyM 200 (bncpm1 #. (bncpm0 #/ bncpm1)) 3 == 27

---------------
---------------
---- PolyF ----
---------------
---------------

polybool : PolyMu
polybool = Poly1 $+ Poly1

polyfnat : PolyMu
polyfnat = Poly1 $+ PolyI

polyf0 : PolyMu
polyf0 = (polyfnat $. Poly1) $*^ 5

polyf1 : PolyMu
polyf1 = (Poly1 $+ PolyI $*^ 2) $.^ 3

polyf2 : PolyMu
polyf2 = polyf0 $.^ 0

Polyf0f : Type -> Type
Polyf0f = MetaPolyFMetaF polyf0

Polyf1f : Type -> Type
Polyf1f = MetaPolyFMetaF polyf1

Polyf2f : Type -> Type
Polyf2f = MetaPolyFMetaF polyf2

Polyf0t : Type
Polyf0t = ConstComponent polyf0

Polyf1t : Type
Polyf1t = ConstComponent polyf1

Polyf2t : Type
Polyf2t = ConstComponent polyf2

polyf0i : Polyf0t
polyf0i = (Left (), Left (), Right (), Left (), Right ())

polyf2i : Not Polyf2t
polyf2i = id

PolyFreeNat : (0 _ : Type) -> Type
PolyFreeNat = MetaPolyFreeM polyfnat

PolyNat : Type
PolyNat = MetaPolyMu polyfnat

polyFNatT0 : PolyFreeNat Nat
polyFNatT0 = InFVar 7

polyFNatT1 : PolyFreeNat Nat
polyFNatT1 = InFCom $ Left ()

polyFNatT2 : PolyFreeNat Nat
polyFNatT2 = InFCom $ Right $ InFVar 5

polyFNatT3 : PolyFreeNat Nat
polyFNatT3 = InFCom $ Right $ InFCom $ Left ()

polyFNatT4 : PolyFreeNat Nat
polyFNatT4 = InFCom $ Right $ InFCom $ Right $ InFVar 3

polyFNatT5 : PolyFreeNat Nat
polyFNatT5 = InFCom $ Right $ InFCom $ Right $ InFCom $ Left ()

polyFNatT6 : PolyFreeNat Nat
polyFNatT6 = InFCom $ Right $ InFCom $ Right $ InFCom $ Right $ InFCom $ Left ()

polynatT0 : PolyNat
polynatT0 = InFCom $ Left ()

polynatT1 : PolyNat
polynatT1 = InFCom $ Right $ InFCom $ Left ()

polynatT2 : PolyNat
polynatT2 = InFCom $ Right $ InFCom $ Right $ InFCom $ Left ()

polyNatIter : Nat -> PolyMu
polyNatIter = ($.^) polyfnat

polyNatIterFixed : Nat -> PolyMu
polyNatIterFixed n = polyNatIter n $. Poly0

PolyNatIter : Nat -> Type
PolyNatIter = ConstComponent . polyNatIter

pniterT0 : Not $ PolyNatIter 0
pniterT0 = id

pniterT1 : PolyNatIter 1
pniterT1 = ()

pniterT2 : PolyNatIter 2
pniterT2 = Left ()

pniterT3 : PolyNatIter 2
pniterT3 = Right ()

pniterT4 : PolyNatIter 3
pniterT4 = Left ()

pniterT5 : PolyNatIter 3
pniterT5 = Right $ Left ()

pniterT6 : PolyNatIter 3
pniterT6 = Right $ Right ()

pniterT7 : PolyNatIter 4
pniterT7 = Left ()

pniterT8 : PolyNatIter 4
pniterT8 = Right $ Left ()

pniterT9 : PolyNatIter 4
pniterT9 = Right $ Right $ Left ()

pniterT10 : PolyNatIter 4
pniterT10 = Right $ Right $ Right ()

polyfeqT0 : Assertion
polyfeqT0 = Assert $ polyfnat /= polyNatIter 0

polyfeqT1 : Assertion
polyfeqT1 = Assert $ polyfnat == polyNatIter 1

polyfeqT2 : Assertion
polyfeqT2 = Assert $ polyfnat /= polyNatIter 2

polyHomBoolF0 : PolyMu
polyHomBoolF0 = PolyHomObj polybool polyf0

polyCardT0 : Assertion
polyCardT0 = Assert $
  polyTCard polyHomBoolF0 == power (polyTCard polyf0) (polyTCard polybool)

polyHomId4Id : PolyMu
polyHomId4Id = PolyHomObj PolyI (4 $:* PolyI)

twoBits : PolyMu
twoBits = polybool $* polybool

polyHomId4Id' : PolyMu
polyHomId4Id' = PolyHomObj PolyI (twoBits $* PolyI)

polyHom4IdId : PolyMu
polyHom4IdId = PolyHomObj (4 $:* PolyI) PolyI

polyHom4IdId' : PolyMu
polyHom4IdId' = PolyHomObj (twoBits $* PolyI) PolyI

polyDepth3BinTree : PolyMu
polyDepth3BinTree = polyf1

polyDepth3BinTreeFixed : PolyMu
polyDepth3BinTreeFixed = polyDepth3BinTree $. Poly0

------------------------------------------
------------------------------------------
---- Metalanguage polynomial functors ----
------------------------------------------
------------------------------------------

data BinBoolTreePos : Type where
  BBLeaf : Bool -> BinBoolTreePos
  BBNode : BinBoolTreePos

data BinBoolTreeDir : BinBoolTreePos -> Type where
  BBLeft : BinBoolTreeDir BBNode
  BBRight : BinBoolTreeDir BBNode

BinBoolTreeLeafVoid : {0 x : Type} -> {0 b : Bool} ->
  BinBoolTreeDir (BBLeaf b) -> x
BinBoolTreeLeafVoid BBLeft impossible
BinBoolTreeLeafVoid BBRight impossible

BinBoolTreePF : PolyFunc
BinBoolTreePF = (BinBoolTreePos ** BinBoolTreeDir)

BinBoolTreeF : Type -> Type
BinBoolTreeF = InterpPolyFunc BinBoolTreePF

InBBLeaf : {ty : Type} -> Bool -> BinBoolTreeF ty
InBBLeaf b = (BBLeaf b ** BinBoolTreeLeafVoid)

InBBDir : {0 ty : BinBoolTreeDir BBNode -> Type} ->
  ty BBLeft -> ty BBRight -> (d : BinBoolTreeDir BBNode) -> ty d
InBBDir l r BBLeft = l
InBBDir l r BBRight = r

BinBoolTree1 : Type
BinBoolTree1 = BinBoolTreeF Void

binBoolTree1False : BinBoolTree1
binBoolTree1False = InBBLeaf False

binBoolTree1True : BinBoolTree1
binBoolTree1True = InBBLeaf True

BinBoolTree2 : Type
BinBoolTree2 = BinBoolTreeF BinBoolTree1

binBoolTree1Test : BinBoolTree2
binBoolTree1Test = (BBNode ** InBBDir (InBBLeaf True) (InBBLeaf False))

BBFMFT : Type
BBFMFT = PolyFuncFreeMFromTranslate BinBoolTreePF Nat

BBFM : PolyFunc
BBFM = PolyFuncFreeM BinBoolTreePF

BBFMFF : Type
BBFMFF = InterpPolyFuncFreeM BinBoolTreePF Nat

------------------------------------
---- Unrefined polynomial types ----
------------------------------------

initObj : SubstObjMu
initObj = Subst0

termObj : SubstObjMu
termObj = Subst1

-- Unary natural numbers less than 7.
unat7 : SubstObjMu
unat7 = SUNat 7

-- Four-bit binary natural numbers.
bnat4 : SubstObjMu
bnat4 = SBNat 4

-- 0 as a term of bnat4.
bnat4_0 : SOTerm PolyCatTest.bnat4
bnat4_0 =
  SMPair (SMInjLeft Subst1 Subst1) $ SMPair (SMInjLeft Subst1 Subst1) $
    SMPair (SMInjLeft Subst1 Subst1) (SMInjLeft Subst1 Subst1)

-- 1 as a term of bnat4.
bnat4_1 : SOTerm PolyCatTest.bnat4
bnat4_1 =
  SMPair (SMInjLeft Subst1 Subst1) $ SMPair (SMInjLeft Subst1 Subst1) $
    SMPair (SMInjLeft Subst1 Subst1) (SMInjRight Subst1 Subst1)

-- 2 as a term of bnat4.
bnat4_2 : SOTerm PolyCatTest.bnat4
bnat4_2 =
  SMPair (SMInjLeft Subst1 Subst1) $ SMPair (SMInjLeft Subst1 Subst1) $
    SMPair (SMInjRight Subst1 Subst1) (SMInjLeft Subst1 Subst1)

-- 15 as a term of bnat4.
bnat4_15 : SOTerm PolyCatTest.bnat4
bnat4_15 =
  SMPair (SMInjRight Subst1 Subst1) $ SMPair (SMInjRight Subst1 Subst1) $
    SMPair (SMInjRight Subst1 Subst1) (SMInjRight Subst1 Subst1)

-- Mappings from bnat4 to bool (which are characteristic functions of
-- subsets of bnat4).
bnat4_to_bool : Type
bnat4_to_bool = SubstMorph bnat4 SubstBool

-- Extract bit2 from bnat4 (its second-most-significant bit).
bnat4_bit_2 : PolyCatTest.bnat4_to_bool
bnat4_bit_2 = SMCase SFalse STrue <! SMProjLeft _ _ <! SMProjRight _ _

-- The exponential object representing functions from Bool to Bool.
boolToBool : SubstObjMu
boolToBool = SubstHomObj SubstBool SubstBool

b2bid : SubstMorph SubstBool SubstBool
b2bid = SMId SubstBool

b2bidTerm : HomTerm SubstBool SubstBool
b2bidTerm = MorphAsTerm b2bid

b2bid_eval_t : SOTerm SubstBool
b2bid_eval_t = soEval _ _ <! SMPair b2bidTerm STrue

b2bid_eval_f : SOTerm SubstBool
b2bid_eval_f = soEval _ _ <! SMPair b2bidTerm SFalse

b2bid_gn : Nat
b2bid_gn = substMorphToGNum b2bid

b2bnot : SubstMorph SubstBool SubstBool
b2bnot = SNot

b2bnot_gn : Nat
b2bnot_gn = substMorphToGNum b2bnot

b2bnotnot : SubstMorph SubstBool SubstBool
b2bnotnot = SNot <! SNot

b2bnotnotTerm : HomTerm SubstBool SubstBool
b2bnotnotTerm = MorphAsTerm b2bnotnot

b2bnotnot_eval_t : SOTerm SubstBool
b2bnotnot_eval_t = soEval _ _ <! SMPair b2bnotnotTerm STrue

b2bnotnot_eval_f : SOTerm SubstBool
b2bnotnot_eval_f = soEval _ _ <! SMPair b2bnotnotTerm SFalse

b2bnotnot_gn : Nat
b2bnotnot_gn = substMorphToGNum b2bnotnot

b2btrue : SubstMorph SubstBool SubstBool
b2btrue = soConst {x=SubstBool} STrue

b2btrue_gn : Nat
b2btrue_gn = substMorphToGNum b2btrue

b2bfalse : SubstMorph SubstBool SubstBool
b2bfalse = soConst {x=SubstBool} SFalse

b2bfalse_gn : Nat
b2bfalse_gn = substMorphToGNum b2bfalse

-- The exponential object representing mappings from bnat4 to bool (which
-- are characteristic functions of subsets of bnat4).
bnat4chi : SubstObjMu
bnat4chi = bnat4 !-> SubstBool

bnat4_bit_2_gn : Nat
bnat4_bit_2_gn = substMorphToGNum bnat4_bit_2

bnat4chi_gn_0 : Maybe PolyCatTest.bnat4_to_bool
bnat4chi_gn_0 = substGNumToMorph bnat4 SubstBool 0

bnat4chi_gn_65535 : Maybe PolyCatTest.bnat4_to_bool
bnat4chi_gn_65535 = substGNumToMorph bnat4 SubstBool 65535

bnat4chi_gn_65536 : Maybe PolyCatTest.bnat4_to_bool
bnat4chi_gn_65536 = substGNumToMorph bnat4 SubstBool 65536

-- Unary bytes
u_byte : SubstObjMu
u_byte = SUNat 8

unat_b : (n : Nat) -> {auto lt : IsYesTrue (isLT n 8)} ->
  SOTerm PolyCatTest.u_byte
unat_b n {lt} = MkSUNat {m=8} {lt} n

unat_20 : (n : Nat) -> {auto lt : IsYesTrue (isLT n 20)} -> SOTerm (SUNat 20)
unat_20 n {lt} = MkSUNat {m=20} {lt} n

-- An up-to-length-5 list of (unary) bytes.
list_depth_5 : SubstObjMu
list_depth_5 = SList 5 u_byte

l0_empty : SOTerm (SList 0 PolyCatTest.u_byte)
l0_empty = sListNil {n=0} {x=u_byte}

l5_empty : SOTerm PolyCatTest.list_depth_5
l5_empty = sListPromoteN {m=0} {n=5} <! l0_empty

l1_1 : SOTerm (SList 1 PolyCatTest.u_byte)
l1_1 = sListEvalCons {n=0} (MkSUNat {m=8} 1) l0_empty

l5_1 : SOTerm PolyCatTest.list_depth_5
l5_1 = sListPromoteN {m=1} {n=5} <! l1_1

l2_2 : SOTerm (SList 2 PolyCatTest.u_byte)
l2_2 = sListEvalCons {n=1} (MkSUNat {m=8} 2) l1_1

l3_3 : SOTerm (SList 3 PolyCatTest.u_byte)
l3_3 = sListEvalCons {n=2} (MkSUNat {m=8} 3) l2_2

l4_4 : SOTerm (SList 4 PolyCatTest.u_byte)
l4_4 = sListEvalCons {n=3} (MkSUNat {m=8} 4) l3_3

l5_5 : SOTerm PolyCatTest.list_depth_5
l5_5 = sListEvalCons {n=4} (MkSUNat {m=8} 5) l4_4

addb_20 : SubstMorph (PolyCatTest.u_byte !* SUNat 20) (SUNat 20)
addb_20 = suAdd {n=20} <!
  SMPair
    (suPromoteN {m=8} {n=20} <! SMProjLeft _ _)
    (SMProjRight _ _)

addb_20_eval :
  SOTerm (PolyCatTest.u_byte) -> (SOTerm (SUNat 20)) -> (SOTerm (SUNat 20))
addb_20_eval m n = addb_20 <! SMPair m n

l1_1_fold_add : SOTerm (SUNat 20)
l1_1_fold_add =
  sListEvalCata {n=1} {a=u_byte} {x=(SUNat 20)} (MkSUNat {m=20} 0) addb_20 l1_1

l3_3_fold_add : SOTerm (SUNat 20)
l3_3_fold_add =
  sListEvalCata {n=3} {a=u_byte} {x=(SUNat 20)} (MkSUNat {m=20} 0) addb_20 l3_3

l5_5_fold_add : SOTerm (SUNat 20)
l5_5_fold_add =
  sListEvalCata {n=5} {a=u_byte} {x=(SUNat 20)} (MkSUNat {m=20} 0) addb_20 l5_5

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
polyCatTest : IO ()
polyCatTest = do
  putStrLn ""
  putStrLn "=================="
  putStrLn "Begin polyCatTest:"
  putStrLn "------------------"
  putStrLn ""
  putStrLn "---------------------------------"
  putStrLn "---- Bounded natural numbers ----"
  putStrLn "---------------------------------"
  putStrLn ""
  putStrLn $ "bat1: " ++ show bat1
  putStrLn $ "but1: " ++ show but1
  putStrLn $ "bat2: " ++ show bat2
  putStrLn $ "bat2 (long): " ++ baShowLong bat2
  putStrLn $ "but2: " ++ show but2
  putStrLn ""
  putStrLn "------------------------------"
  putStrLn "---- Polynomial morphisms ----"
  putStrLn "------------------------------"
  putStrLn ""
  putStrLn $ "bnvlm0 = " ++ show bncvlm0
  putStrLn $ "bncpm0 = " ++ show bncpm0
  putStrLn $ "bncpm1 = " ++ show bncpm1
  putStrLn ""
  putStrLn "---------------"
  putStrLn "---- PolyF ----"
  putStrLn "---------------"
  putStrLn $ "polyf0 = " ++ show polyf0
  putStrLn $ "distrib[polyf0] = " ++ show (polyDistrib polyf0)
  putStrLn $ "position-list[polyf0] = " ++ polyPosShow polyf0
  putStrLn $ "poly-list[polyf0] = " ++ show (toPolyShape polyf0)
  putStrLn $ "poly-list[polyf1] = " ++ show (toPolyShape polyf1)
  putStrLn $ "pnitert10 = " ++ show pniterT10
  putStrLn $ "card[polyf0] = " ++ show (polyTCard polyf0)
  putStrLn $ "card[polybool] = " ++ show (polyTCard polybool)
  putStrLn $ "(polybool -> polyf0) = " ++ show polyHomBoolF0
  putStrLn $ "card[polybool -> polyf0] = " ++ show (polyTCard polyHomBoolF0)
  putStrLn $ "(id -> 4 * id) = " ++ show polyHomId4Id
  putStrLn $ "(id -> (2 * 2) * id) = " ++ show polyHomId4Id'
  putStrLn $ "(4 * id -> id) = " ++ show polyHom4IdId
  putStrLn $ "((2 * 2) * id -> id) = " ++ show polyHom4IdId'
  putStrLn $ "polyDepth3BT = " ++ show (toPolyShape polyDepth3BinTree)
  putStrLn $ "card[polyDepth3BT,0] = " ++ show (polyTCard polyDepth3BinTree)
  putStrLn $ "depth4Nat = " ++ show (polyNatIter 4)
  putStrLn $ "card[depth4Nat] = " ++ show (polyTCard (polyNatIter 4))
  putStrLn $ "card[depth4Nat -> polyDepth3BT] = " ++
    show (polyTCard $ PolyHomObj (polyNatIter 4) (polyDepth3BinTree))
  putStrLn $ "card[polyDepth3BT -> depth4Nat] = " ++
    show (polyTCard $ PolyHomObj (polyDepth3BinTree) (polyNatIter 4))
  putStrLn $ "hom[polyDepth3BT -> depth4Nat] = " ++
    showPolyShape (PolyHomObj (polyDepth3BinTree) (polyNatIter 4))
  putStrLn $ "polyDepth3BTFixed = " ++ show polyDepth3BinTreeFixed
  putStrLn $ "card[polyDepth3BTFixed,0] = "
    ++ show (polyTCard polyDepth3BinTreeFixed)
  putStrLn $ "depth4NatFixed = " ++ show (polyNatIterFixed 4)
  putStrLn $ "card[depth4NatFixed] = " ++ show (polyTCard (polyNatIterFixed 4))
  putStrLn $ "card[depth4NatFixed -> polyDepth3BTFixed] = " ++
    show (polyTCard $ PolyHomObj (polyNatIterFixed 4) (polyDepth3BinTreeFixed))
  putStrLn $ "card[polyDepth3BTFixed -> depth4NatFixed] = " ++
    show (polyTCard $ PolyHomObj (polyDepth3BinTreeFixed) (polyNatIterFixed 4))
  putStrLn $ "first compose = " ++ show ((4 $:* PolyI) $. (PolyI $+ Poly1))
  putStrLn $ "second compose = " ++
    show ((twoBits $* PolyI) $. (PolyI $+ Poly1))
  putStrLn $ "exercise 5.8.3 first part unformatted = " ++
    show (((PolyI $* PolyI) $. (PolyI $*^ 3 $+ Poly1)))
  putStrLn $ "exercise 5.8.3 first part distributed = " ++
    show (polyDistrib (((PolyI $* PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn $ "exercise 5.8.3 first part = " ++
    show (toPolyShape (((PolyI $* PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn $ "exercise 5.8.3 second part = " ++
    show (toPolyShape (((PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn $ "exercise 5.8.3 composite unformatted = " ++
    show (((PolyI $* PolyI $+ PolyI) $. (PolyI $*^ 3 $+ Poly1)))
  putStrLn $ "exercise 5.8.3 composite distributed = " ++
    show (polyDistrib (((PolyI $* PolyI $+ PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn $ "exercise 5.8.3 composite = " ++
    show (toPolyShape (((PolyI $* PolyI $+ PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn ""
  putStrLn "----------------"
  putStrLn "---- PolyOp ----"
  putStrLn "----------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "---- BoundedNat ----"
  putStrLn $ show testBN0
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "----------------"
  putStrLn "---- NTuple ----"
  putStrLn $ show testNT0
  putStrLn "----------------"
  putStrLn ""
  putStrLn "---- BoundedList ----"
  putStrLn $ show testBL0
  putStrLn $ show testBL1
  putStrLn $ show testBL2
  putStrLn $ show testBL3
  putStrLn $ show testBL4
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "---- Polynomial ----"
  putStrLn $ show testPoly6
  putStrLn $ show testPoly0
  putStrLn $ show testPoly7
  putStrLn $ show testPoly0p7
  putStrLn $ show $ map (flip scaleMonPolyShape testPolyS7) testPolyS0
  putStrLn $ show testPoly0m7
  putStrLn $ show testPoly9
  putStrLn $ show testPoly9exp4
  putStrLn $ show $ testPolyNatIter 0
  putStrLn $ show $ testPolyNatIter 1
  putStrLn $ show $ testPolyNatIter 2
  putStrLn $ show $ testPolyNatIter 3
  putStrLn $ show polyEx58q
  putStrLn $ show $ composePolyShape
    (addPolyShape (homNPolyShape 2) (homNPolyShape 1)) polyEx58q
  putStrLn $ show $ mulPolyShape polyEx293p polyEx293q
  putStrLn $ show $ parProdPolyShape polyEx293p polyEx293q
  putStrLn $ show $ parProdPolyShapeList [polyEx293p, idPolyShape, polyEx293q]
  putStrLn $ show $ polyShapeExponential idPolyShape idPolyShape
  putStrLn $ show $ polyShapeExponential idPolyShape (prodIdPolyShape 4)
  putStrLn $ show $ parProdClosureShape [(2, 1), (1,2)] [(3, 2), (0, 3)]
  putStrLn $ psPosShow testPolyS6
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "------------------------"
  putStrLn "Idris Nat implementation"
  putStrLn "------------------------"
  putStrLn $ show (power 2 0)
  putStrLn $ show (power 2 10)
  putStrLn $ show (power 2 20)
  putStrLn $ show (power 2 30)
  putStrLn $ show (power 2 40)
  putStrLn $ show (power 2 50)
  putStrLn $ show (power 2 60)
  putStrLn $ show (power 2 64)
  putStrLn $ show (power 2 65)
  putStrLn $ show (power 2 100)
  putStrLn $ show (power 2 1000)
  putStrLn $ show (power 2 10000)
  putStrLn $ show $ ptInterpNat powerByMultsTestTerm 2
  putStrLn "------------------------"
  putStrLn ""
  putStrLn "------"
  putStrLn "MuNatO"
  putStrLn "------"
  putStrLn $ show (natToMu 10)
  putStrLn $ show $ muToNat $ natHomObj (natToMu 3) (natToMu 4)
  putStrLn $ show testPre0
  putStrLn $ showPreMeta 1 testPre0
  putStrLn $ show testPre1
  putStrLn $ showPreMeta 2 testPre1
  putStrLn $ show testPre2
  putStrLn $ showPreMeta 2 testPre2
  putStrLn $ show testPre3
  putStrLn $ showPreMeta 4 testPre3
  putStrLn $ show testPre4
  putStrLn $ showPreMeta 4 testPre4
  putStrLn $ show testPre5
  putStrLn $ showPreMeta 4 testPre5
  putStrLn "------"
  putStrLn ""
  putStrLn "------------------------"
  putStrLn "RangedNat/RangedNatMorph"
  putStrLn "------------------------"
  putStrLn $ show $ testRNMPolyS0
  putStrLn $ show $ testRNMPolyS1
  putStrLn $ show $ testRNM0
  putStrLn $ show $ testRNM5
  putStrLn $ show $ testRNM13
  putStrLn $ show $ testRNM15
  putStrLn "------------------------"
  putStrLn ""
  putStrLn "-----------------------------------"
  putStrLn "Augmented RangedNat/RangedNatMorph"
  putStrLn "-----------------------------------"
  putStrLn $ show $ testARNM1
  putStrLn $ show $ testARNM2
  putStrLn $ show $ testARNM3
  putStrLn "-----------------------------------"
  putStrLn ""
  putStrLn "------------------------------------------"
  putStrLn "---- Metalanguage polynomial functors ----"
  putStrLn "------------------------------------------"
  putStrLn ""
  putStrLn "------------------------------------"
  putStrLn "---- Unrefined polynomial types ----"
  putStrLn "------------------------------------"
  putStrLn ""
  putStrLn $ "initial object: " ++ show initObj
  putStrLn $ "initial object as Nat: " ++ show (substObjToNat initObj)
  putStrLn $ "initial object in metalanguage: " ++ show (metaSOShowType initObj)
  putStrLn $ "terminal object: " ++ show termObj
  putStrLn $ "terminal object as Nat: " ++ show (substObjToNat termObj)
  putStrLn $ "terminal object in metalanguage: " ++
    show (metaSOShowType termObj)
  putStrLn $ "Bool: " ++ show SubstBool
  putStrLn $ "Bool as Nat: " ++ show (substObjToNat SubstBool)
  putStrLn $ "Bool in metalanguage: " ++ show (metaSOShowType SubstBool)
  putStrLn $ "unat7: " ++ show unat7
  putStrLn $ "unat7 as Nat: " ++ show (substObjToNat unat7)
  putStrLn $ "unat7 in metalanguage: " ++ show (metaSOShowType unat7)
  putStrLn $ "bnat4: " ++ show bnat4
  putStrLn $ "bnat4 as Nat: " ++ show (substObjToNat bnat4)
  putStrLn $ "bnat4 in metalanguage: " ++ show (metaSOShowType bnat4)
  putStrLn $ "bnat4_0: " ++ showSubstMorph bnat4_0
  putStrLn $ "bnat4_0 as Nat: " ++ show (substTermToNat bnat4_0)
  putStrLn $ "bnat4_0 as poly func: " ++ show (substMorphToBNC bnat4_0)
  putStrLn $ "bnat4_1: " ++ showSubstMorph bnat4_1
  putStrLn $ "bnat4_1 as Nat: " ++ show (substTermToNat bnat4_1)
  putStrLn $ "bnat4_1 as poly func: " ++ show (substMorphToBNC bnat4_1)
  putStrLn $ "bnat4_2: " ++ showSubstMorph bnat4_2
  putStrLn $ "bnat4_2 as Nat: " ++ show (substTermToNat bnat4_2)
  putStrLn $ "bnat4_2 as poly func: " ++ show (substMorphToBNC bnat4_2)
  putStrLn $ "bnat4_15: " ++ showSubstMorph bnat4_15
  putStrLn $ "bnat4_15 as Nat: " ++ show (substTermToNat bnat4_15)
  putStrLn $ "bnat4_15 as poly func: " ++ show (substMorphToBNC bnat4_15)
  putStrLn $ "id(boolToBool) as morph: " ++ showSubstMorph b2bid
  putStrLn $ "not(boolToBool) as morph: " ++ showSubstMorph b2bnot
  putStrLn $ "true(boolToBool) as morph: " ++ showSubstMorph b2btrue
  putStrLn $ "false(boolToBool) as morph: " ++ showSubstMorph b2bfalse
  putStrLn $ "id(boolToBool) as term: " ++
    showSubstMorph (MorphAsTerm b2bid)
  putStrLn $ "not(boolToBool) as term: " ++
    showSubstMorph (MorphAsTerm b2bnot)
  putStrLn $ "true(boolToBool) as term: " ++
    showSubstMorph (MorphAsTerm b2btrue)
  putStrLn $ "false(boolToBool) as term: " ++
    showSubstMorph (MorphAsTerm b2bfalse)
  putStrLn $ "term(id(boolToBool)) back to morph: " ++
    showSubstMorph (MorphToTermAndBack b2bid)
  putStrLn $ "term(not(boolToBool)) back to morph: " ++
    showSubstMorph (MorphToTermAndBack b2bnot)
  putStrLn $ "term(true(boolToBool)) back to morph: " ++
    showSubstMorph (MorphToTermAndBack b2btrue)
  putStrLn $ "term(false(boolToBool)) back to morph: " ++
    showSubstMorph (MorphToTermAndBack b2bfalse)
  putStrLn $ "id(boolToBool)'s Gödel number: " ++ show b2bid_gn
  putStrLn $ "backandforth(id(boolToBool))'s Gödel number: " ++
    show (substMorphToGNum (MorphToTermAndBack b2bid))
  putStrLn $ "not(boolToBool)'s Gödel number: " ++ show b2bnot_gn
  putStrLn $ "notnot(boolToBool)'s Gödel number: " ++ show b2bnotnot_gn
  putStrLn $ "true(boolToBool)'s Gödel number: " ++ show b2btrue_gn
  putStrLn $ "false(boolToBool)'s Gödel number: " ++ show b2bfalse_gn
  putStrLn $ "0 morphism in boolToBool: " ++
    showMaybeSubstMorph (substGNumToMorph SubstBool SubstBool 0)
  putStrLn $ "1 morphism in boolToBool: " ++
    showMaybeSubstMorph (substGNumToMorph SubstBool SubstBool 1)
  putStrLn $ "2 morphism in boolToBool: " ++
    showMaybeSubstMorph (substGNumToMorph SubstBool SubstBool 2)
  putStrLn $ "3 morphism in boolToBool: " ++
    showMaybeSubstMorph (substGNumToMorph SubstBool SubstBool 3)
  putStrLn $ "4 morphism in boolToBool: " ++
    showMaybeSubstMorph (substGNumToMorph SubstBool SubstBool 4)
  putStrLn $ "5 morphism in boolToBool: " ++
    showMaybeSubstMorph (substGNumToMorph SubstBool SubstBool 5)
  putStrLn $ "true as nat: " ++ show (substTermToNat STrue)
  putStrLn $ "false as nat: " ++ show (substTermToNat SFalse)
  putStrLn $ "not(true) as nat: " ++ show (substTermToNat (b2bnot <! STrue))
  putStrLn $ "not(false) as nat: " ++ show (substTermToNat (b2bnot <! SFalse))
  putStrLn $ "id(true) as nat: " ++ show (substTermToNat (b2bid <! STrue))
  putStrLn $ "id(false) as nat: " ++ show (substTermToNat (b2bid <! SFalse))
  putStrLn $ "notnot(true) as nat: " ++
    show (substTermToNat (b2bnotnot <! STrue))
  putStrLn $ "notnot(false) as nat: " ++
    show (substTermToNat (b2bnotnot <! SFalse))
  putStrLn $ "backandforth(not(true)) as nat: " ++
    show (substTermToNat (MorphToTermAndBack b2bnot <! STrue))
  putStrLn $ "backandforth(not(false)) as nat: " ++
    show (substTermToNat (MorphToTermAndBack b2bnot <! SFalse))
  putStrLn $ "backandforth(id(true)) as nat: " ++
    show (substTermToNat (MorphToTermAndBack b2bid <! STrue))
  putStrLn $ "backandforth(id(false)) as nat: " ++
    show (substTermToNat (MorphToTermAndBack b2bid <! SFalse))
  putStrLn $ "backandforth(true(true)) as nat: " ++
    show (substTermToNat (MorphToTermAndBack b2btrue <! STrue))
  putStrLn $ "backandforth(true(false)) as nat: " ++
    show (substTermToNat (MorphToTermAndBack b2btrue <! SFalse))
  putStrLn $ "backandforth(false(true)) as nat: " ++
    show (substTermToNat (MorphToTermAndBack b2bfalse <! STrue))
  putStrLn $ "backandforth(false(false)) as nat: " ++
    show (substTermToNat (MorphToTermAndBack b2bfalse <! SFalse))
  putStrLn $ "eval(notnot(true)) = " ++
    show (substTermToNat b2bnotnot_eval_t)
  putStrLn $ "eval(notnot(false)) = " ++
    show (substTermToNat b2bnotnot_eval_f)
  putStrLn $ "eval(id(true)) = " ++
    show (substTermToNat b2bid_eval_t)
  putStrLn $ "eval(id(false)) = " ++
    show (substTermToNat b2bid_eval_f)
  putStrLn $ "bool->bool as object: " ++ show (SubstHomObj SubstBool SubstBool)
  putStrLn $ "eval (f->f t->f) x false = " ++
    show (substTermToNat (soEval SubstBool SubstBool <!
      SMPair (SMPair (SMInjLeft _ _) (SMInjLeft _ _)) SFalse))
  putStrLn $ "eval (f->f t->f) x true = " ++
    show (substTermToNat (soEval SubstBool SubstBool <!
      SMPair (SMPair (SMInjLeft _ _) (SMInjLeft _ _)) STrue))
  putStrLn $ "eval (f->f t->t) x false = " ++
    show (substTermToNat (soEval SubstBool SubstBool <!
      SMPair (SMPair (SMInjLeft _ _) (SMInjRight _ _)) SFalse))
  putStrLn $ "eval (f->f t->t) x true = " ++
    show (substTermToNat (soEval SubstBool SubstBool <!
      SMPair (SMPair (SMInjLeft _ _) (SMInjRight _ _)) STrue))
  putStrLn $ "eval (f->t t->f) x false = " ++
    show (substTermToNat (soEval SubstBool SubstBool <!
      SMPair (SMPair (SMInjRight _ _) (SMInjLeft _ _)) SFalse))
  putStrLn $ "eval (f->t t->f) x true = " ++
    show (substTermToNat (soEval SubstBool SubstBool <!
      SMPair (SMPair (SMInjRight _ _) (SMInjLeft _ _)) STrue))
  putStrLn $ "eval (f->t t->t) x false = " ++
    show (substTermToNat (soEval SubstBool SubstBool <!
      SMPair (SMPair (SMInjRight _ _) (SMInjRight _ _)) SFalse))
  putStrLn $ "eval (f->t t->t) x true = " ++
    show (substTermToNat (soEval SubstBool SubstBool <!
      SMPair (SMPair (SMInjRight _ _) (SMInjRight _ _)) STrue))
  putStrLn $ "eval bool->bool: " ++ showSubstMorph (soEval SubstBool SubstBool)
  putStrLn $ "boolToBool as Nat: " ++ show (substObjToNat boolToBool)
  putStrLn $ "bnat4chi: " ++ show bnat4chi
  putStrLn $ "bnat4chi as Nat: " ++ show (substObjToNat bnat4chi)
  putStrLn $ "bnat4chi in metalanguage: " ++ show (metaSOShowType bnat4chi)
  putStrLn $ "lowest-numbered morphism in bnat4chi: " ++
    showMaybeSubstMorph bnat4chi_gn_0
  putStrLn $ "highest-numbered morphism in bnat4chi: " ++
    showMaybeSubstMorph bnat4chi_gn_65535
  putStrLn $ "beyond-highest-numbered morphism in bnat4chi: " ++
    showMaybeSubstMorph bnat4chi_gn_65536
  putStrLn $ "bit 2 of bnat4_15: " ++
    show (substTermToNat $ bnat4_bit_2 <! bnat4_15)
  putStrLn $ "bit 2 of bnat4_15 as poly func: " ++
    show (substMorphToBNC $ bnat4_bit_2 <! bnat4_15)
  putStrLn $ "bit 2 of bnat4_2: " ++
    show (substTermToNat $ bnat4_bit_2 <! bnat4_2)
  putStrLn $ "bit 2 of bnat_2 as poly func: " ++
    show (substMorphToBNC $ bnat4_bit_2 <! bnat4_2)
  putStrLn $ "bnat4_bit_2 as morphism: " ++ showSubstMorph bnat4_bit_2
  putStrLn $ "bnat4_bit_2's Gödel number: " ++ show bnat4_bit_2_gn
  putStrLn $ "bit 2 of bnat4_15 via term: " ++
    show (substTermToNat $ MorphToTermAndBack bnat4_bit_2 <! bnat4_15)
  putStrLn $ "bit 2 of bnat4_2 via term: " ++
    show (substTermToNat $ MorphToTermAndBack bnat4_bit_2 <! bnat4_2)
  putStrLn ""
  putStrLn "----------------"
  putStrLn "End polyCatTest."
  putStrLn "================"
  pure ()
