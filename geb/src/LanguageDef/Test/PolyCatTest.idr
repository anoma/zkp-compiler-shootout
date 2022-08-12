module LanguageDef.Test.PolyCatTest

import Test.TestLibrary
import LanguageDef.PolyCat

%default total

{- XXX

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

------------------
---- SubstObj ----
------------------

testSO0 : MuISubstO
testSO0 = ISOCoproduct ISOTerminal ISOTerminal

testSO1 : MuISubstO
testSO1 = ISOProduct testSO0 testSO0

testSO2 : MuISubstO
testSO2 = ISOCoproduct testSO0 ISOTerminal

testSO3 : MuISubstO
testSO3 = isubstOHomObj testSO1 testSO2

testSO4 : MuISubstO
testSO4 = isubstOHomObj testSO2 testSO1

testSO5 : MuISubstO
testSO5 = isubstOHomObj testSO0 testSO2

testSO6 : MuISubstO
testSO6 = isubstOHomObj testSO0 testSO0

testSO7 : MuISubstO
testSO7 = ISOProduct testSO0 ISOTerminal

testSO8 : MuISubstO
testSO8 = isubstOHomObj testSO0 testSO7

testSO9 : MuISubstO
testSO9 = isubstOHomObj testSO2 testSO2
  XXX -}
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
bncpmt12 = Assert $ metaBNCPolyM 200 (bncpm1 #- bncpm0) 3 == 126

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
  metaBNCPolyM 100 (IfZero (bncpm0 #/ bncpm1) bncpm0 bncpm1) 3 == 38

bncpmt20 : Assertion
bncpmt20 = Assert $
  metaBNCPolyM 100 (IfZero (bncpm1 #/ bncpm0) bncpm0 bncpm1) 3 == 64

bncpmt21 : Assertion
bncpmt21 = Assert $ metaBNCPolyM 200 (bncpm1 #. (bncpm0 #/ bncpm1)) 3 == 27

----------------
----------------
---- PolyOp ----
----------------
----------------

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
  {- XXX
  putStrLn ""
  putStrLn "----------------"
  putStrLn "---- PolyOp ----"
  putStrLn "----------------"
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
  putStrLn $ psIdxShow testPolyS6
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
  putStrLn "--------"
  putStrLn "SubstObj"
  putStrLn "--------"
  putStrLn $ show $ isubstODepth testSO0
  putStrLn $ show $ isubstOCard testSO0
  putStrLn $ show $ isubstODepth testSO1
  putStrLn $ show $ isubstOCard testSO1
  putStrLn $ show $ isubstODepth testSO2
  putStrLn $ show $ isubstOCard testSO2
  putStrLn $ show $ isubstODepth testSO3
  putStrLn $ show $ isubstOCard testSO3
  putStrLn $ show $ isubstODepth testSO4
  putStrLn $ show $ isubstOCard testSO4
  putStrLn $ show $ isubstODepth testSO5
  putStrLn $ show $ isubstOCard testSO5
  putStrLn $ show testSO5
  putStrLn $ show $ isubstOCard testSO6
  putStrLn $ show testSO6
  putStrLn $ show $ isubstOCard testSO8
  putStrLn $ show testSO8
  putStrLn $ show $ isubstOCard testSO9
  putStrLn $ show testSO9
  putStrLn "--------"
  XXX -}
  putStrLn ""
  putStrLn "----------------"
  putStrLn "End polyCatTest."
  putStrLn "================"
  pure ()
