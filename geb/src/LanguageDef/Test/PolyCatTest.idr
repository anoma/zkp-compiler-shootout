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

-------------------
---- RangedNat ----
-------------------

--------------------------
---- Circuit category ----
--------------------------

testCircuitObj0 : CircuitObj
testCircuitObj0 = (0, 3)

testCircuitPS0 : PolyShape
testCircuitPS0 = [(1, 1), (0, 1)]

testCircuitObj1 : CircuitObj
testCircuitObj1 = (1, 4)

testCircuitMorph0 :
  CircuitMorphism PolyCatTest.testCircuitObj0 PolyCatTest.testCircuitObj1
testCircuitMorph0 = MkCircuitPolyMorphism testCircuitPS0

export
polyCatTest : IO ()
polyCatTest = do
  putStrLn ""
  putStrLn "=================="
  putStrLn "Begin polyCatTest:"
  putStrLn ""
  putStrLn "---- BoundedNat ----"
  putStrLn $ show testBN0
  putStrLn "--------------------"
  putStrLn ""
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
  putStrLn ""
  putStrLn "------"
  putStrLn "MuNatO"
  putStrLn "------"
  putStrLn $ show (natToMu 10)
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
  putStrLn ""
  putStrLn "---------"
  putStrLn "RangedNat"
  putStrLn "---------"
  putStrLn ""
  putStrLn "-----------------"
  putStrLn "Circuit category"
  putStrLn "-----------------"
  putStrLn $ show $ psInterpNat testCircuitPS0 0
  putStrLn $ show $ psInterpNat testCircuitPS0 3
  putStrLn $ "testCircuitMorph0 = " ++ cmShow testCircuitMorph0
  putStrLn ""
  putStrLn "End polyCatTest."
  putStrLn "=================="
  pure ()