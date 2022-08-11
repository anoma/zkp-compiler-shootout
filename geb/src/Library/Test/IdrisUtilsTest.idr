module Library.Test.IdrisUtilsTest

import Test.TestLibrary
import Library.IdrisUtils

%default total

minmodt0 : Assertion
minmodt0 = Assert $ minusModulo 3 18 12 == 0

minmodt1 : Assertion
minmodt1 = Assert $ minusModulo 3 25 12 == 1

minmodt2 : Assertion
minmodt2 = Assert $ minusModulo 3 64 53 == 2

minmodt3 : Assertion
minmodt3 = Assert $ minusModulo 3 12 18 == 0

minmodt4 : Assertion
minmodt4 = Assert $ minusModulo 3 12 25 == 2

minmodt5 : Assertion
minmodt5 = Assert $ minusModulo 3 53 64 == 1

minmodt6 : Assertion
minmodt6 = Assert $ minusModulo 13 72 18 == 2

minmodt7 : Assertion
minmodt7 = Assert $ minusModulo 9 55 77 == 5

export
idrisUtilsTest : IO ()
idrisUtilsTest = do
  -- putStrLn "Begin idrisUtilsTest:"
  -- putStrLn "End idrisUtilsTest."
  pure ()
