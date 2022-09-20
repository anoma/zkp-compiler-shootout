module LanguageDef.Test.PatternCatTest

import Test.TestLibrary
import LanguageDef.PatternCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
patternCatTest : IO ()
patternCatTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin patternCatTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End patternCatTest."
  putStrLn "==================="
  pure ()
