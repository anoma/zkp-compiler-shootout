module Test.TestLibrary

import public Library.IdrisUtils
import public Library.IdrisCategories

%default total

public export
Assertion : Type
Assertion = ()

public export
Assert : (b : Bool) -> if b then () else List ()
Assert True = ()
Assert False = []

export
testLibraryTest : IO ()
testLibraryTest = do
  -- putStrLn "Begin testLibraryTest:"
  -- putStrLn "End testLibraryTest."
  pure ()
