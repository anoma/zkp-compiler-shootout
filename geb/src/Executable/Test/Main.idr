module Executable.Test.Main

import Test.TestLibrary
import Library.Test.IdrisUtilsTest
import Library.Test.IdrisCategoriesTest
import LanguageDef.Test.PatternCatTest
import LanguageDef.Test.PolyCatTest
import LanguageDef.Test.AtomTest
import LanguageDef.Test.RefinedADTTest
import LanguageDef.Test.UniversalCategoryTest
import LanguageDef.Test.InterpretationTest
import LanguageDef.Test.SyntaxTest
import LanguageDef.Test.ExpressionTest
import LanguageDef.Test.MetaprogrammingTest
import LanguageDef.Test.LogicTest
import LanguageDef.Test.ComputationalEffectsTest
import LanguageDef.Test.EmbeddedTest
import Library.Test.CategoryTheoryTest

%default total

export
main : IO ()
main = do
  Test.TestLibrary.testLibraryTest
  Library.Test.IdrisUtilsTest.idrisUtilsTest
  Library.Test.IdrisCategoriesTest.libraryIdrisCategoriesTest
  LanguageDef.Test.AtomTest.languageDefAtomTest
  LanguageDef.Test.RefinedADTTest.languageDefRefinedADTTest
  LanguageDef.Test.UniversalCategoryTest.languageDefUniversalCategoryTest
  LanguageDef.Test.InterpretationTest.languageDefInterpretationTest
  LanguageDef.Test.SyntaxTest.languageDefSyntaxTest
  LanguageDef.Test.ExpressionTest.languageDefExpressionTest
  LanguageDef.Test.MetaprogrammingTest.languageDefMetaprogrammingTest
  LanguageDef.Test.LogicTest.languageDefLogicTest
  LanguageDef.Test.ComputationalEffectsTest.languageDefComputationalEffectsTest
  LanguageDef.Test.EmbeddedTest.languageDefEmbeddedTest
  Library.Test.CategoryTheoryTest.libraryCategoryTheoryTest
  LanguageDef.Test.PolyCatTest.polyCatTest
  LanguageDef.Test.PatternCatTest.patternCatTest
