import Test.Hspec
import Titan
import Titan.Prelude
import Titan.Std
import qualified TTTest
import qualified PrettyPrinterTest
import qualified ParserTest
import qualified BinderTest
import qualified ResolverTest
import qualified KindInferenceTest
import qualified TypeInferenceTest
import qualified PatternCheckerTest

main :: IO ()
main = hspec $ do
  TTTest.spec
  PrettyPrinterTest.spec
  ParserTest.spec
  BinderTest.spec
  ResolverTest.spec
  KindInferenceTest.spec
  TypeInferenceTest.spec
  PatternCheckerTest.spec
  describe "std" $ do
    stdFiles <- runIO stdFiles
    testStd emptyGlobal stdFiles

testStd :: Global -> [(String, String)] -> Spec
testStd _ [] = return ()
testStd global ((path, code):rest) = do
  let parse' = parse @Program path
      bind' = bind global
      test f code = case (parse' >=> bind' >=> f) code of
        Left e -> expectationFailure $ show e
        Right r -> (parse' >=> bind' >=> f) (pprint (program r)) `shouldBe` Right r

  describe path $ do
    it "parse" $ parse' code `shouldSatisfy` isRight
    it "pprint" $ (parse' code >>= parse' . pprint) `shouldBe` parse' code
    it "bind" $ test pure code
    it "resolve" $ test resolve code
    it "ki" $ test (resolve >=> ki) code
    it "ti" $ test (resolve >=> ki >=> ti) code

  case parse' code >>= bind' of
    Right global -> testStd global rest
    _ -> return ()
