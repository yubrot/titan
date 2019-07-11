module TestHelper where

import Test.Hspec
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import Titan
import Titan.Prelude

renderCode :: PrettyCode a => a -> Text
renderCode = Text.unwords . map Text.strip . Text.lines . renderStrict . layoutSmart (LayoutOptions Unbounded) . prettyInline 0

shouldBeRight :: (Eq a, Show a, HasCallStack) => Either Error a -> a -> Expectation
shouldBeRight ea b = case ea of
  Right a -> a `shouldBe` b
  Left e -> expectationFailure $ Text.unpack $ renderStrict $ layoutSmart (LayoutOptions Unbounded) $ pretty e
