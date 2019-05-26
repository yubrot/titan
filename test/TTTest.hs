module TTTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude

spec :: Spec
spec = describe "Titan.TT" $ do
  it "Typing" $ do
    (succ <$> pure 0)
      `shouldBe` (pure 1 :: Typing Integer)
    (succ <$> Untyped)
      `shouldBe` (Untyped :: Typing Integer)
    ((+) <$> Typed Explicit 3 <*> Typed Explicit 5)
      `shouldBe` (Typed Explicit 8)
    ((+) <$> Typed Inferred 2 <*> Typed Explicit 4)
      `shouldBe` (Typed Inferred 6)
    ((+) <$> Typed Explicit 1 <*> Typed Inferred 5)
      `shouldBe` (Typed Inferred 6)
    ((+) <$> Typed Inferred 1 <*> Typed Inferred 5)
      `shouldBe` (Typed Inferred 6)
    ((+) <$> Typed Explicit 1 <*> Untyped)
      `shouldBe` Untyped
    (pure 0 <|> pure 1)
      `shouldBe` (pure 0 :: Typing Integer)
    (empty <|> pure 1)
      `shouldBe` (pure 1 :: Typing Integer)
    (empty <|> empty)
      `shouldBe` (Untyped :: Typing Integer)
