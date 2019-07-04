module BinderTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude

test :: Text -> Either Error Text
test code = fmap (pretty . program) (parse "test" code >>= bind emptyGlobal)

spec :: Spec
spec = describe "Titan.Binder" $ do
  it "Program" $ do
    test ""
      `shouldBe` Right ""
    test "val hello = 123"
      `shouldBe` Right "val hello = 123"
    test "val hello = 123 val hello = 123"
      `shouldBe` Left (MultipleDeclarationsOf "hello")
    test "val hello = 123 val world = 123"
      `shouldBe` Right "val hello = 123 val world = 123"
    test "data Vec { con Vec Int Int }"
      `shouldBe` Right "data Vec { con Vec Int Int }"
    test "data Vec2 { con Vec Int Int } data Vec3 { con Vec Int Int Int }"
      `shouldBe` Left (MultipleDeclarationsOf "Vec")
    test "data Vec { con Vec Int Int con Vec Int Int Int }"
      `shouldBe` Left (MultipleDeclarationsOf "Vec")
    test "data Vec { con Vec2 Int Int } data Vec { con Vec3 Int Int Int }"
      `shouldBe` Left (MultipleDeclarationsOf "Vec")
    test "class Hello a { val hello : a }"
      `shouldBe` Right "class Hello a { val hello : a }"
    test "class Hello a { val hello : a } class Hello a { val greet : a }"
      `shouldBe` Left (MultipleDeclarationsOf "Hello")
    test "class Hello a { val hello : a } class Greet a { val hello : a }"
      `shouldBe` Left (MultipleDeclarationsOf "hello")
    test "class Hello a { val hello : a } val hello = 123"
      `shouldBe` Left (MultipleDeclarationsOf "hello")
    test "default"
      `shouldBe` Right "default"
    test "default { Just }"
      `shouldBe` Right "default { Just }"
    test "default default"
      `shouldBe` Left MultipleDefault
  it "local binds" $ do
    test "val hello : [a a] a"
      `shouldBe` Left (MultipleDeclarationsOf "a")
    test "data Pair a a"
      `shouldBe` Left (MultipleDeclarationsOf "a")
    test "class C a a"
      `shouldBe` Left (MultipleDeclarationsOf "a")
    test "class C { val hello : [a a] a }"
      `shouldBe` Left (MultipleDeclarationsOf "a")
    test "class C a { val hello : [a] a }"
      `shouldBe` Left (MultipleDeclarationsOf "a")
    test "val hello = let x = 0, x = 0 in x"
      `shouldBe` Left (MultipleDeclarationsOf "x")
    test "val f = fun x x -> x"
      `shouldBe` Left (MultipleDeclarationsOf "x")
    test "class C { val hello : a = fun x x -> x }"
      `shouldBe` Left (MultipleDeclarationsOf "x")
    test "val f = fun x -> fun y y -> x"
      `shouldBe` Left (MultipleDeclarationsOf "y")
    test "val f = let g = fun x x -> x in g"
      `shouldBe` Left (MultipleDeclarationsOf "x")
    test "val f = let g = g in fun x x -> x"
      `shouldBe` Left (MultipleDeclarationsOf "x")
    test "val f = let g : [a a] a in g"
      `shouldBe` Left (MultipleDeclarationsOf "a")
