module BinderTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude
import TestHelper

test :: Text -> Either Error Text
test code = fmap (renderCode . program) (parse "test" code >>= bind emptyGlobal)

(==>) :: HasCallStack => Text -> Text -> Expectation
code ==> result = test code `shouldBeRight` result

(==>!) :: HasCallStack => Text -> Text -> Expectation
code ==>! a = test code `shouldSatisfy` \case
  Left (MultipleDeclarationsOf a') -> a == a'
  _ -> False

spec :: Spec
spec = describe "Titan.Binder" $ do
  it "Program" $ do
    ""
      ==> ""
    "val hello = 123"
      ==> "val hello = 123"
    "val hello = 123 val hello = 123"
      ==>! "hello"
    "val hello = 123 val world = 123"
      ==> "val hello = 123 val world = 123"
    "data Vec { con Vec Int Int }"
      ==> "data Vec { con Vec Int Int }"
    "data Vec2 { con Vec Int Int } data Vec3 { con Vec Int Int Int }"
      ==>! "Vec"
    "data Vec { con Vec Int Int con Vec Int Int Int }"
      ==>! "Vec"
    "data Vec { con Vec2 Int Int } data Vec { con Vec3 Int Int Int }"
      ==>! "Vec"
    "class Hello a { val hello : a }"
      ==> "class Hello a { val hello : a }"
    "class Hello a { val hello : a } class Hello a { val greet : a }"
      ==>! "Hello"
    "class Hello a { val hello : a } class Greet a { val hello : a }"
      ==>! "hello"
    "class Hello a { val hello : a } val hello = 123"
      ==>! "hello"
    "default"
      ==> "default"
    "default { Just }"
      ==> "default { Just }"
    test "default default"
      `shouldSatisfy` \case Left MultipleDefault -> True; _ -> False
  it "local binds" $ do
    "val hello : [a a] a"
      ==>! "a"
    "data Pair a a"
      ==>! "a"
    "class C a a"
      ==>! "a"
    "class C { val hello : [a a] a }"
      ==>! "a"
    "class C a { val hello : [a] a }"
      ==>! "a"
    "val hello = let x = 0, x = 0 in x"
      ==>! "x"
    "val f = fun x x -> x"
      ==>! "x"
    "class C { val hello : a = fun x x -> x }"
      ==>! "x"
    "val f = fun x -> fun y y -> x"
      ==>! "y"
    "val f = let g = fun x x -> x in g"
      ==>! "x"
    "val f = let g = g in fun x x -> x"
      ==>! "x"
    "val f = let g : [a a] a in g"
      ==>! "a"
