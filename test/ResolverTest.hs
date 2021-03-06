module ResolverTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude
import TestHelper

test :: Text -> Either Error Text
test code = fmap (renderCode . program) (parse "test" code >>= bind emptyGlobal >>= resolve)

(==>) :: HasCallStack => Text -> Text -> Expectation
code ==> result = forM_ [code, result] $ \code -> test code `shouldBeRight` result

(==>!) :: HasCallStack => Text -> Text -> Expectation
code ==>! a = test code `shouldSatisfy` \case
  Left (CannotResolve a') -> a == a'
  _ -> False

spec :: Spec
spec = describe "Titan.Resolver" $ do
  it "global definitions" $ do
    ""
      ==> ""
    "val a = a"
      ==> "val a = a"
    "val a = b"
      ==>! "b"
    "val a = b val b = a"
      ==> "val a = b val b = a"
    "val a : A"
      ==>! "A"
    "val a : A data A"
      ==> "val a : [] A data A"
    "val a = A data A"
      ==>! "A"
    "val a : A = B data A { con B }"
      ==> "val a : [] A = B data A { con B }"
    "val a : B data A { con B }"
      ==>! "B"
    "val a : A = A data A { con A }"
      ==> "val a : [] A = A data A { con A }"
    -- NOTE: Is this resolver error?
    -- Currently Titan cannot treat constraints as first-class type.
    -- See also: ConstraintKinds
    "val a : C class C"
      ==>! "C"
    "val a : T where C T data T class C"
      ==> "val a : [] T where C T data T class C"
    "val a = c data T class C { val c : T }"
      ==> "val a = c data T class C { val c : [] T }"
    "val a = c data T class C { val c : T = a }"
      ==> "val a = c data T class C { val c : [] T = a }"
    "instance T"
      ==>! "T"
    "class T instance T"
      ==> "class T instance [] T"
  it "local parameters" $ do
    "val hello : a -> b"
      ==> "val hello : [a b] a -> b"
    "val hello : a -> a"
      ==> "val hello : [a] a -> a"
    "val hello : [a] a -> b"
      ==>! "b"
    "val hello : m a"
      ==> "val hello : [m a] m a"
    "val hello : b -> a"
      ==> "val hello : [b a] b -> a"
    "data List a"
      ==> "data List a"
    "data Pair a b"
      ==> "data Pair a b"
    "data Pair a { con Pair a b }"
      ==>! "b"
    "data Phantom a { con Phantom }"
      ==> "data Phantom a { con Phantom }"
    "data Pair a b { con Pair a b }"
      ==> "data Pair a b { con Pair a b }"
    "class C a"
      ==> "class C a"
    "class C a b"
      ==> "class C a b"
    "class C a class D a where C a"
      ==> "class C a class D a where C a"
    "class C a class D a where C b"
      ==>! "b"
    "class D a where C a"
      ==>! "C"
    "class C a { val c : a }"
      ==> "class C a { val c : [] a }"
    "class C a { val c : a -> b }"
      ==> "class C a { val c : [b] a -> b }"
    "class C a { val c : [] a -> b }"
      ==>! "b"
    "val hello : a where C b class C"
      ==> "val hello : [a b] a where C b class C"
    "val hello : [a] a where C b class C"
      ==>! "b"
    "class C instance C a"
      ==> "class C instance [a] C a"
    "class C instance C a where C b"
      ==> "class C instance [a b] C a where C b"
    "data A (a : *)"
      ==> "data A (a : *)"
    "data A (a : ?)"
      ==> "data A (a : ?)"
    "data A (a : * -> *)"
      ==> "data A (a : * -> *)"
    "class C instance C a"
      ==> "class C instance [a] C a"
    "class C instance [a] C a where C b"
      ==>! "b"
    "class C instance [a b] C a b"
      ==> "class C instance [a b] C a b"
  it "expressions" $ do
    "val hello = hello"
      ==> "val hello = hello"
    "val hello = goodbye"
      ==>! "goodbye"
    "val hello = Hello 123 data A { con Hello }"
      ==> "val hello = Hello 123 data A { con Hello }"
    "val hello = hello hello hello"
      ==> "val hello = hello hello hello"
    "val hello = 123"
      ==> "val hello = 123"
    "val hello = let goodbye = 123 in goodbye hello"
      ==> "val hello = let goodbye = 123 in goodbye hello"
    "val hello = let x = x in x"
      ==> "val hello = let x = x in x"
    "val hello = let x = y, y = x in y"
      ==> "val hello = let x = y, y = x in y"
    "val hello = let x = let y = 0 in 0 in y"
      ==>! "y"
    "val goodbye = hello val hello = goodbye"
      ==> "val goodbye = hello val hello = goodbye"
    "val f : a -> b = let g : b -> c = 0 in 1"
      ==> "val f : [a b] a -> b = let g : [b c] b -> c = 0 in 1"
    "val f : a -> b = let g : [c] b -> c = 0 in 1"
      ==>! "b"
    "val f : [a b] a -> b = let g : b -> c = 0 in 1"
      ==> "val f : [a b] a -> b = let g : [c] b -> c = 0 in 1"
    "val f : [a b] a -> b = let g : [b c] b -> c = 0 in 1"
      ==> "val f : [a b] a -> b = let g : [b c] b -> c = 0 in 1"
    "class F a { val f : a = let g : [] a in g }"
      ==> "class F a { val f : [] a = let g : [] a in g }"
    "val f = fun x -> 0"
      ==> "val f = fun x -> 0"
    "val f = fun x -> x"
      ==> "val f = fun x -> x"
    "val f = fun x y -> x y"
      ==> "val f = fun x y -> x y"
    "val f = fun _ -> 0"
      ==> "val f = fun _ -> 0"
    "val f = fun 0 -> 0"
      ==> "val f = fun 0 -> 0"
    "val f = fun x@123 -> x"
      ==> "val f = fun x@123 -> x"
    "val f = fun P -> 0 data P { con Q }"
      ==>! "P"
    "val f = fun Q -> 0 data P { con Q }"
      ==> "val f = fun Q -> 0 data P { con Q }"
    "val f = fun x _ -> x | _ y -> y"
      ==> "val f = fun x _ -> x | _ y -> y"
    "val f = fun x _ -> y | _ y -> x"
      ==>! "y"
    "val f = fun x _ -> x | _ y -> x"
      ==>! "x"
    "val f = fun x _ -> x | _ x -> x"
      ==> "val f = fun x _ -> x | _ x -> x"
