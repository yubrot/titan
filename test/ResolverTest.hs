module ResolverTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude

test :: String -> Either Error String
test code = fmap (pprint . program) (parse "test" code >>= bind emptyGlobal >>= resolve)

(==>) :: HasCallStack => String -> Either Error String -> Expectation
code ==> result = case result of
  Left e ->
    test code `shouldBe` Left e
  Right r -> do
    test code `shouldBe` Right r
    test r `shouldBe` Right r

spec :: Spec
spec = describe "Titan.Resolver" $ do
  it "global definitions" $ do
    ""
      ==> Right ""
    "val a = a"
      ==> Right "val a = a"
    "val a = b"
      ==> Left (CannotResolve "b")
    "val a = b val b = a"
      ==> Right "val a = b val b = a"
    "val a : A"
      ==> Left (CannotResolve "A")
    "val a : A data A"
      ==> Right "val a : [] A data A"
    "val a = A data A"
      ==> Left (CannotResolve "A")
    "val a : A = B data A { con B }"
      ==> Right "val a : [] A = B data A { con B }"
    "val a : B data A { con B }"
      ==> Left (CannotResolve "B")
    "val a : A = A data A { con A }"
      ==> Right "val a : [] A = A data A { con A }"
    -- NOTE: Is this resolver error?
    -- Currently Titan cannot treat constraints as first-class type.
    -- See also: ConstraintKinds
    "val a : C class C"
      ==> Left (CannotResolve "C")
    "val a : T where C T data T class C"
      ==> Right "val a : [] T where C T data T class C"
    "val a = c data T class C { val c : T }"
      ==> Right "val a = c data T class C { val c : [] T }"
    "val a = c data T class C { val c : T = a }"
      ==> Right "val a = c data T class C { val c : [] T = a }"
    "instance T"
      ==> Left (CannotResolve "T")
    "class T instance T"
      ==> Right "class T instance [] T"
  it "local parameters" $ do
    "val hello : a -> b"
      ==> Right "val hello : [a b] a -> b"
    "val hello : a -> a"
      ==> Right "val hello : [a] a -> a"
    "val hello : [a] a -> b"
      ==> Left (CannotResolve "b")
    "val hello : m a"
      ==> Right "val hello : [m a] m a"
    "val hello : b -> a"
      ==> Right "val hello : [b a] b -> a"
    "data List a"
      ==> Right "data List a"
    "data Pair a b"
      ==> Right "data Pair a b"
    "data Pair a { con Pair a b }"
      ==> Left (CannotResolve "b")
    "data Phantom a { con Phantom }"
      ==> Right "data Phantom a { con Phantom }"
    "data Pair a b { con Pair a b }"
      ==> Right "data Pair a b { con Pair a b }"
    "class C a"
      ==> Right "class C a"
    "class C a b"
      ==> Right "class C a b"
    "class C a class D a where C a"
      ==> Right "class C a class D a where C a"
    "class C a class D a where C b"
      ==> Left (CannotResolve "b")
    "class D a where C a"
      ==> Left (CannotResolve "C")
    "class C a { val c : a }"
      ==> Right "class C a { val c : [] a }"
    "class C a { val c : a -> b }"
      ==> Right "class C a { val c : [b] a -> b }"
    "class C a { val c : [] a -> b }"
      ==> Left (CannotResolve "b")
    "val hello : a where C b class C"
      ==> Right "val hello : [a b] a where C b class C"
    "val hello : [a] a where C b class C"
      ==> Left (CannotResolve "b")
    "class C instance C a"
      ==> Right "class C instance [a] C a"
    "class C instance C a where C b"
      ==> Right "class C instance [a b] C a where C b"
    "data A (a : Type)"
      ==> Right "data A (a : Type)"
    "data A (a : Constraint)"
      ==> Right "data A (a : Constraint)"
    "data A (a : Type -> Type)"
      ==> Right "data A (a : Type -> Type)"
    "class C instance C a"
      ==> Right "class C instance [a] C a"
    "class C instance [a] C a where C b"
      ==> Left (CannotResolve "b")
    "class C instance [a b] C a b"
      ==> Right "class C instance [a b] C a b"
  it "expressions" $ do
    "val hello = hello"
      ==> Right "val hello = hello"
    "val hello = goodbye"
      ==> Left (CannotResolve "goodbye")
    "val hello = Hello 123 data A { con Hello }"
      ==> Right "val hello = Hello 123 data A { con Hello }"
    "val hello = hello hello hello"
      ==> Right "val hello = hello hello hello"
    "val hello = 123"
      ==> Right "val hello = 123"
    "val hello = let goodbye = 123 in goodbye hello"
      ==> Right "val hello = let goodbye = 123 in goodbye hello"
    "val hello = let x = x in x"
      ==> Right "val hello = let x = x in x"
    "val hello = let x = y, y = x in y"
      ==> Right "val hello = let x = y, y = x in y"
    "val hello = let x = let y = 0 in 0 in y"
      ==> Left (CannotResolve "y")
    "val goodbye = hello val hello = goodbye"
      ==> Right "val goodbye = hello val hello = goodbye"
    "val f : a -> b = let g : b -> c = 0 in 1"
      ==> Right "val f : [a b] a -> b = let g : [b c] b -> c = 0 in 1"
    "val f : a -> b = let g : [c] b -> c = 0 in 1"
      ==> Left (CannotResolve "b")
    "val f : [a b] a -> b = let g : b -> c = 0 in 1"
      ==> Right "val f : [a b] a -> b = let g : [c] b -> c = 0 in 1"
    "val f : [a b] a -> b = let g : [b c] b -> c = 0 in 1"
      ==> Right "val f : [a b] a -> b = let g : [b c] b -> c = 0 in 1"
    "class F a { val f : a = let g : [] a in g }"
      ==> Right "class F a { val f : [] a = let g : [] a in g }"
    "val f = fun x -> 0"
      ==> Right "val f = fun x -> 0"
    "val f = fun x -> x"
      ==> Right "val f = fun x -> x"
    "val f = fun x y -> x y"
      ==> Right "val f = fun x y -> x y"
    "val f = fun _ -> 0"
      ==> Right "val f = fun _ -> 0"
    "val f = fun 0 -> 0"
      ==> Right "val f = fun 0 -> 0"
    "val f = fun x@123 -> x"
      ==> Right "val f = fun x@123 -> x"
    "val f = fun P -> 0 data P { con Q }"
      ==> Left (CannotResolve "P")
    "val f = fun Q -> 0 data P { con Q }"
      ==> Right "val f = fun Q -> 0 data P { con Q }"
    "val f = fun x _ -> x | _ y -> y"
      ==> Right "val f = fun x _ -> x | _ y -> y"
    "val f = fun x _ -> y | _ y -> x"
      ==> Left (CannotResolve "y")
    "val f = fun x _ -> x | _ y -> x"
      ==> Left (CannotResolve "x")
    "val f = fun x _ -> x | _ x -> x"
      ==> Right "val f = fun x _ -> x | _ x -> x"
