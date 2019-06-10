module TypeInferenceTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude

test :: String -> Either Error String
test code = fmap (pprint . program) (parse "test" code >>= bind emptyGlobal >>= resolve >>= ki >>= ti)

(==>) :: HasCallStack => String -> String -> Expectation
code ==> result = forM_ [code, result] $ \code -> test code `shouldBe` Right result

(==>!) :: HasCallStack => String -> (Error -> Bool) -> Expectation
code ==>! f = test code `shouldSatisfy` \case Left e -> f e; _ -> False

spec :: Spec
spec = describe "Titan.TypeInference" $ do
  it "verify classes" $ do
    ""
      ==> ""
    "class A"
      ==> "class A"
    "class A"
      ==> "class A"
    "class A class B"
      ==> "class A class B"
    "class A class B where A"
      ==> "class A class B where A"
    "class A where B class B where A"
      ==>! \case CyclicClasses _ -> True; _ -> False
    "class A where B class B"
      ==> "class A where B class B"
    "class A class B where A class C where (A, B) class D where (B, C)"
      ==> "class A class B where A class C where (A, B) class D where (B, C)"
  it "verify instances" $ do
    "class A instance A"
      ==> "class A instance [] A"
    "class A instance A instance A"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "data S data T class A a instance A S instance A T"
      ==> "data S data T class A (a : Type) instance [] A S instance [] A T"
    "data S a data T a class A a instance A (S a) instance A (T a)"
      ==> "data S (a : Type) data T (a : Type) class A (a : Type) instance [(a : Type)] A (S a) instance [(a : Type)] A (T a)"
    "data S a class A a instance A (S a) instance A (S a)"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "data S a data T class A a instance A (S a) instance A (S T)"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "data S a b data T data U class A a instance A (S a T) instance A (S a U)"
      ==> "data S (a : Type) (b : Type) data T data U class A (a : Type) instance [(a : Type)] A (S a T) instance [(a : Type)] A (S a U)"
    "data S a b data T data U class A a instance A (S a T) instance A (S U a)"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "class A a instance A a instance A (f a)"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "class A a b instance A a a instance A a b"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "data T class A a b instance A a a instance A a T"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "class A a b instance A a a instance A a (f a)"
      ==> "class A (a : Type) (b : Type) instance [(a : Type)] A a a instance [(a : Type) (f : Type -> Type)] A a (f a)"
    "data T data U class A a b instance A a T instance A U a"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "data T data U class A a b instance A a T instance A a U"
      ==> "data T data U class A (a : Type) (b : Type) instance [(a : Type)] A a T instance [(a : Type)] A a U"
  it "implicit defs" $ do
    "val f = A data T { con A }"
      ==> "val f : [] T = A data T { con A }"
    "val f = A data S data T { con A S }"
      ==> "val f : [] S -> T = A data S data T { con A S }"
    "val f = A data T x { con A x }"
      ==> "val f : [(a : Type)] a -> T a = A data T (x : Type) { con A x }"
    "val f = A data T x { con A }"
      ==> "val f : [(a : Type)] T a = A data T (x : Type) { con A }"
    "val f = g val g : x -> x"
      ==> "val f : [(a : Type)] a -> a = g val g : [(x : Type)] x -> x"
    "val f = g val g : x -> y"
      ==> "val f : [(a : Type) (b : Type)] a -> b = g val g : [(x : Type) (y : Type)] x -> y"
    "val f = g T val g : x -> x data A { con T }"
      ==> "val f : [] A = g T val g : [(x : Type)] x -> x data A { con T }"
    "val f = g T val g : x data A { con T }"
      ==> "val f : [(a : Type)] a = g T val g : [(x : Type)] x data A { con T }"
    "val f = g T val g : A data A { con T }"
      ==>! \case CannotUnifyType _ _ _ -> True; _ -> False
    "val f = 'a' data Char"
      ==> "val f : [] Char = 'a' data Char"
    "val f = \"foo\" data Char data List a"
      ==> "val f : [] List Char = \"foo\" data Char data List (a : Type)"
    "val f = 0 class Num x"
      ==> "val f : [(a : Type)] a where Num a = 0 class Num (x : Type)"
    "val f = 0.5 class Fractional x"
      ==> "val f : [(a : Type)] a where Fractional a = 0.5 class Fractional (x : Type)"
    "val f = fun _ -> A data T { con A }"
      ==> "val f : [(a : Type)] a -> T = fun _ -> A data T { con A }"
    "val f = fun x -> x"
      ==> "val f : [(a : Type)] a -> a = fun x -> x"
    "val f = fun x y -> x"
      ==> "val f : [(a : Type) (b : Type)] a -> b -> a = fun x y -> x"
    "val f = fun x y -> y"
      ==> "val f : [(a : Type) (b : Type)] a -> b -> b = fun x y -> y"
    "val f = fun x y -> y x"
      ==> "val f : [(a : Type) (b : Type)] a -> (a -> b) -> b = fun x y -> y x"
    "val f = fun x y -> x x"
      ==>! \case CannotUnifyType _ _ OccursCheckFailed -> True; _ -> False
    "val f = fun 'a' -> 'b' | x -> x data Char"
      ==> "val f : [] Char -> Char = fun 'a' -> 'b' | x -> x data Char"
    "val f = fun 'a' -> 'b' | 'a' -> 'd' data Char"
      ==>! \case UselessPattern "'a'" -> True; _ -> False
    "val f = fun 'a' -> 'b' data Char"
      ==>! \case NonExhaustivePattern ["_"] -> True; _ -> False
    "val f = fun 'a' y -> y | x y -> x data Char"
      ==> "val f : [] Char -> Char -> Char = fun 'a' y -> y | x y -> x data Char"
    "val f = fun 'a' -> 'b' | \"a\" -> 'b' data Char data List a"
      ==>! \case CannotUnifyType _ _ _ -> True; _ -> False
    "val f = fun 'a' -> 'b' | \"a\" -> 'b' data Char data List a"
      ==>! \case CannotUnifyType _ _ _ -> True; _ -> False
    "val f = fun x 'a' -> 'a' | y -> y data Char"
      ==>! \case ArityMismatch 2 _ -> True; _ -> False
    "val f = fun A -> A data T { con A }"
      ==> "val f : [] T -> T = fun A -> A data T { con A }"
    "val f = fun A -> A data T a { con A con B con C a }"
      ==>! \case NonExhaustivePattern ["B", "(C _)"] -> True; _ -> False
    "val f = fun (A a) -> A data T { con A }"
      ==>! \case CannotUnifyType _ _ _ -> True; _ -> False
    "val f = fun A -> A data T { con A T }"
      ==>! \case ArityMismatch 1 _ -> True; _ -> False
    "val f = fun (A x y) -> y data T x { con A x x }"
      ==> "val f : [(a : Type)] T a -> a = fun (A x y) -> y data T (x : Type) { con A x x }"
    "val f = fun x@10 _ -> x | _ y -> y class Num x"
      ==> "val f : [(a : Type)] a -> a -> a where Num a = fun x@10 _ -> x | _ y -> y class Num (x : Type)"
    "val f = g val g = f"
      ==> "val f : [(a : Type)] a = g val g : [(b : Type)] b = f"
    "val any val f = (fun (Pair x _) -> x) g val g = Pair f any data Pair x y { con Pair x y }"
      ==> "val any : [(a : Type)] a val f : [(d : Type)] d = (fun (Pair x _) -> x) g val g : [(b : Type) (c : Type)] Pair b c = Pair f any data Pair (x : Type) (y : Type) { con Pair x y }"
    "val f = fun (Cons x _) -> x data List x { con Cons x (List x) }"
      ==> "val f : [(a : Type)] List a -> a = fun (Cons x _) -> x data List (x : Type) { con Cons x (List x) }"
  it "explicit defs" $ do
    "val f : a = f"
      ==> "val f : [(a : Type)] a = f"
    "val f : T = B data T { con A } data U { con B }"
      ==>! \case CannotUnifyType _ _ Mismatch -> True; _ -> False
    "val f : a = 'a' data Char"
      ==>! \case CannotUnifyType _ _ SignatureTooGeneral -> True; _ -> False
    "val f : a -> a = fun x -> x"
      ==> "val f : [(a : Type)] a -> a = fun x -> x"
    "val f : T -> T = fun x -> x data T"
      ==> "val f : [] T -> T = fun x -> x data T"
    "val f : T -> a -> b = fun x y -> y data T"
      ==>! \case CannotUnifyType _ _ SignatureTooGeneral -> True; _ -> False
    "val f : T = 0 data T class Num x"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : a val g : a = f 0 class Num x"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    -- NOTE: Currently Titan behaves like GHC with AllowAmbiguousTypes enabled.
    "val f : a where F b class F x"
      ==> "val f : [(a : Type) (b : Type)] a where F b class F (x : Type)"
    "val f : a where F b val g = f class F x"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    -- Polymorphic recursion
    "val f = fun Leaf -> 0 | (Bin _ x) -> f x data Pair x y { con Pair x y } data Tree t { con Bin t (Tree (Pair t t)) con Leaf } class Num a"
      ==>! \case CannotUnifyType _ _ OccursCheckFailed -> True; _ -> False
    "val f : Tree a -> b where Num b = fun Leaf -> 0 | (Bin _ x) -> f x data Pair x y { con Pair x y } data Tree t { con Bin t (Tree (Pair t t)) con Leaf } class Num a"
      ==> "val f : [(a : Type) (b : Type)] Tree a -> b where Num b = fun Leaf -> 0 | (Bin _ x) -> f x data Pair (x : Type) (y : Type) { con Pair x y } data Tree (t : Type) { con Bin t (Tree (Pair t t)) con Leaf } class Num (a : Type)"
  it "nested defs" $ do
    "val f = fun x -> let g = fun y -> y in g x"
      ==> "val f : [(b : Type)] b -> b = fun x -> let g : [(a : Type)] a -> a = fun y -> y in g x"
    "val f = fun x -> let g = fun _ -> h x in g A val h : x -> T where F x data T { con A } class F x"
      ==> "val f : [(b : Type)] b -> T where F b = fun x -> let g : [(a : Type)] a -> T = fun _ -> h x in g A val h : [(x : Type)] x -> T where F x data T { con A } class F (x : Type)"
    "val any : x val f : [a b] a -> b = fun x -> let g : [c] a -> c = fun y -> any in g x"
      ==> "val any : [(x : Type)] x val f : [(a : Type) (b : Type)] a -> b = fun x -> let g : [(c : Type)] a -> c = fun y -> any in g x"
    -- NoMonoLocalBinds
    "val f : x -> y -> y where F x y val g = fun a -> let h = fun b -> f a b in Pair (h 0) (h 'a') data Char data Pair x y { con Pair x y } class F x y class Num x"
      ==> "val f : [(x : Type) (y : Type)] x -> y -> y where F x y val g : [(b : Type) (c : Type)] b -> Pair c Char where (F b c, Num c, F b Char) = fun a -> let h : [(a : Type)] a -> a where F b a = fun b -> f a b in Pair (h 0) (h 'a') data Char data Pair (x : Type) (y : Type) { con Pair x y } class F (x : Type) (y : Type) class Num (x : Type)"
    "val f = fun x -> let g = fun y z -> S (T x y) z in g 'a' data Char data S x y { con S x y } data T x { con T x x }"
      ==> "val f : [(b : Type)] Char -> b -> S (T Char) b = fun x -> let g : [(a : Type)] Char -> a -> S (T Char) a = fun y z -> S (T x y) z in g 'a' data Char data S (x : Type) (y : Type) { con S x y } data T (x : Type) { con T x x }"
    "val f = fun x -> let g : a -> b -> S (T a) b = fun y z -> S (T x y) z in g 'a' data Char data S x y { con S x y } data T x { con T x x }"
      ==>! \case CannotUnifyType _ _ SignatureTooGeneral -> True; _ -> False
  it "class methods" $ do
    "class F { val f : a }"
      ==> "class F { val f : [(a : Type)] a }"
    "val g = f class F { val f : a }"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val g : a = f class F { val f : a }"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val g : a where F = f class F { val f : a }"
      ==> "val g : [(a : Type)] a where F = f class F { val f : [(a : Type)] a }"
    "val g = f class F a { val f : a }"
      ==> "val g : [(b : Type)] b where F b = f class F (a : Type) { val f : [] a }"
    "val g = f class F a { val f : a -> b }"
      ==> "val g : [(c : Type) (d : Type)] c -> d where F c = f class F (a : Type) { val f : [(b : Type)] a -> b }"
    "data Char class F a { val f : Char = 'a' }"
      ==> "data Char class F (a : Type) { val f : [] Char = 'a' }"
    "class F a { val f : a -> a = fun x -> x }"
      ==> "class F (a : Type) { val f : [] a -> a = fun x -> x }"
    "class F a { val f : a -> b -> b = fun x y -> y }"
      ==> "class F (a : Type) { val f : [(b : Type)] a -> b -> b = fun x y -> y }"
    "class F a { val f : a -> a = fun x -> f x }"
      ==> "class F (a : Type) { val f : [] a -> a = fun x -> f x }"
    "val g : Char -> Char class F a { val f : a -> a = fun x -> g x } data Char"
      ==>! \case CannotUnifyType _ _ SignatureTooGeneral -> True; _ -> False
    "class F a { val f : a -> a = fun x -> g x } class G a { val g : a -> a }"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "class F a where G a { val f : a -> a = fun x -> g x } class G a { val g : a -> a }"
      ==> "class F (a : Type) where G a { val f : [] a -> a = fun x -> g x } class G (a : Type) { val g : [] a -> a }"
  it "entailment" $ do
    "val f : Int = 0 data Int class Num x instance Num Int"
      ==> "val f : [] Int = 0 data Int class Num (x : Type) instance [] Num Int"
    "val f : Int = 0.0 data Int class Num x class Fractional x where Num x instance Num Int"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : Float = 0.0 data Float class Fractional x where Num x class Num x instance Fractional Float instance Num Float"
      ==> "val f : [] Float = 0.0 data Float class Fractional (x : Type) where Num x class Num (x : Type) instance [] Fractional Float instance [] Num Float"
    "val f : a where Num a = f class Num x"
      ==> "val f : [(a : Type)] a where Num a = f class Num (x : Type)"
    "val f : a where Num a = 0 class Num x"
      ==> "val f : [(a : Type)] a where Num a = 0 class Num (x : Type)"
    "val f : a where Fractional a = 0 class Fractional x"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : a where Fractional a = 0 class Fractional x where Num x class Num x"
      ==> "val f : [(a : Type)] a where Fractional a = 0 class Fractional (x : Type) where Num x class Num (x : Type)"
    "val f : a where Fractional a = 0 class Fractional x where Nu x class Nu x where Num x class Num x"
      ==> "val f : [(a : Type)] a where Fractional a = 0 class Fractional (x : Type) where Nu x class Nu (x : Type) where Num x class Num (x : Type)"
    "val f : T = 0 data T class Num x instance Num a"
      ==> "val f : [] T = 0 data T class Num (x : Type) instance [(a : Type)] Num a"
    "val f : T = 0 data T class Num x instance Num a where Num a"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : Pair T a = 0 data Pair x y { con Pair x y } data T class Num x instance Num (Pair x y)"
      ==> "val f : [(a : Type)] Pair T a = 0 data Pair (x : Type) (y : Type) { con Pair x y } data T class Num (x : Type) instance [(x : Type) (y : Type)] Num (Pair x y)"
    "val f : Pair T a = 0 data Pair x y { con Pair x y } data T class Num x instance Num (Pair x y) where (Num x, Num y)"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : Pair T a = 0 data Pair x y { con Pair x y } data T class Num x instance Num T instance Num (Pair x y) where (Num x, Num y)"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : Pair T a where Num a = 0 data Pair x y { con Pair x y } data T class Num x instance Num T instance Num (Pair x y) where (Num x, Num y)"
      ==> "val f : [(a : Type)] Pair T a where Num a = 0 data Pair (x : Type) (y : Type) { con Pair x y } data T class Num (x : Type) instance [] Num T instance [(x : Type) (y : Type)] Num (Pair x y) where (Num x, Num y)"
    "val f : Pair T a where Fractional a = 0 data Pair x y { con Pair x y } data T class Fractional x where Num x class Num x instance Num T instance Num (Pair x y) where (Num x, Num y)"
      ==> "val f : [(a : Type)] Pair T a where Fractional a = 0 data Pair (x : Type) (y : Type) { con Pair x y } data T class Fractional (x : Type) where Num x class Num (x : Type) instance [] Num T instance [(x : Type) (y : Type)] Num (Pair x y) where (Num x, Num y)"
    "val f : Pair T a = 0 data Pair x y { con Pair x y } data T class Num x class X x instance Num T instance Num (Pair x y) where (Num x, X y) instance X x"
      ==> "val f : [(a : Type)] Pair T a = 0 data Pair (x : Type) (y : Type) { con Pair x y } data T class Num (x : Type) class X (x : Type) instance [] Num T instance [(x : Type) (y : Type)] Num (Pair x y) where (Num x, X y) instance [(x : Type)] X x"
  it "defaults" $ do
    "val f = (fun (Pair x _) -> x) g val g = Pair f 0 data Pair x y { con Pair x y } class Num x"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val f = (fun (Pair x _) -> x) g val g = Pair f 0 data Int data Pair x y { con Pair x y } class Num x default { Int }"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val f = (fun (Pair x _) -> x) g val g = Pair f 0 data Int data Pair x y { con Pair x y } class Num x instance Num Int default { Int }"
      ==> "val f : [(a : Type)] a = (fun (Pair x _) -> x) g val g : [(b : Type) (c : Type)] Pair c b where Num b = Pair f 0 data Int data Pair (x : Type) (y : Type) { con Pair x y } class Num (x : Type) instance [] Num Int default { Int }"
    "val f = (fun (Pair x _) -> incr x) g val g = Pair f 0 data Int data Pair x y { con Pair x y } class Num x { val incr : x -> x } instance Num Int default { Int }"
      ==> "val f : [(a : Type)] a where Num a = (fun (Pair x _) -> incr x) g val g : [(b : Type) (c : Type)] Pair b c where (Num b, Num c) = Pair f 0 data Int data Pair (x : Type) (y : Type) { con Pair x y } class Num (x : Type) { val incr : [] x -> x } instance [] Num Int default { Int }"
    "val h : Char -> Char = fun x -> g (f x) val f : Char -> a where C a val g : a -> Char where C a data Char class C x"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val f val g = f h class Functor f { val h : f x }"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    -- FIXME: This should be resolvable:
    "val f val g = f h class Functor f { val h : f x } instance Functor f"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val f val g = f h data Maybe t class Functor f { val h : f x } instance Functor Maybe default { Maybe }"
      ==> "val f : [(a : Type)] a val g : [(b : Type)] b = f h data Maybe (t : Type) class Functor (f : Type -> Type) { val h : [(x : Type)] f x } instance [] Functor Maybe default { Maybe }"
    "val f val g = f h data Int data Maybe t class Functor f { val h : f x } instance Functor Maybe default { Int Maybe }"
      ==> "val f : [(a : Type)] a val g : [(b : Type)] b = f h data Int data Maybe (t : Type) class Functor (f : Type -> Type) { val h : [(x : Type)] f x } instance [] Functor Maybe default { Int Maybe }"
