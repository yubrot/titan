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
      ==> "data S data T class A (a : *) instance [] A S instance [] A T"
    "data S a data T a class A a instance A (S a) instance A (T a)"
      ==> "data S (a : *) data T (a : *) class A (a : *) instance [(a : *)] A (S a) instance [(a : *)] A (T a)"
    "data S a class A a instance A (S a) instance A (S a)"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "data S a data T class A a instance A (S a) instance A (S T)"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "data S a b data T data U class A a instance A (S a T) instance A (S a U)"
      ==> "data S (a : *) (b : *) data T data U class A (a : *) instance [(a : *)] A (S a T) instance [(a : *)] A (S a U)"
    "data S a b data T data U class A a instance A (S a T) instance A (S U a)"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "class A a instance A a instance A (f a)"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "class A a b instance A a a instance A a b"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "data T class A a b instance A a a instance A a T"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "class A a b instance A a a instance A a (f a)"
      ==> "class A (a : *) (b : *) instance [(a : *)] A a a instance [(a : *) (f : * -> *)] A a (f a)"
    "data T data U class A a b instance A a T instance A U a"
      ==>! \case OverlappingInstances _ _ -> True; _ -> False
    "data T data U class A a b instance A a T instance A a U"
      ==> "data T data U class A (a : *) (b : *) instance [(a : *)] A a T instance [(a : *)] A a U"
    "data T class F a class G a where F a instance G T"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "data T class F a class G a where F a instance F T instance G T"
      ==> "data T class F (a : *) class G (a : *) where F a instance [] F T instance [] G T"
    "data T a class F a class G a where F a instance F (T a) where F a instance G (T a)"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "data T a class F a class G a where F a instance F (T a) where F a instance G (T a) where F a"
      ==> "data T (a : *) class F (a : *) class G (a : *) where F a instance [(a : *)] F (T a) where F a instance [(a : *)] G (T a) where F a"
    "data T a class F a class G a where F a instance F (T a) where F a instance G (T a) where G a"
      ==> "data T (a : *) class F (a : *) class G (a : *) where F a instance [(a : *)] F (T a) where F a instance [(a : *)] G (T a) where G a"
    "data T a class F a class G a where F a instance F (T a) where G a instance G (T a) where G a"
      ==> "data T (a : *) class F (a : *) class G (a : *) where F a instance [(a : *)] F (T a) where G a instance [(a : *)] G (T a) where G a"
  it "implicit defs" $ do
    "val f = A data T { con A }"
      ==> "val f : [] T = A data T { con A }"
    "val f = A data S data T { con A S }"
      ==> "val f : [] S -> T = A data S data T { con A S }"
    "val f = A data T x { con A x }"
      ==> "val f : [(a : *)] a -> T a = A data T (x : *) { con A x }"
    "val f = A data T x { con A }"
      ==> "val f : [(a : *)] T a = A data T (x : *) { con A }"
    "val f = g val g : x -> x"
      ==> "val f : [(a : *)] a -> a = g val g : [(x : *)] x -> x"
    "val f = g val g : x -> y"
      ==> "val f : [(a : *) (b : *)] a -> b = g val g : [(x : *) (y : *)] x -> y"
    "val f = g T val g : x -> x data A { con T }"
      ==> "val f : [] A = g T val g : [(x : *)] x -> x data A { con T }"
    "val f = g T val g : x data A { con T }"
      ==> "val f : [(a : *)] a = g T val g : [(x : *)] x data A { con T }"
    "val f = g T val g : A data A { con T }"
      ==>! \case CannotUnifyType _ _ _ -> True; _ -> False
    "val f = 'a' data Char"
      ==> "val f : [] Char = 'a' data Char"
    "val f = \"foo\" data Char data List a"
      ==> "val f : [] List Char = \"foo\" data Char data List (a : *)"
    "val f = 0 class Num x"
      ==> "val f : [(a : *)] a where Num a = 0 class Num (x : *)"
    "val f = 0.5 class Fractional x"
      ==> "val f : [(a : *)] a where Fractional a = 0.5 class Fractional (x : *)"
    "val f = fun _ -> A data T { con A }"
      ==> "val f : [(a : *)] a -> T = fun _ -> A data T { con A }"
    "val f = fun x -> x"
      ==> "val f : [(a : *)] a -> a = fun x -> x"
    "val f = fun x y -> x"
      ==> "val f : [(a : *) (b : *)] a -> b -> a = fun x y -> x"
    "val f = fun x y -> y"
      ==> "val f : [(a : *) (b : *)] a -> b -> b = fun x y -> y"
    "val f = fun x y -> y x"
      ==> "val f : [(a : *) (b : *)] a -> (a -> b) -> b = fun x y -> y x"
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
      ==> "val f : [(a : *)] T a -> a = fun (A x y) -> y data T (x : *) { con A x x }"
    "val f = fun x@10 _ -> x | _ y -> y class Num x"
      ==> "val f : [(a : *)] a -> a -> a where Num a = fun x@10 _ -> x | _ y -> y class Num (x : *)"
    "val f = g val g = f"
      ==> "val f : [(a : *)] a = g val g : [(b : *)] b = f"
    "val any val f = (fun (Pair x _) -> x) g val g = Pair f any data Pair x y { con Pair x y }"
      ==> "val any : [(a : *)] a val f : [(d : *)] d = (fun (Pair x _) -> x) g val g : [(b : *) (c : *)] Pair b c = Pair f any data Pair (x : *) (y : *) { con Pair x y }"
    "val f = fun (Cons x _) -> x data List x { con Cons x (List x) }"
      ==> "val f : [(a : *)] List a -> a = fun (Cons x _) -> x data List (x : *) { con Cons x (List x) }"
    "val f = fun x -> show (Pair x x) val show : x -> String where Show x data Pair x y { con Pair x y } data String class Show x"
      ==> "val f : [(a : *)] a -> String where Show (Pair a a) = fun x -> show (Pair x x) val show : [(x : *)] x -> String where Show x data Pair (x : *) (y : *) { con Pair x y } data String class Show (x : *)"
    "val f = fun x -> show (Pair x x) val show : x -> String where Show x data Pair x y { con Pair x y } data String class Show x instance Show (Pair x y) where (Show x, Show y)"
      ==> "val f : [(a : *)] a -> String where Show a = fun x -> show (Pair x x) val show : [(x : *)] x -> String where Show x data Pair (x : *) (y : *) { con Pair x y } data String class Show (x : *) instance [(x : *) (y : *)] Show (Pair x y) where (Show x, Show y)"
  it "explicit defs" $ do
    "val f : a = f"
      ==> "val f : [(a : *)] a = f"
    "val f : T = B data T { con A } data U { con B }"
      ==>! \case CannotUnifyType _ _ Mismatch -> True; _ -> False
    "val f : a = 'a' data Char"
      ==>! \case CannotUnifyType _ _ SignatureTooGeneral -> True; _ -> False
    "val f : a -> a = fun x -> x"
      ==> "val f : [(a : *)] a -> a = fun x -> x"
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
      ==> "val f : [(a : *) (b : *)] a where F b class F (x : *)"
    "val f : a where F b val g = f class F x"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    -- Polymorphic recursion
    "val f = fun Leaf -> 0 | (Bin _ x) -> f x data Pair x y { con Pair x y } data Tree t { con Bin t (Tree (Pair t t)) con Leaf } class Num a"
      ==>! \case CannotUnifyType _ _ OccursCheckFailed -> True; _ -> False
    "val f : Tree a -> b where Num b = fun Leaf -> 0 | (Bin _ x) -> f x data Pair x y { con Pair x y } data Tree t { con Bin t (Tree (Pair t t)) con Leaf } class Num a"
      ==> "val f : [(a : *) (b : *)] Tree a -> b where Num b = fun Leaf -> 0 | (Bin _ x) -> f x data Pair (x : *) (y : *) { con Pair x y } data Tree (t : *) { con Bin t (Tree (Pair t t)) con Leaf } class Num (a : *)"
  it "nested defs" $ do
    "val f = fun x -> let g = fun y -> y in g x"
      ==> "val f : [(b : *)] b -> b = fun x -> let g : [(a : *)] a -> a = fun y -> y in g x"
    "val f = fun x -> let g = fun _ -> h x in g A val h : x -> T where F x data T { con A } class F x"
      ==> "val f : [(b : *)] b -> T where F b = fun x -> let g : [(a : *)] a -> T = fun _ -> h x in g A val h : [(x : *)] x -> T where F x data T { con A } class F (x : *)"
    "val any : x val f : [a b] a -> b = fun x -> let g : [c] a -> c = fun y -> any in g x"
      ==> "val any : [(x : *)] x val f : [(a : *) (b : *)] a -> b = fun x -> let g : [(c : *)] a -> c = fun y -> any in g x"
    -- NoMonoLocalBinds
    "val f : x -> y -> y where F x y val g = fun a -> let h = fun b -> f a b in Pair (h 0) (h 'a') data Char data Pair x y { con Pair x y } class F x y class Num x"
      ==> "val f : [(x : *) (y : *)] x -> y -> y where F x y val g : [(b : *) (c : *)] b -> Pair c Char where (F b Char, F b c, Num c) = fun a -> let h : [(a : *)] a -> a where F b a = fun b -> f a b in Pair (h 0) (h 'a') data Char data Pair (x : *) (y : *) { con Pair x y } class F (x : *) (y : *) class Num (x : *)"
    "val f = fun x -> let g = fun y z -> S (T x y) z in g 'a' data Char data S x y { con S x y } data T x { con T x x }"
      ==> "val f : [(b : *)] Char -> b -> S (T Char) b = fun x -> let g : [(a : *)] Char -> a -> S (T Char) a = fun y z -> S (T x y) z in g 'a' data Char data S (x : *) (y : *) { con S x y } data T (x : *) { con T x x }"
    "val f = fun x -> let g : a -> b -> S (T a) b = fun y z -> S (T x y) z in g 'a' data Char data S x y { con S x y } data T x { con T x x }"
      ==>! \case CannotUnifyType _ _ SignatureTooGeneral -> True; _ -> False
  it "class methods" $ do
    "class F { val f : a }"
      ==> "class F { val f : [(a : *)] a }"
    "val g = f class F { val f : a }"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val g = f class F { val f : a } instance F"
      ==> "val g : [(b : *)] b = f class F { val f : [(a : *)] a } instance [] F"
    "val g : a = f class F { val f : a }"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val g : a where F = f class F { val f : a }"
      ==> "val g : [(a : *)] a where F = f class F { val f : [(a : *)] a }"
    "val g = f class F a { val f : a }"
      ==> "val g : [(b : *)] b where F b = f class F (a : *) { val f : [] a }"
    "val g = f class F a { val f : a } instance F a"
      ==> "val g : [(b : *)] b = f class F (a : *) { val f : [] a } instance [(a : *)] F a"
    "val g = f class F a { val f : a -> b }"
      ==> "val g : [(c : *) (d : *)] c -> d where F c = f class F (a : *) { val f : [(b : *)] a -> b }"
    "data Char class F a { val f : Char = 'a' }"
      ==> "data Char class F (a : *) { val f : [] Char = 'a' }"
    "class F a { val f : a -> a = fun x -> x }"
      ==> "class F (a : *) { val f : [] a -> a = fun x -> x }"
    "class F a { val f : a -> b -> b = fun x y -> y }"
      ==> "class F (a : *) { val f : [(b : *)] a -> b -> b = fun x y -> y }"
    "class F a { val f : a -> a = fun x -> f x }"
      ==> "class F (a : *) { val f : [] a -> a = fun x -> f x }"
    "val g : Char -> Char class F a { val f : a -> a = fun x -> g x } data Char"
      ==>! \case CannotUnifyType _ _ SignatureTooGeneral -> True; _ -> False
    "class F a { val f : a -> a = fun x -> g x } class G a { val g : a -> a }"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "class F a where G a { val f : a -> a = fun x -> g x } class G a { val g : a -> a }"
      ==> "class F (a : *) where G a { val f : [] a -> a = fun x -> g x } class G (a : *) { val g : [] a -> a }"
  it "entailment" $ do
    "val f : Int = 0 data Int class Num x instance Num Int"
      ==> "val f : [] Int = 0 data Int class Num (x : *) instance [] Num Int"
    "val f : Int = 0.0 data Int class Num x class Fractional x where Num x instance Num Int"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : Float = 0.0 data Float class Fractional x where Num x class Num x instance Fractional Float instance Num Float"
      ==> "val f : [] Float = 0.0 data Float class Fractional (x : *) where Num x class Num (x : *) instance [] Fractional Float instance [] Num Float"
    "val f : a where Num a = f class Num x"
      ==> "val f : [(a : *)] a where Num a = f class Num (x : *)"
    "val f : a where Num a = 0 class Num x"
      ==> "val f : [(a : *)] a where Num a = 0 class Num (x : *)"
    "val f : a where Fractional a = 0 class Fractional x class Num x"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : a where Fractional a = 0 class Fractional x where Num x class Num x"
      ==> "val f : [(a : *)] a where Fractional a = 0 class Fractional (x : *) where Num x class Num (x : *)"
    "val f : a where Fractional a = 0 class Fractional x where Nu x class Nu x where Num x class Num x"
      ==> "val f : [(a : *)] a where Fractional a = 0 class Fractional (x : *) where Nu x class Nu (x : *) where Num x class Num (x : *)"
    "val f : T = 0 data T class Num x instance Num a"
      ==> "val f : [] T = 0 data T class Num (x : *) instance [(a : *)] Num a"
    "val f : T = 0 data T class Num x instance Num a where Num a"
      ==>! \case InstanceResolutionExhausted _ -> True; _ -> False
    "val f : Pair T a = 0 data Pair x y { con Pair x y } data T class Num x instance Num (Pair x y)"
      ==> "val f : [(a : *)] Pair T a = 0 data Pair (x : *) (y : *) { con Pair x y } data T class Num (x : *) instance [(x : *) (y : *)] Num (Pair x y)"
    "val f : Pair T a = 0 data Pair x y { con Pair x y } data T class Num x instance Num (Pair x y) where (Num x, Num y)"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : Pair T a = 0 data Pair x y { con Pair x y } data T class Num x instance Num T instance Num (Pair x y) where (Num x, Num y)"
      ==>! \case NoMatchingInstances _ _ -> True; _ -> False
    "val f : Pair T a where Num a = 0 data Pair x y { con Pair x y } data T class Num x instance Num T instance Num (Pair x y) where (Num x, Num y)"
      ==> "val f : [(a : *)] Pair T a where Num a = 0 data Pair (x : *) (y : *) { con Pair x y } data T class Num (x : *) instance [] Num T instance [(x : *) (y : *)] Num (Pair x y) where (Num x, Num y)"
    "val f : Pair T a where Fractional a = 0 data Pair x y { con Pair x y } data T class Fractional x where Num x class Num x instance Num T instance Num (Pair x y) where (Num x, Num y)"
      ==> "val f : [(a : *)] Pair T a where Fractional a = 0 data Pair (x : *) (y : *) { con Pair x y } data T class Fractional (x : *) where Num x class Num (x : *) instance [] Num T instance [(x : *) (y : *)] Num (Pair x y) where (Num x, Num y)"
    "val f : Pair T a = 0 data Pair x y { con Pair x y } data T class Num x class X x instance Num T instance Num (Pair x y) where (Num x, X y) instance X x"
      ==> "val f : [(a : *)] Pair T a = 0 data Pair (x : *) (y : *) { con Pair x y } data T class Num (x : *) class X (x : *) instance [] Num T instance [(x : *) (y : *)] Num (Pair x y) where (Num x, X y) instance [(x : *)] X x"
  it "defaults" $ do
    "val f = (fun (Pair x _) -> x) g val g = Pair f 0 data Pair x y { con Pair x y } class Num x"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val f = (fun (Pair x _) -> x) g val g = Pair f 0 data Int data Pair x y { con Pair x y } class Num x default { Int }"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val f = (fun (Pair x _) -> x) g val g = Pair f 0 data Int data Pair x y { con Pair x y } class Num x instance Num Int default { Int }"
      ==> "val f : [(a : *)] a = (fun (Pair x _) -> x) g val g : [(b : *) (c : *)] Pair b c where Num c = Pair f 0 data Int data Pair (x : *) (y : *) { con Pair x y } class Num (x : *) instance [] Num Int default { Int }"
    "val f = (fun (Pair x _) -> incr x) g val g = Pair f 0 data Int data Pair x y { con Pair x y } class Num x { val incr : x -> x } instance Num Int default { Int }"
      ==> "val f : [(a : *)] a where Num a = (fun (Pair x _) -> incr x) g val g : [(b : *) (c : *)] Pair b c where (Num b, Num c) = Pair f 0 data Int data Pair (x : *) (y : *) { con Pair x y } class Num (x : *) { val incr : [] x -> x } instance [] Num Int default { Int }"
    "val h : Char -> Char = fun x -> g (f x) val f : Char -> a where C a val g : a -> Char where C a data Char class C x"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val f val g = f h class Functor f { val h : f x }"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val f val g = f h class Functor f { val h : f x } instance Functor f"
      ==> "val f : [(a : *)] a val g : [(b : *)] b = f h class Functor (f : * -> *) { val h : [(x : *)] f x } instance [(f : * -> *)] Functor f"
    "val f val g = f h data Maybe t class Functor f { val h : f x } instance Functor Maybe"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val f val g = f h data Maybe t class Functor f { val h : f x } instance Functor Maybe default { Maybe }"
      ==> "val f : [(a : *)] a val g : [(b : *)] b = f h data Maybe (t : *) class Functor (f : * -> *) { val h : [(x : *)] f x } instance [] Functor Maybe default { Maybe }"
    "val f val g = f h data Int data Maybe t class Functor f { val h : f x } instance Functor Maybe default { Int Maybe }"
      ==> "val f : [(a : *)] a val g : [(b : *)] b = f h data Int data Maybe (t : *) class Functor (f : * -> *) { val h : [(x : *)] f x } instance [] Functor Maybe default { Int Maybe }"
  it "verify classes with functional dependencies" $ do
    "class F a b | a ~> b"
      ==> "class F (a : *) (b : *) | a ~> b"
    "class F a b | a ~> b class G a b where F a b"
      ==>! \case FundepsAreWeakerThanSuperclasses _ _ -> True; _ -> False
    "class F a b | a ~> b class G a b | a ~> b where F a b"
      ==> "class F (a : *) (b : *) | a ~> b class G (a : *) (b : *) | a ~> b where F a b"
    "class F a b | a ~> b class G a b c | a c ~> b where F a b"
      ==>! \case FundepsAreWeakerThanSuperclasses _ _ -> True; _ -> False
    "class F a b c | a b ~> c class G a b c | a ~> c where F a b c"
      ==> "class F (a : *) (b : *) (c : *) | a b ~> c class G (a : *) (b : *) (c : *) | a ~> c where F a b c"
    "class F a b c | a b ~> c class G a b | a ~> b where F a b b"
      ==> "class F (a : *) (b : *) (c : *) | a b ~> c class G (a : *) (b : *) | a ~> b where F a b b"
    "class F a b | a ~> b class G b a | a ~> b where F b a"
      ==>! \case FundepsAreWeakerThanSuperclasses _ _ -> True; _ -> False
    "class F a b c | a ~> b class G a b c | a ~> b c where F a c b"
      ==> "class F (a : *) (b : *) (c : *) | a ~> b class G (a : *) (b : *) (c : *) | a ~> b c where F a c b"
    "class F a b c | a ~> b c class G a b c | a ~> b where F a b c"
      ==>! \case FundepsAreWeakerThanSuperclasses _ _ -> True; _ -> False
  it "verify instances with functional dependencies" $ do
    "class F a b instance F a b"
      ==> "class F (a : *) (b : *) instance [(a : *) (b : *)] F a b"
    "data A data B class F a b | a ~> b instance F A B"
      ==> "data A data B class F (a : *) (b : *) | a ~> b instance [] F A B"
    "data A data B class F a b | a ~> b instance F a b"
      ==>! \case CoverageConditionUnsatisfied _ _ -> True; _ -> False
    "data T a class F a b | a ~> b instance F (T a) a"
      ==> "data T (a : *) class F (a : *) (b : *) | a ~> b instance [(a : *)] F (T a) a"
    "data T a class F a b | a ~> b instance F a (T a)"
      ==> "data T (a : *) class F (a : *) (b : *) | a ~> b instance [(a : *)] F a (T a)"
    "data A class F a b | a ~> b instance F a A"
      ==> "data A class F (a : *) (b : *) | a ~> b instance [(a : *)] F a A"
    "data A class F a b | a ~> b instance F A a"
      ==>! \case CoverageConditionUnsatisfied _ _ -> True; _ -> False
    "data T a class F a b | a ~> b instance F (T x) y where F x y"
      ==> "data T (a : *) class F (a : *) (b : *) | a ~> b instance [(x : *) (y : *)] F (T x) y where F x y"
    "class F a b | a ~> b instance F x y where F x x"
      ==>! \case CoverageConditionUnsatisfied _ _ -> True; _ -> False
    "data A data B class F a b | a ~> b instance F A A instance F B A"
      ==> "data A data B class F (a : *) (b : *) | a ~> b instance [] F A A instance [] F B A"
    "data A data B class F a b | a ~> b instance F A A instance F A B"
      ==>! \case ConsistencyConditionUnsatisfied _ _ _ -> True; _ -> False
    "data A data B data T a b class F a b c | a ~> b instance F (T a b) a A instance F (T a b) a B"
      ==> "data A data B data T (a : *) (b : *) class F (a : *) (b : *) (c : *) | a ~> b instance [(a : *) (b : *)] F (T a b) a A instance [(a : *) (b : *)] F (T a b) a B"
    "data A data B data T a b class F a b c | a ~> b instance F (T a b) a A instance F (T a b) b B"
      ==>! \case ConsistencyConditionUnsatisfied _ _ _ -> True; _ -> False
    "data Float data Int class Add a b c | a b ~> c instance Add Float Float Float instance Add Float Int Float instance Add Int Float Float instance Add Int Int Int"
      ==> "data Float data Int class Add (a : *) (b : *) (c : *) | a b ~> c instance [] Add Float Float Float instance [] Add Float Int Float instance [] Add Int Float Float instance [] Add Int Int Int"
    "data Float data Int class Add a b c | a b ~> c instance Add Float Float Float instance Add Float Int Float instance Add Int Float Float instance Add Int Int Int instance Add Int Int Float"
      ==>! \case ConsistencyConditionUnsatisfied _ _ _ -> True; _ -> False
  it "improving inferred types with functional dependencies" $ do
    "val g = f A data A { con A } data B class F x y { val f : x -> y } instance F A B"
      ==> "val g : [(a : *)] a where F A a = f A data A { con A } data B class F (x : *) (y : *) { val f : [] x -> y } instance [] F A B"
    "val g = f A data A { con A } data B class F x y | x ~> y { val f : x -> y } instance F A B"
      ==> "val g : [] B = f A data A { con A } data B class F (x : *) (y : *) | x ~> y { val f : [] x -> y } instance [] F A B"
    "val g = f (f A) data A { con A } data B data C class F a b { val f : a -> b } instance F A B instance F B C"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val g = fun x -> f (f x) class F x y { val f : x -> y }"
      ==>! \case CannotResolveAmbiguity _ _ -> True; _ -> False
    "val g = f (f A) data A { con A } data B data C class F a b | a ~> b { val f : a -> b } instance F A B instance F B C"
      ==> "val g : [] C = f (f A) data A { con A } data B data C class F (a : *) (b : *) | a ~> b { val f : [] a -> b } instance [] F A B instance [] F B C"
    "val g = fun x -> f (f x) class F x y | x ~> y { val f : x -> y }"
      ==> "val g : [(a : *) (b : *) (c : *)] a -> b where (F a c, F c b) = fun x -> f (f x) class F (x : *) (y : *) | x ~> y { val f : [] x -> y }"
    "val g = fun a b c d -> f (f a d) (f b c) class F x y z | x y ~> z { val f : x -> y -> z }"
      ==> "val g : [(a : *) (b : *) (c : *) (d : *) (e : *) (f : *) (g : *)] a -> b -> c -> d -> e where (F a d f, F b c g, F f g e) = fun a b c d -> f (f a d) (f b c) class F (x : *) (y : *) (z : *) | x y ~> z { val f : [] x -> y -> z }"
    "val g = fun x -> Pair (f x) (f x) data Pair x y { con Pair x y } class F x y { val f : x -> y }"
      ==> "val g : [(a : *) (b : *) (c : *)] a -> Pair b c where (F a b, F a c) = fun x -> Pair (f x) (f x) data Pair (x : *) (y : *) { con Pair x y } class F (x : *) (y : *) { val f : [] x -> y }"
    "val g = fun x -> Pair (f x) (f x) data Pair x y { con Pair x y } class F x y | x ~> y { val f : x -> y }"
      ==> "val g : [(a : *) (b : *)] a -> Pair b b where F a b = fun x -> Pair (f x) (f x) data Pair (x : *) (y : *) { con Pair x y } class F (x : *) (y : *) | x ~> y { val f : [] x -> y }"
    "val g = f A data A { con A } data B class F a b { val f : a -> b } class G a b | a ~> b instance F a b where G a b instance G A B"
      ==> "val g : [] B = f A data A { con A } data B class F (a : *) (b : *) { val f : [] a -> b } class G (a : *) (b : *) | a ~> b instance [(a : *) (b : *)] F a b where G a b instance [] G A B"
    "val g = f class F x y { val f : x -> y } class G x y | x ~> y instance F x y where G x y"
      ==> "val g : [(a : *) (b : *)] a -> b where G a b = f class F (x : *) (y : *) { val f : [] x -> y } class G (x : *) (y : *) | x ~> y instance [(x : *) (y : *)] F x y where G x y"
    "val g : a -> b where G a b = f class F x y { val f : x -> y } class G x y | x ~> y instance F x y where G x y"
      ==> "val g : [(a : *) (b : *)] a -> b where G a b = f class F (x : *) (y : *) { val f : [] x -> y } class G (x : *) (y : *) | x ~> y instance [(x : *) (y : *)] F x y where G x y"
    "val g = fun x y -> Pair (f x y) (f x y) data A { con A } data Pair x y { con Pair x y } class F x y z { val f : z -> x -> y } class G x y | x ~> y instance F x y A where G x y"
      ==> "val g : [(a : *) (b : *) (c : *) (d : *)] a -> b -> Pair c d where (F b c a, F b d a) = fun x y -> Pair (f x y) (f x y) data A { con A } data Pair (x : *) (y : *) { con Pair x y } class F (x : *) (y : *) (z : *) { val f : [] z -> x -> y } class G (x : *) (y : *) | x ~> y instance [(x : *) (y : *)] F x y A where G x y"
    "val g = fun x y -> Pair (f x y) (f x y) val h = g A data A { con A } data Pair x y { con Pair x y } class F x y z { val f : z -> x -> y } class G x y | x ~> y instance F x y A where G x y"
      ==> "val g : [(a : *) (b : *) (c : *) (d : *)] a -> b -> Pair c d where (F b c a, F b d a) = fun x y -> Pair (f x y) (f x y) val h : [(e : *) (f : *)] e -> Pair f f where G e f = g A data A { con A } data Pair (x : *) (y : *) { con Pair x y } class F (x : *) (y : *) (z : *) { val f : [] z -> x -> y } class G (x : *) (y : *) | x ~> y instance [(x : *) (y : *)] F x y A where G x y"
    "val g = Pair (f A) (f A) data A { con A } data Pair x y { con Pair x y } class F x y { val f : x -> y }"
      ==> "val g : [(a : *) (b : *)] Pair a b where (F A a, F A b) = Pair (f A) (f A) data A { con A } data Pair (x : *) (y : *) { con Pair x y } class F (x : *) (y : *) { val f : [] x -> y }"
    "val g = Pair (f A) (f A) data A { con A } data Pair x y { con Pair x y } class F x y | x ~> y { val f : x -> y }"
      ==> "val g : [(a : *)] Pair a a where F A a = Pair (f A) (f A) data A { con A } data Pair (x : *) (y : *) { con Pair x y } class F (x : *) (y : *) | x ~> y { val f : [] x -> y }"
