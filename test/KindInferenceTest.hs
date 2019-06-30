module KindInferenceTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude

test :: String -> Either Error String
test code = fmap (pprint . program) (parse "test" code >>= bind emptyGlobal >>= resolve >>= ki)

(==>) :: HasCallStack => String -> String -> Expectation
code ==> result = forM_ [code, result] $ \code -> test code `shouldBe` Right result

(==>!) :: HasCallStack => String -> (Error -> Bool) -> Expectation
code ==>! f = test code `shouldSatisfy` \case Left e -> f e; _ -> False

spec :: Spec
spec = describe "Titan.KindInference" $ do
  it "data types" $ do
    ""
      ==> ""
    "data Foo"
      ==> "data Foo"
    "data Foo a"
      ==> "data Foo (a : *)"
    "data Foo a b"
      ==> "data Foo (a : *) (b : *)"
    "data Foo a { con Foo a }"
      ==> "data Foo (a : *) { con Foo a }"
    "data Foo (a : *) { con Foo a }"
      ==> "data Foo (a : *) { con Foo a }"
    "data Foo (a : * -> *)"
      ==> "data Foo (a : * -> *)"
    "data Foo (a : * -> *) { con Foo a }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "data Foo (a : # *)"
      ==> "data Foo (a : # *)"
    "data Foo (a : # *) { con Foo a }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "data Foo a b { con Foo (a -> b) }"
      ==> "data Foo (a : *) (b : *) { con Foo (a -> b) }"
    "data Foo m (a : *) { con Foo (m a) }"
      ==> "data Foo (m : * -> *) (a : *) { con Foo (m a) }"
    "data Foo (m : * -> *) a { con Foo (m a) }"
      ==> "data Foo (m : * -> *) (a : *) { con Foo (m a) }"
    "data Foo a { con Foo { a } }"
      ==> "data Foo (a : # *) { con Foo { a } }"
    "data Foo { con Foo <> }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "data Foo a { con Foo <hello : {} | a> }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "data Foo a { con Foo { hello : {} | a } }"
      ==> "data Foo (a : # *) { con Foo { hello : {} | a } }"
    "data Foo a b { con Foo { hello : b | a } }"
      ==> "data Foo (a : # *) (b : *) { con Foo { hello : b | a } }"
    "data Foo a b { con Foo { hello : b | a } { b } }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "data Foo a b { con Foo { hello : b | a } { a } }"
      ==> "data Foo (a : # *) (b : *) { con Foo { hello : b | a } { a } }"
    "data Foo m a { con Foo { m a } }"
      ==> "data Foo (m : * -> # *) (a : *) { con Foo { m a } }"
    "data Foo (m : (* -> *) -> *) a { con Foo (m a) }"
      ==> "data Foo (m : (* -> *) -> *) (a : * -> *) { con Foo (m a) }"
    "data Foo m a { con Foo (m a) }"
      ==> "data Foo (m : * -> *) (a : *) { con Foo (m a) }"
    "data Foo m (a : * -> *) { con Foo (m a) }"
      ==> "data Foo (m : (* -> *) -> *) (a : * -> *) { con Foo (m a) }"
    "data Foo m { con Foo (m m) }"
      ==>! \case CannotUnifyKind _ _ OccursCheckFailed -> True; _ -> False
    "data Foo f a b { con A (f a) con B (a b) }"
      ==> "data Foo (f : (* -> *) -> *) (a : * -> *) (b : *) { con A (f a) con B (a b) }"
    "data A data B a { con B (a A) }"
      ==> "data A data B (a : * -> *) { con B (a A) }"
    "data A a data B a { con B (a A) }"
      ==> "data A (a : *) data B (a : (* -> *) -> *) { con B (a A) }"
    "data A a data B a data C { con C (A B) }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "data A (a : * -> *) data B a data C { con C (A B) }"
      ==> "data A (a : * -> *) data B (a : *) data C { con C (A B) }"
    "data List a { con Cons a (List a) }"
      ==> "data List (a : *) { con Cons a (List a) }"
    "data Free f a { con Free (f (Free f a)) }"
      ==> "data Free (f : * -> *) (a : *) { con Free (f (Free f a)) }"
    "data A a { con A (B a) } data B a { con B (a (A a)) }"
      ==> "data A (a : * -> *) { con A (B a) } data B (a : * -> *) { con B (a (A a)) }"
  it "classes" $ do
    "class Foo"
      ==> "class Foo"
    "class Foo a"
      ==> "class Foo (a : *)"
    "class Foo a b"
      ==> "class Foo (a : *) (b : *)"
    "class Foo a { val foo : a -> a }"
      ==> "class Foo (a : *) { val foo : [] a -> a }"
    "class Foo a { val foo : a -> b }"
      ==> "class Foo (a : *) { val foo : [(b : *)] a -> b }"
    "class Foo a { val foo : a b }"
      ==> "class Foo (a : * -> *) { val foo : [(b : *)] a b }"
    "class Foo a { val foo : b a }"
      ==> "class Foo (a : *) { val foo : [(b : * -> *)] b a }"
    "class Foo a { val f : b a val g : a b }"
      ==> "class Foo (a : * -> *) { val f : [(b : (* -> *) -> *)] b a val g : [(b : *)] a b }"
    "class Foo a b { val f : c (b a) }"
      ==> "class Foo (a : *) (b : * -> *) { val f : [(c : * -> *)] c (b a) }"
    "class F a where G a class G a"
      ==> "class F (a : *) where G a class G (a : *)"
    "class F a where G a class G (a : * -> *)"
      ==> "class F (a : * -> *) where G a class G (a : * -> *)"
    "class F (a : * -> *) where G a class G a"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "class F (a : * -> *) where G a class G a { val f : m a }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "class F a where G a class G a { val f : a b }"
      ==> "class F (a : * -> *) where G a class G (a : * -> *) { val f : [(b : *)] a b }"
    -- F depends on G but G does not; b is defaulted to * and then inferring F fails
    "class F a { val f : b a where G b } class G b { val g : m b }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "class F a { val f : b a where G b } class G b { val g : m b a where F a }"
      ==> "class F (a : *) { val f : [(b : * -> *)] b a where G b } class G (b : * -> *) { val g : [(m : (* -> *) -> * -> *) (a : *)] m b a where F a }"
    "class F class G a where F a"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
  it "defs, class methods, instances and defaults" $ do
    "val foo = 123"
      ==> "val foo = 123"
    "val foo : a -> b"
      ==> "val foo : [(a : *) (b : *)] a -> b"
    "val foo : T a -> b data T a"
      ==> "val foo : [(a : *) (b : *)] T a -> b data T (a : *)"
    "val foo = let x : a b in x"
      ==> "val foo = let x : [(a : * -> *) (b : *)] a b in x"
    "val foo : [m a] m a = let bar : [f] a f in bar"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "val foo : m a = let bar : a f in bar"
      ==> "val foo : [(m : * -> *) (a : *)] m a = let bar : [(a : * -> *) (f : *)] a f in bar"
    "val foo : a = let bar : b = let baz : c in baz in bar"
      ==> "val foo : [(a : *)] a = let bar : [(b : *)] b = let baz : [(c : *)] c in baz in bar"
    "val foo : [a m] m a = let bar : [a f] a f in bar"
      ==> "val foo : [(a : *) (m : * -> *)] m a = let bar : [(a : * -> *) (f : *)] a f in bar"
    "class F a { val f : x = let g : a b in g }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "class F a { val f : x = let g : b a in g }"
      ==> "class F (a : *) { val f : [(x : *)] x = let g : [(b : * -> *)] b a in g }"
    "class F instance F"
      ==> "class F instance [] F"
    "class F a instance F"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "class F a instance F a"
      ==> "class F (a : *) instance [(a : *)] F a"
    "class F a { val f : a b } instance F a"
      ==> "class F (a : * -> *) { val f : [(b : *)] a b } instance [(a : * -> *)] F a"
    "class F a class G (a : * -> *) class H a b instance H a b where (F a, G b)"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "data T a class F a instance F T"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
    "class F a class G (a : * -> *) class H a (b : * -> *) instance H a b where (F a, G b)"
      ==> "class F (a : *) class G (a : * -> *) class H (a : *) (b : * -> *) instance [(a : *) (b : * -> *)] H a b where (F a, G b)"
    "data T default { T }"
      ==> "data T default { T }"
    "data T a default { T }"
      ==> "data T (a : *) default { T }"
    "data S a data T default { (S T) }"
      ==> "data S (a : *) data T default { S T }"
    "data S a data T default { (S T T) }"
      ==>! \case CannotUnifyKind _ _ Mismatch -> True; _ -> False
