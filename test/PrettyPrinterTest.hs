{-# LANGUAGE OverloadedLists #-}
module PrettyPrinterTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude

test :: forall a. Pretty a => a -> String
test = pprint

spec :: Spec
spec = describe "Titan.PrettyPrinter" $ do
  it "Id" $ do
    test (Id "hello")
      `shouldBe` "hello"
  it "Kind" $ do
    test @Kind (KVar $ Id "a")
      `shouldBe` "_a"
    test @Kind KType
      `shouldBe` "*"
    test @Kind KConstraint
      `shouldBe` "?"
    test @Kind (KRow KType)
      `shouldBe` "# *"
    test @Kind (KType :--> KType)
      `shouldBe` "* -> *"
    test @Kind (KType :--> (KType :--> KType) :--> KType)
      `shouldBe` "* -> (* -> *) -> *"
    test @Kind (KType :--> KRow (KType :--> KRow KType))
      `shouldBe` "* -> # (* -> # *)"
  it "Type" $ do
    test @Type (TVar (Id "a") KType topLevel)
      `shouldBe` "_a"
    test @Type (con "Pair" [])
      `shouldBe` "Pair"
    test @Type (TCon TypeConArrow)
      `shouldBe` "(->)"
    test @Type (TCon TypeConRecord)
      `shouldBe` "{_}"
    test @Type TEmptyRow
      `shouldBe` "<>"
    test @Type (TCon (TypeConRowExtend "name"))
      `shouldBe` "<+name>"
    test @Type (con "Pair" [var "a", var "b"])
      `shouldBe` "Pair a b"
    test @Type (var "a" :--> var "b")
      `shouldBe` "a -> b"
    test @Type (var "a" :--> var "b" :--> var "c")
      `shouldBe` "a -> b -> c"
    test @Type (con "Maybe" [var "a"] :--> con "Maybe" [var "b"])
      `shouldBe` "Maybe a -> Maybe b"
    test @Type (con "Maybe" [var "a" :--> var "b"] :--> con "Maybe" [var "b"])
      `shouldBe` "Maybe (a -> b) -> Maybe b"
    test @Type (var "a")
      `shouldBe` "a"
    test @Type (TRowExtend "name" (var "a") TEmptyRow)
      `shouldBe` "<name : a>"
    test @Type (TRowExtend "name" (var "a") (var "b"))
      `shouldBe` "<name : a | b>"
    test @Type (TRowExtend "x" (con "Int" []) (TRowExtend "y" (con "Int" []) TEmptyRow))
      `shouldBe` "<x : Int, y : Int>"
    test @Type (TRowExtend "x" (con "Int" []) (TRowExtend "y" (con "Int" []) (var "a")))
      `shouldBe` "<x : Int, y : Int | a>"
    test @Type (con "Eff" [TRowExtend "name" (var "a") TEmptyRow])
      `shouldBe` "Eff <name : a>"
    test @Type (TRecord (var "a"))
      `shouldBe` "{ a }"
    test @Type (TRecord TEmptyRow)
      `shouldBe` "{}"
    test @Type (TRecord (TRowExtend "name" (var "a") TEmptyRow))
      `shouldBe` "{ name : a }"
    test @Type (TRecord (TRowExtend "name" (var "a") (var "b")))
      `shouldBe` "{ name : a | b }"
    test @Type (TRecord (TRowExtend "x" (con "Int" []) (TRowExtend "y" (con "Int" []) TEmptyRow)))
      `shouldBe` "{ x : Int, y : Int }"
    test @Type (TRecord (TRowExtend "x" (con "Int" []) (TRowExtend "y" (con "Int" []) (var "a"))))
      `shouldBe` "{ x : Int, y : Int | a }"
    test @Type (con "IO" [TRecord (TRowExtend "name" (con "String" []) TEmptyRow)])
      `shouldBe` "IO { name : String }"
    test @Type (con "IO" [TupleCreate [con "A" [], var "b"]])
      `shouldBe` "IO (A, b)"
  it "Parameter" $ do
    test @Parameter (var "a")
      `shouldBe` "a"
    test @Parameter (Parameter (Id "a") (Typed Explicit KType))
      `shouldBe` "a : *"
    test @Parameter (Parameter (Id "a") (Typed Inferred $ KType :--> KType))
      `shouldBe` "a : * -> *"
  it "Constraint" $ do
    test @Constraint (con "Partial" [])
      `shouldBe` "Partial"
    test @Constraint (con "Eq" [var "a"])
      `shouldBe` "Eq a"
    test @Constraint (con "Coercible" [var "a", con "Maybe" [var "b"]])
      `shouldBe` "Coercible a (Maybe b)"
  it "Scheme" $ do
    test (Scheme Untyped (var "a") [])
      `shouldBe` "a"
    test (Scheme Untyped (var "a") [con "Eq" [var "a"]])
      `shouldBe` "a where Eq a"
    test (Scheme Untyped (var "a" :--> var "b") [con "Eq" [var "a"], con "Show" [var "a"]])
      `shouldBe` "a -> b where (Eq a, Show a)"
    test (Scheme (Typed Explicit [var "a"]) (var "a" :--> var "a") [])
      `shouldBe` "[a] a -> a"
    test (Scheme (Typed Explicit [Parameter (Id "a") (Typed Inferred KType)]) (var "a" :--> var "a") [])
      `shouldBe` "[(a : *)] a -> a"
  it "Literal" $ do
    test (LInteger 123)
      `shouldBe` "123"
    test (LChar 'x')
      `shouldBe` "'x'"
    test (LFloat 3.14)
      `shouldBe` "3.14"
    test (LString "hello")
      `shouldBe` "\"hello\""
  it "Pattern" $ do
    test @Pattern (var "x")
      `shouldBe` "x"
    test @Pattern PWildcard
      `shouldBe` "_"
    test @Pattern (con "Nothing" [])
      `shouldBe` "Nothing"
    test @Pattern (con "Cons" [var "x", var "xs"])
      `shouldBe` "Cons x xs"
    test @Pattern (con "Cons" [var "x", con "Cons" [var "y", PWildcard]])
      `shouldBe` "Cons x (Cons y _)"
    test @Pattern (PVar (PatternDef (Id "xss")) (Just $ con "Cons" [var "x", var "xs"]))
      `shouldBe` "xss@(Cons x xs)"
    test @Pattern (PLit (LInteger 123))
      `shouldBe` "123"
  it "Expr" $ do
    test @Expr (var "x")
      `shouldBe` "x"
    test @Expr (con "Pair" [])
      `shouldBe` "Pair"
    test @Expr (ECon ValueConEmptyRecord)
      `shouldBe` "{}"
    test @Expr (ECon (ValueConRecordSelect "foo"))
      `shouldBe` "{.foo}"
    test @Expr (ECon (ValueConRecordRestrict "foo"))
      `shouldBe` "{-foo}"
    test @Expr (ECon (ValueConRecordExtend "foo"))
      `shouldBe` "{+foo}"
    test @Expr (ECon (ValueConRecordUpdate "foo"))
      `shouldBe` "{%foo}"
    test @Expr (var "f" :@@ var "a" :@@ var "b")
      `shouldBe` "f a b"
    test @Expr (con "Pair" [var "a", var "b"])
      `shouldBe` "Pair a b"
    test @Expr (ELit (LInteger 123))
      `shouldBe` "123"
    test @Expr (ERecordSelect "y" (var "x"))
      `shouldBe` "x.y"
    test @Expr (ERecordSelect "z" (ERecordSelect "y" (var "x")))
      `shouldBe` "x.y.z"
    test @Expr (var "f" :@@ ERecordSelect "c" (var "a" :@@ var "b") :@@ var "d")
      `shouldBe` "f (a b).c d"
    test @Expr (RecordCreate [("x", var "y")])
      `shouldBe` "{ x = y }"
    test @Expr (RecordCreate [("x", var "y"), ("a", var "b")])
      `shouldBe` "{ x = y, a = b }"
    test @Expr (RecordUpdate [("x", var "y")] (var "z"))
      `shouldBe` "%{ x = y } z"
    test @Expr (RecordUpdate [("x", var "y"), ("a", var "b")] (var "c"))
      `shouldBe` "%{ x = y, a = b } c"
    test @Expr (RecordUpdate [("x", var "y")] (RecordCreate [("a", var "b")]))
      `shouldBe` "%{ x = y } { a = b }"
    test @Expr (TupleCreate [])
      `shouldBe` "{}"
    test @Expr (TupleCreate [var "a", var "b"])
      `shouldBe` "(a, b)"
    test @Expr (ELet1 (LocalDef (Id "x") Untyped (Just $ var "a")) (var "z"))
      `shouldBe` "let x = a in z"
    test @Expr (ELet [LocalDef (Id "x") Untyped (Just $ var "a"), LocalDef (Id "y") Untyped (Just $ var "b")] (var "z"))
      `shouldBe` "let x = a, y = b in z"
    test @Expr (ELet1 (LocalDef (Id "x") Untyped (Just $ ELet1 (LocalDef (Id "y") Untyped (Just $ var "z")) (var "a"))) (ELet1 (LocalDef (Id "b") Untyped (Just $ var "c")) (var "d")))
      `shouldBe` "let x = let y = z in a in let b = c in d"
    test @Expr (ELet1 (LocalDef (Id "x") (Typed Explicit $ Scheme Untyped (var "a") []) (Just $ var "y")) (var "z"))
      `shouldBe` "let x : a = y in z"
    test @Expr (ELet1 (LocalDef (Id "x") (Typed Explicit $ Scheme Untyped (var "a") []) Nothing) (var "z"))
      `shouldBe` "let x : a in z"
    test @Expr (ELet1 (LocalDef (Id "x") Untyped (Just $ var "a")) (var "z") :@@ var "b")
      `shouldBe` "(let x = a in z) b"
    test @Expr (ELam1 ([var "a", var "b"] :-> var "a"))
      `shouldBe` "fun a b -> a"
    test @Expr (ELam1 ([con "Cons" [var "x", PWildcard], con "Cons" [PWildcard, var "ys"]] :-> var "ys"))
      `shouldBe` "fun (Cons x _) (Cons _ ys) -> ys"
    let lam1 p e = ELam1 ([var p] :-> e)
    let lam2 p1 e1 p2 e2 = ELam [[var p1] :-> e1, [var p2] :-> e2]
    let let1 n i e = ELet1 (LocalDef (Id n) Untyped (Just i)) e
    test @Expr (lam2 "a" (lam1 "b" (var "c")) "d" (lam1 "e" (var "f")))
      `shouldBe` "fun a -> (fun b -> c) | d -> (fun e -> f)" -- this should be "... d -> fun e -> f"
    test @Expr (lam2 "x" (let1 "y" (var "z") (var "a")) "b" (var "c"))
      `shouldBe` "fun x -> let y = z in a | b -> c"
    test @Expr (let1 "x" (lam1 "y" (var "z")) (lam1 "a" (var "b")))
      `shouldBe` "let x = fun y -> z in fun a -> b"
    test @Expr (lam2 "w" (let1 "x" (lam1 "y" (var "z")) (lam1 "a" (var "b"))) "v" (var "c"))
      `shouldBe` "fun w -> let x = fun y -> z in (fun a -> b) | v -> c"
    test @Expr (lam2 "w" (let1 "x" (lam1 "y" (var "z")) (lam1 "a" (var "b")) :@@ var "c") "v" (var "d"))
      `shouldBe` "fun w -> (let x = fun y -> z in fun a -> b) c | v -> d"
  it "Decl" $ do
    test (DDef (Def (Id "show") (Typed Explicit $ Scheme Untyped (var "a" :--> con "String" []) [con "Show" [var "a"]]) Nothing))
      `shouldBe` "val show : a -> String where Show a"
    test (DDef (Def (Id "Id") Untyped (Just $ ELam1 ([var "x"] :-> var "x"))))
      `shouldBe` "val Id = fun x -> x"
    test (DData (DataTypeCon (Id "List") [var "a"]) [])
      `shouldBe` "data List a"
    test (DDump DumpEverything (DData (DataTypeCon (Id "List") [var "a"]) []))
      `shouldBe` "dump data List a"
    test (DData (DataTypeCon (Id "Free") [Parameter (Id "f") (Typed Explicit $ KType :--> KType), Parameter (Id "a") Untyped]) [])
      `shouldBe` "data Free (f : * -> *) a"
    test (DData (DataTypeCon (Id "List") [var "a"]) [DataValueCon (Id "Cons") [var "a", con "List" [var "a"]], DataValueCon (Id "Nil") []])
      `shouldBe` "data List a { con Cons a (List a) con Nil }"
    test (DClass (ClassCon (Id "Eq") [var "a"] [] []) [])
      `shouldBe` "class Eq a"
    test (DClass (ClassCon (Id "Eq") [var "a"] [] []) [ClassMethod (Id "eq") (Scheme Untyped (var "a" :--> var "a" :--> con "Bool" []) []) Nothing])
      `shouldBe` "class Eq a { val eq : a -> a -> Bool }"
    test (DClass (ClassCon (Id "Coerce") [var "a", var "b"] [[Id "a"] :~> [Id "b"], [Id "b"] :~> [Id "a"]] []) [])
      `shouldBe` "class Coerce a b | a ~> b, b ~> a"
    test (DClass (ClassCon (Id "Ord") [var "a"] [] [con "Eq" [var "a"]]) [ClassMethod (Id "compare") (Scheme Untyped (var "a" :--> var "a" :--> con "Ordering" []) []) Nothing])
      `shouldBe` "class Ord a where Eq a { val compare : a -> a -> Ordering }"
    test (DInstance (Instance Untyped (Id "Eq") [con "Pair" [var "a", var "b"]] [con "Eq" [var "a"], con "Eq" [var "b"]]))
      `shouldBe` "instance Eq (Pair a b) where (Eq a, Eq b)"
    test (DInstance (Instance (Typed Explicit [var "a"]) (Id "Any") [var "a"] []))
      `shouldBe` "instance [a] Any a"
    test (DDefault (Default []))
      `shouldBe` "default"
    test (DDefault (Default [con "Maybe" [], con "Integer" []]))
      `shouldBe` "default { Maybe Integer }"
