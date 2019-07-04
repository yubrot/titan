{-# LANGUAGE OverloadedLists #-}
module ParserTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude

test :: forall a. Parse a => Text -> Either Error a
test = parse "test"

spec :: Spec
spec = describe "Titan.Parser" $ do
  it "Lexer" $ do
    test ""
      `shouldBe` Right (Program [])
    test "  "
      `shouldBe` Right (Program [])
    test "  /* comment \n comment */  "
      `shouldBe` Right (Program [])
    test "  // hello \n // world \n  "
      `shouldBe` Right (Program [])
  it "Kind" $ do
    test @Kind "a"
      `shouldSatisfy` isLeft
    test @Kind "*"
      `shouldBe` Right KType
    test @Kind "?"
      `shouldBe` Right KConstraint
    test @Kind "* -> *"
      `shouldBe` Right (KType :--> KType)
    test @Kind "* -> (* -> *) -> *"
      `shouldBe` Right (KType :--> (KType :--> KType) :--> KType)
    test @Kind "# *"
      `shouldBe` Right (KRow KType)
    test @Kind "# * -> # * -> *"
      `shouldBe` Right (KRow KType :--> KRow KType :--> KType)
    test @Kind "# (* -> *)"
      `shouldBe` Right (KRow (KType :--> KType))
  it "Type" $ do
    test @Type "a"
      `shouldBe` Right (var "a")
    test @Type "val"
      `shouldSatisfy` isLeft
    test @Type "Pair a b"
      `shouldBe` Right (con "Pair" [var "a", var "b"])
    test @Type "(->)"
      `shouldBe` Right (TCon TypeConArrow)
    test @Type "{_}"
      `shouldBe` Right (TCon TypeConRecord)
    test @Type "<>"
      `shouldBe` Right TEmptyRow
    test @Type "<+name>"
      `shouldBe` Right (TCon (TypeConRowExtend (LName "name")))
    test @Type "a -> b -> a"
      `shouldBe` Right (var "a" :--> var "b" :--> var "a")
    test @Type "a -> Maybe a"
      `shouldBe` Right (var "a" :--> con "Maybe" [var "a"])
    test @Type "Maybe (a -> b)"
      `shouldBe` Right (con "Maybe" [var "a" :--> var "b"])
    test @Type "a (b c) d"
      `shouldBe` Right (var "a" :@@ (var "b" :@@ var "c") :@@ var "d")
    test @Type "<name : a>"
      `shouldBe` Right (TRowExtend (LName "name") (var "a") TEmptyRow)
    test @Type "<name : a | b>"
      `shouldBe` Right (TRowExtend (LName "name") (var "a") (var "b"))
    test @Type "<x : Int, y : Int>"
      `shouldBe` Right (TRowExtend (LName "x") (con "Int" []) (TRowExtend (LName "y") (con "Int" []) TEmptyRow))
    test @Type "<x : Int, y : Int | a>"
      `shouldBe` Right (TRowExtend (LName "x") (con "Int" []) (TRowExtend (LName "y") (con "Int" []) (var "a")))
    test @Type "Eff <name : a>"
      `shouldBe` Right (con "Eff" [TRowExtend (LName "name") (var "a") TEmptyRow])
    test @Type "{ a }"
      `shouldBe` Right (TRecord (var "a"))
    test @Type "{}"
      `shouldBe` Right (TRecord TEmptyRow)
    test @Type "{ name : a }"
      `shouldBe` Right (TRecord (TRowExtend (LName "name") (var "a") TEmptyRow))
    test @Type "{ name : a | b }"
      `shouldBe` Right (TRecord (TRowExtend (LName "name") (var "a") (var "b")))
    test @Type "{ x : Int, y : Int }"
      `shouldBe` Right (TRecord (TRowExtend (LName "x") (con "Int" []) (TRowExtend (LName "y") (con "Int" []) TEmptyRow)))
    test @Type "{ x : Int, y : Int | a }"
      `shouldBe` Right (TRecord (TRowExtend (LName "x") (con "Int" []) (TRowExtend (LName "y") (con "Int" []) (var "a"))))
    test @Type "IO { name : String }"
      `shouldBe` Right (con "IO" [TRecord (TRowExtend (LName "name") (con "String" []) TEmptyRow)])
    test @Type "{ 0: Int, 1: Bool }"
      `shouldBe` Right (TupleCreate [con "Int" [], con "Bool" []])
    test @Type "()"
      `shouldBe` Right (TupleCreate [])
    test @Type "(a, b, c)"
      `shouldBe` Right (TupleCreate [var "a", var "b", var "c"])
  it "Parameter" $ do
    test @Parameter "a"
      `shouldBe` Right (var "a")
    test @Parameter "(a : * -> *)"
      `shouldBe` Right (Parameter (Id "a") (Typed Explicit $ KType :--> KType))
  it "Constraint" $ do
    test @Constraint "Partial"
      `shouldBe` Right (con "Partial" [])
    test @Constraint "Num a"
      `shouldBe` Right (con "Num" [var "a"])
    test @Constraint "Coercible a b"
      `shouldBe` Right (con "Coercible" [var "a", var "b"])
    test @Constraint "Eq (List a)"
      `shouldBe` Right (con "Eq" [con "List" [var "a"]])
  it "Scheme" $ do
    test "a"
      `shouldBe` Right (Scheme Untyped (var "a") [])
    test "[] a"
      `shouldBe` Right (Scheme (Typed Explicit []) (var "a") [])
    test "[a] a"
      `shouldBe` Right (Scheme (Typed Explicit [var "a"]) (var "a") [])
    test "[a b] Pair a b"
      `shouldBe` Right (Scheme (Typed Explicit [var "a", var "b"]) (con "Pair" [var "a", var "b"]) [])
    test "a where ()"
      `shouldBe` Right (Scheme Untyped (var "a") [])
    test "a where Eq a"
      `shouldBe` Right (Scheme Untyped (var "a") [con "Eq" [var "a"]])
    test "a where (Eq a, Show a)"
      `shouldBe` Right (Scheme Untyped (var "a") [con "Eq" [var "a"], con "Show" [var "a"]])
    test "[a] a where Show a"
      `shouldBe` Right (Scheme (Typed Explicit [var "a"]) (var "a") [con "Show" [var "a"]])
  it "Literal" $ do
    test "123"
      `shouldBe` Right (LInteger 123)
    test "3.14"
      `shouldBe` Right (LFloat 3.14)
    test "-123"
      `shouldBe` Right (LInteger (-123))
    test "-3.14"
      `shouldBe` Right (LFloat (-3.14))
    test "'q'"
      `shouldBe` Right (LChar 'q')
    test "'\n'"
      `shouldBe` Right (LChar '\n')
    test "\"Hello, World!\""
      `shouldBe` Right (LString "Hello, World!")
  it "Pattern" $ do
    test @Pattern "x"
      `shouldBe` Right (var "x")
    test @Pattern "Nil"
      `shouldBe` Right (con "Nil" [])
    test @Pattern "_"
      `shouldBe` Right PWildcard
    test @Pattern "Cons x xs"
      `shouldBe` Right (con "Cons" [var "x", var "xs"])
    test @Pattern "Cons x (Cons x xs)"
      `shouldBe` Right (con "Cons" [var "x", con "Cons" [var "x", var "xs"]])
    test @Pattern "Cons Nil Nil"
      `shouldBe` Right (con "Cons" [con "Nil" [], con "Nil" []])
    test @Pattern "123"
      `shouldBe` Right (PLit (LInteger 123))
    test @Pattern "xss@(Cons x xs)"
      `shouldBe` Right (PVar (PatternDef (Id "xss")) (Just $ con "Cons" [var "x", var "xs"]))
  it "Expr" $ do
    test @Expr "x"
      `shouldBe` Right (var "x")
    test @Expr "Cons"
      `shouldBe` Right (con "Cons" [])
    test @Expr "{}"
      `shouldBe` Right (ECon ValueConEmptyRecord)
    test @Expr "{.foo}"
      `shouldBe` Right (ECon (ValueConRecordSelect (LName "foo")))
    test @Expr "{-foo}"
      `shouldBe` Right (ECon (ValueConRecordRestrict (LName "foo")))
    test @Expr "{+foo}"
      `shouldBe` Right (ECon (ValueConRecordExtend (LName "foo")))
    test @Expr "{%foo}"
      `shouldBe` Right (ECon (ValueConRecordUpdate (LName "foo")))
    test @Expr "Cons x xs"
      `shouldBe` Right (con "Cons" [var "x", var "xs"])
    test @Expr "123"
      `shouldBe` Right (ELit (LInteger 123))
    test @Expr "x.y"
      `shouldBe` Right (ERecordSelect (LName "y") (var "x"))
    test @Expr "x.y.z"
      `shouldBe` Right (ERecordSelect (LName "z") (ERecordSelect (LName "y") (var "x")))
    test @Expr "f (a b).c d"
      `shouldBe` Right (var "f" :@@ ERecordSelect (LName "c") (var "a" :@@ var "b") :@@ var "d")
    test @Expr "{ x = y }"
      `shouldBe` Right (RecordCreate [(LName "x", var "y")])
    test @Expr "{ x = y, a = b }"
      `shouldBe` Right (RecordCreate [(LName "x", var "y"), (LName "a", var "b")])
    test @Expr "%{ x = y } z"
      `shouldBe` Right (RecordUpdate [(LName "x", var "y")] (var "z"))
    test @Expr "%{ x = y, a = b } c"
      `shouldBe` Right (RecordUpdate [(LName "x", var "y"), (LName "a", var "b")] (var "c"))
    test @Expr "%{ x = y } { a = b }"
      `shouldBe` Right (RecordUpdate [(LName "x", var "y")] (RecordCreate [(LName "a", var "b")]))
    test @Expr "f (a b) c"
      `shouldBe` Right (var "f" :@@ (var "a" :@@ var "b") :@@ var "c")
    test @Expr "{ 0 = a, 1 = b }"
      `shouldBe` Right (TupleCreate [var "a", var "b"])
    test @Expr "()"
      `shouldBe` Right (TupleCreate [])
    test @Expr "('a', 'b', 'c')"
      `shouldBe` Right (TupleCreate [ELit (LChar 'a'), ELit (LChar 'b'), ELit (LChar 'c')])
    let a =: e = LocalDef (Id a) Untyped (Just e)
    test @Expr "let x = y in z"
      `shouldBe` Right (ELet ["x" =: var "y"] (var "z"))
    test @Expr "let x = y z, a = b in c"
      `shouldBe` Right (ELet ["x" =: (var "y" :@@ var "z"), "a" =: var "b"] (var "c"))
    test @Expr "let x = let y = z in a in let b = c in d"
      `shouldBe` Right (ELet ["x" =: ELet ["y" =: var "z"] (var "a")] (ELet ["b" =: var "c"] (var "d")))
    test @Expr "let x : a in z"
      `shouldBe` Right (ELet [LocalDef (Id "x") (Typed Explicit $ Scheme Untyped (var "a") []) Nothing] (var "z"))
    test @Expr "let x : a = y in z"
      `shouldBe` Right (ELet [LocalDef (Id "x") (Typed Explicit $ Scheme Untyped (var "a") []) (Just $ var "y")] (var "z"))
    test @Expr "let x : [a] a in z"
      `shouldBe` Right (ELet [LocalDef (Id "x") (Typed Explicit $ Scheme (Typed Explicit [var "a"]) (var "a") []) Nothing] (var "z"))
    test @Expr "let x : [(a : *)] a where Show a in z"
      `shouldBe` Right (ELet [LocalDef (Id "x") (Typed Explicit $ Scheme (Typed Explicit [Parameter (Id "a") (Typed Explicit KType)]) (var "a") [con "Show" [var "a"]]) Nothing] (var "z"))
    test @Expr "fun a b -> a"
      `shouldBe` Right (ELam [[var "a", var "b"] :-> var "a"])
    test @Expr "fun (Cons x _) (Cons _ ys) -> ys"
      `shouldBe` Right (ELam [[con "Cons" [var "x", PWildcard], con "Cons" [PWildcard, var "ys"]] :-> var "ys"])
    test @Expr "fun | a -> (fun b -> c) | d -> fun e -> f"
      `shouldBe` Right (ELam [[var "a"] :-> ELam [[var "b"] :-> var "c"], [var "d"] :-> ELam [[var "e"] :-> var "f"]])
    test @Expr "fun x -> let y = z in a | b -> c"
      `shouldBe` Right (ELam [[var "x"] :-> ELet ["y" =: var "z"] (var "a"), [var "b"] :-> var "c"])
    test @Expr "let x = fun y -> z in fun a -> b"
      `shouldBe` Right (ELet ["x" =: ELam [[var "y"] :-> var "z"]] (ELam [[var "a"] :-> var "b"]))
    test @Expr "fun w -> let x = fun y -> z in (fun a -> b) | v -> c"
      `shouldBe` Right (ELam [[var "w"] :-> ELet ["x" =: ELam [[var "y"] :-> var "z"]] (ELam [[var "a"] :-> var "b"]), [var "v"] :-> var "c"])
  it "Decl" $ do
    test "val show : a -> String where Show a"
      `shouldBe` Right (DDef (Def (Id "show") (Typed Explicit $ Scheme Untyped (var "a" :--> con "String" []) [con "Show" [var "a"]]) Nothing))
    test "dump val show"
      `shouldBe` Right (DDump DumpEverything (DDef (Def (Id "show") Untyped Nothing)))
    test "data List a {\n  con Cons a (List a)\n  con Nil\n}"
      `shouldBe` Right (DData (DataTypeCon (Id "List") [var "a"]) [DataValueCon (Id "Cons") [var "a", con "List" [var "a"]], DataValueCon (Id "Nil") []])
    test "class Partial"
      `shouldBe` Right (DClass (ClassCon (Id "Partial") [] [] []) [])
    test "class Ord a where Eq a {\n  val compare : a -> a -> Ordering\n}"
      `shouldBe` Right (DClass (ClassCon (Id "Ord") [var "a"] [] [con "Eq" [var "a"]]) [ClassMethod (Id "compare") (Scheme Untyped (var "a" :--> var "a" :--> con "Ordering" []) []) Nothing])
    test "class Coerce a b | a ~> b"
      `shouldBe` Right (DClass (ClassCon (Id "Coerce") [var "a", var "b"] [[Id "a"] :~> [Id "b"]] []) [])
    test "instance Eq (Pair a b) where (Eq a, Eq b)"
      `shouldBe` Right (DInstance (Instance Untyped (Id "Eq") [con "Pair" [var "a", var "b"]] [con "Eq" [var "a"], con "Eq" [var "b"]]))
    test "instance [] Eq Int"
      `shouldBe` Right (DInstance (Instance (Typed Explicit []) (Id "Eq") [con "Int" []] []))
    test "default {\n  Maybe\n  Integer\n}"
      `shouldBe` Right (DDefault (Default [con "Maybe" [], con "Integer" []]))
