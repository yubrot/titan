{-# LANGUAGE OverloadedLists #-}
module ParserTest
  ( spec
  ) where

import Test.Hspec
import Titan
import Titan.Prelude
import TestHelper

test :: forall a. Parse a => Text -> Either Error a
test = parse "test"

spec :: Spec
spec = describe "Titan.Parser" $ do
  it "Lexer" $ do
    test ""
      `shouldBeRight` Program []
    test "  "
      `shouldBeRight` Program []
    test "  /* comment \n comment */  "
      `shouldBeRight` Program []
    test "  // hello \n // world \n  "
      `shouldBeRight` Program []
  it "Kind" $ do
    test @Kind "a"
      `shouldSatisfy` isLeft
    test @Kind "*"
      `shouldBeRight` KType
    test @Kind "?"
      `shouldBeRight` KConstraint
    test @Kind "* -> *"
      `shouldBeRight` (KType :--> KType)
    test @Kind "* -> (* -> *) -> *"
      `shouldBeRight` (KType :--> (KType :--> KType) :--> KType)
    test @Kind "# *"
      `shouldBeRight` KRow KType
    test @Kind "# * -> # * -> *"
      `shouldBeRight` (KRow KType :--> KRow KType :--> KType)
    test @Kind "# (* -> *)"
      `shouldBeRight` KRow (KType :--> KType)
  it "Type" $ do
    test @Type "a"
      `shouldBeRight` var "a"
    test @Type "val"
      `shouldSatisfy` isLeft
    test @Type "Pair a b"
      `shouldBeRight` con "Pair" [var "a", var "b"]
    test @Type "(->)"
      `shouldBeRight` TCon TypeConArrow
    test @Type "{_}"
      `shouldBeRight` TCon TypeConRecord
    test @Type "<>"
      `shouldBeRight` TEmptyRow
    test @Type "<+name>"
      `shouldBeRight` TCon (TypeConRowExtend (LName "name"))
    test @Type "a -> b -> a"
      `shouldBeRight` (var "a" :--> var "b" :--> var "a")
    test @Type "a -> Maybe a"
      `shouldBeRight` (var "a" :--> con "Maybe" [var "a"])
    test @Type "Maybe (a -> b)"
      `shouldBeRight` con "Maybe" [var "a" :--> var "b"]
    test @Type "a (b c) d"
      `shouldBeRight` (var "a" :@@ (var "b" :@@ var "c") :@@ var "d")
    test @Type "<name : a>"
      `shouldBeRight` TRowExtend (LName "name") (var "a") TEmptyRow
    test @Type "<name : a | b>"
      `shouldBeRight` TRowExtend (LName "name") (var "a") (var "b")
    test @Type "<x : Int, y : Int>"
      `shouldBeRight` TRowExtend (LName "x") (con "Int" []) (TRowExtend (LName "y") (con "Int" []) TEmptyRow)
    test @Type "<x : Int, y : Int | a>"
      `shouldBeRight` TRowExtend (LName "x") (con "Int" []) (TRowExtend (LName "y") (con "Int" []) (var "a"))
    test @Type "Eff <name : a>"
      `shouldBeRight` con "Eff" [TRowExtend (LName "name") (var "a") TEmptyRow]
    test @Type "{ a }"
      `shouldBeRight` TRecord (var "a")
    test @Type "{}"
      `shouldBeRight` TRecord TEmptyRow
    test @Type "{ name : a }"
      `shouldBeRight` TRecord (TRowExtend (LName "name") (var "a") TEmptyRow)
    test @Type "{ name : a | b }"
      `shouldBeRight` TRecord (TRowExtend (LName "name") (var "a") (var "b"))
    test @Type "{ x : Int, y : Int }"
      `shouldBeRight` TRecord (TRowExtend (LName "x") (con "Int" []) (TRowExtend (LName "y") (con "Int" []) TEmptyRow))
    test @Type "{ x : Int, y : Int | a }"
      `shouldBeRight` TRecord (TRowExtend (LName "x") (con "Int" []) (TRowExtend (LName "y") (con "Int" []) (var "a")))
    test @Type "IO { name : String }"
      `shouldBeRight` con "IO" [TRecord (TRowExtend (LName "name") (con "String" []) TEmptyRow)]
    test @Type "{ 0: Int, 1: Bool }"
      `shouldBeRight` TupleCreate [con "Int" [], con "Bool" []]
    test @Type "()"
      `shouldBeRight` TupleCreate []
    test @Type "(a, b, c)"
      `shouldBeRight` TupleCreate [var "a", var "b", var "c"]
  it "Parameter" $ do
    test @Parameter "a"
      `shouldBeRight` var "a"
    test @Parameter "(a : * -> *)"
      `shouldBeRight` Parameter (Id "a") (Typed Explicit $ KType :--> KType)
  it "Constraint" $ do
    test @Constraint "Partial"
      `shouldBeRight` con "Partial" []
    test @Constraint "Num a"
      `shouldBeRight` con "Num" [var "a"]
    test @Constraint "Coercible a b"
      `shouldBeRight` con "Coercible" [var "a", var "b"]
    test @Constraint "Eq (List a)"
      `shouldBeRight` con "Eq" [con "List" [var "a"]]
  it "Scheme" $ do
    test "a"
      `shouldBeRight` Scheme Untyped (var "a") []
    test "[] a"
      `shouldBeRight` Scheme (Typed Explicit []) (var "a") []
    test "[a] a"
      `shouldBeRight` Scheme (Typed Explicit [var "a"]) (var "a") []
    test "[a b] Pair a b"
      `shouldBeRight` Scheme (Typed Explicit [var "a", var "b"]) (con "Pair" [var "a", var "b"]) []
    test "a where ()"
      `shouldBeRight` Scheme Untyped (var "a") []
    test "a where Eq a"
      `shouldBeRight` Scheme Untyped (var "a") [con "Eq" [var "a"]]
    test "a where (Eq a, Show a)"
      `shouldBeRight` Scheme Untyped (var "a") [con "Eq" [var "a"], con "Show" [var "a"]]
    test "[a] a where Show a"
      `shouldBeRight` Scheme (Typed Explicit [var "a"]) (var "a") [con "Show" [var "a"]]
  it "Literal" $ do
    test "123"
      `shouldBeRight` LInteger 123
    test "3.14"
      `shouldBeRight` LFloat 3.14
    test "-123"
      `shouldBeRight` LInteger (-123)
    test "-3.14"
      `shouldBeRight` LFloat (-3.14)
    test "'q'"
      `shouldBeRight` LChar 'q'
    test "'\n'"
      `shouldBeRight` LChar '\n'
    test "\"Hello, World!\""
      `shouldBeRight` LString "Hello, World!"
  it "Pattern" $ do
    test @Pattern "x"
      `shouldBeRight` var "x"
    test @Pattern "Nil"
      `shouldBeRight` con "Nil" []
    test @Pattern "_"
      `shouldBeRight` PWildcard
    test @Pattern "Cons x xs"
      `shouldBeRight` con "Cons" [var "x", var "xs"]
    test @Pattern "Cons x (Cons x xs)"
      `shouldBeRight` con "Cons" [var "x", con "Cons" [var "x", var "xs"]]
    test @Pattern "Cons Nil Nil"
      `shouldBeRight` con "Cons" [con "Nil" [], con "Nil" []]
    test @Pattern "123"
      `shouldBeRight` PLit (LInteger 123)
    test @Pattern "xss@(Cons x xs)"
      `shouldBeRight` PVar (PatternDef (Id "xss")) (Just $ con "Cons" [var "x", var "xs"])
  it "Expr" $ do
    test @Expr "x"
      `shouldBeRight` var "x"
    test @Expr "Cons"
      `shouldBeRight` con "Cons" []
    test @Expr "{}"
      `shouldBeRight` ECon ValueConEmptyRecord
    test @Expr "{.foo}"
      `shouldBeRight` ECon (ValueConRecordSelect (LName "foo"))
    test @Expr "{-foo}"
      `shouldBeRight` ECon (ValueConRecordRestrict (LName "foo"))
    test @Expr "{+foo}"
      `shouldBeRight` ECon (ValueConRecordExtend (LName "foo"))
    test @Expr "{%foo}"
      `shouldBeRight` ECon (ValueConRecordUpdate (LName "foo"))
    test @Expr "Cons x xs"
      `shouldBeRight` con "Cons" [var "x", var "xs"]
    test @Expr "123"
      `shouldBeRight` ELit (LInteger 123)
    test @Expr "x.y"
      `shouldBeRight` ERecordSelect (LName "y") (var "x")
    test @Expr "x.y.z"
      `shouldBeRight` ERecordSelect (LName "z") (ERecordSelect (LName "y") (var "x"))
    test @Expr "f (a b).c d"
      `shouldBeRight` (var "f" :@@ ERecordSelect (LName "c") (var "a" :@@ var "b") :@@ var "d")
    test @Expr "{ x = y }"
      `shouldBeRight` RecordCreate [(LName "x", var "y")]
    test @Expr "{ x = y, a = b }"
      `shouldBeRight` RecordCreate [(LName "x", var "y"), (LName "a", var "b")]
    test @Expr "%{ x = y } z"
      `shouldBeRight` RecordUpdate [(LName "x", var "y")] (var "z")
    test @Expr "%{ x = y, a = b } c"
      `shouldBeRight` RecordUpdate [(LName "x", var "y"), (LName "a", var "b")] (var "c")
    test @Expr "%{ x = y } { a = b }"
      `shouldBeRight` RecordUpdate [(LName "x", var "y")] (RecordCreate [(LName "a", var "b")])
    test @Expr "f (a b) c"
      `shouldBeRight` (var "f" :@@ (var "a" :@@ var "b") :@@ var "c")
    test @Expr "{ 0 = a, 1 = b }"
      `shouldBeRight` TupleCreate [var "a", var "b"]
    test @Expr "()"
      `shouldBeRight` TupleCreate []
    test @Expr "('a', 'b', 'c')"
      `shouldBeRight` TupleCreate [ELit (LChar 'a'), ELit (LChar 'b'), ELit (LChar 'c')]
    let a =: e = LocalDef (Id a) Untyped (Just e)
    test @Expr "let x = y in z"
      `shouldBeRight` ELet ["x" =: var "y"] (var "z")
    test @Expr "let x = y z, a = b in c"
      `shouldBeRight` ELet ["x" =: (var "y" :@@ var "z"), "a" =: var "b"] (var "c")
    test @Expr "let x = let y = z in a in let b = c in d"
      `shouldBeRight` ELet ["x" =: ELet ["y" =: var "z"] (var "a")] (ELet ["b" =: var "c"] (var "d"))
    test @Expr "let x : a in z"
      `shouldBeRight` ELet [LocalDef (Id "x") (Typed Explicit $ Scheme Untyped (var "a") []) Nothing] (var "z")
    test @Expr "let x : a = y in z"
      `shouldBeRight` ELet [LocalDef (Id "x") (Typed Explicit $ Scheme Untyped (var "a") []) (Just $ var "y")] (var "z")
    test @Expr "let x : [a] a in z"
      `shouldBeRight` ELet [LocalDef (Id "x") (Typed Explicit $ Scheme (Typed Explicit [var "a"]) (var "a") []) Nothing] (var "z")
    test @Expr "let x : [(a : *)] a where Show a in z"
      `shouldBeRight` ELet [LocalDef (Id "x") (Typed Explicit $ Scheme (Typed Explicit [Parameter (Id "a") (Typed Explicit KType)]) (var "a") [con "Show" [var "a"]]) Nothing] (var "z")
    test @Expr "fun a b -> a"
      `shouldBeRight` ELam [[var "a", var "b"] :-> var "a"]
    test @Expr "fun (Cons x _) (Cons _ ys) -> ys"
      `shouldBeRight` ELam [[con "Cons" [var "x", PWildcard], con "Cons" [PWildcard, var "ys"]] :-> var "ys"]
    test @Expr "fun a -> (fun b -> c) | d -> fun e -> f"
      `shouldBeRight` ELam [[var "a"] :-> ELam [[var "b"] :-> var "c"], [var "d"] :-> ELam [[var "e"] :-> var "f"]]
    test @Expr "fun x -> let y = z in a | b -> c"
      `shouldBeRight` ELam [[var "x"] :-> ELet ["y" =: var "z"] (var "a"), [var "b"] :-> var "c"]
    test @Expr "let x = fun y -> z in fun a -> b"
      `shouldBeRight` ELet ["x" =: ELam [[var "y"] :-> var "z"]] (ELam [[var "a"] :-> var "b"])
    test @Expr "fun w -> let x = fun y -> z in (fun a -> b) | v -> c"
      `shouldBeRight` ELam [[var "w"] :-> ELet ["x" =: ELam [[var "y"] :-> var "z"]] (ELam [[var "a"] :-> var "b"]), [var "v"] :-> var "c"]
  it "Decl" $ do
    test "val show : a -> String where Show a"
      `shouldBeRight` DDef (Def (Id "show") (Typed Explicit $ Scheme Untyped (var "a" :--> con "String" []) [con "Show" [var "a"]]) Nothing)
    test "dump val show"
      `shouldBeRight` DDump DumpEverything (DDef (Def (Id "show") Untyped Nothing))
    test "data List a {\n  con Cons a (List a)\n  con Nil\n}"
      `shouldBeRight` DData (DataTypeCon (Id "List") [var "a"]) [DataValueCon (Id "Cons") [var "a", con "List" [var "a"]], DataValueCon (Id "Nil") []]
    test "class Partial"
      `shouldBeRight` DClass (ClassCon (Id "Partial") [] [] []) []
    test "class Ord a where Eq a {\n  val compare : a -> a -> Ordering\n}"
      `shouldBeRight` DClass (ClassCon (Id "Ord") [var "a"] [] [con "Eq" [var "a"]]) [ClassMethod (Id "compare") (Scheme Untyped (var "a" :--> var "a" :--> con "Ordering" []) []) Nothing]
    test "class Coerce a b | a ~> b"
      `shouldBeRight` DClass (ClassCon (Id "Coerce") [var "a", var "b"] [[Id "a"] :~> [Id "b"]] []) []
    test "instance Eq (Pair a b) where (Eq a, Eq b)"
      `shouldBeRight` DInstance (Instance Untyped (Id "Eq") [con "Pair" [var "a", var "b"]] [con "Eq" [var "a"], con "Eq" [var "b"]])
    test "instance [] Eq Int"
      `shouldBeRight` DInstance (Instance (Typed Explicit []) (Id "Eq") [con "Int" []] [])
    test "default {\n  Maybe\n  Integer\n}"
      `shouldBeRight` DDefault (Default [con "Maybe" [], con "Integer" []])
