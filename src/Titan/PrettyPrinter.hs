module Titan.PrettyPrinter
  ( Pretty(..)
  , PrettyFundeps(..)
  , PrettyContext(..)
  , PrettyQuantification(..)
  ) where

import Titan.Prelude
import Titan.TT

class Pretty a where
  {-# MINIMAL pprintsPrec | pprint #-}
  pprintsPrec :: Int -> a -> ShowS
  pprintsPrec _ x s = pprint x ++ s
  pprint :: a -> String
  pprint x = pprints x ""

pprints :: Pretty a => a -> ShowS
pprints = pprintsPrec 0

instance Pretty (Id a) where
  pprint id = id^.name

instance Pretty Kind where
  pprintsPrec prec = \case
    KVar s -> raw "_" . pprintsPrec prec s
    KType -> raw "*"
    KConstraint -> raw "?"
    KFun a b -> paren (0 < prec) (pprintsPrec 1 a . raw " -> " . pprintsPrec 0 b)

instance Pretty Type where
  pprintsPrec prec = \case
    TVar s _ _ -> raw "_" . pprintsPrec prec s
    TCon s -> pprintsPrec prec s
    TFun a b -> paren (0 < prec) (pprintsPrec 1 a . raw " -> " . pprintsPrec 0 b)
    TApp a b -> paren (9 < prec) (pprintsPrec 9 a . raw " " . pprintsPrec 10 b)
    TGen s -> pprintsPrec prec s

instance Pretty TypeCon where
  pprintsPrec prec = \case
    TypeConData s -> pprintsPrec prec s
    TypeConArrow -> raw "(->)"

instance Pretty Parameter where
  pprintsPrec prec parameter = case parameter^.kind of
    Typed _ k -> paren (9 < prec) $ pprints (parameter^.ident) . raw " : " . pprints k
    _ -> pprints (parameter^.ident)

instance Pretty (Fundep a) where
  pprintsPrec _ (as :~> bs) = p as . raw " ~> " . p bs
   where
    p [] = id
    p (x:xs) = cat " " 0 x 0 xs

newtype PrettyFundeps a = PrettyFundeps [Fundep a]

instance Pretty (PrettyFundeps a) where
  pprintsPrec _ (PrettyFundeps fundeps) = case fundeps of
    [] -> id
    d:ds -> raw " | " . cat ", " 0 d 0 ds

instance Pretty Constraint where
  pprintsPrec prec = \case
    CClass s ts -> paren (9 < prec) (cat " " 0 s 10 ts)

instance Pretty Scheme where
  pprintsPrec _ scheme =
    (pprints . PrettyQuantification) (scheme^.quantification) .
    pprints (scheme^.body) .
    (pprints . PrettyContext) (scheme^.context)

newtype PrettyQuantification = PrettyQuantification (Typing [Parameter])

instance Pretty PrettyQuantification where
  pprintsPrec _ = \case
    PrettyQuantification (Typed _ []) -> raw "[] "
    PrettyQuantification (Typed _ (p:ps)) -> raw "[" . cat " " 10 p 10 ps . raw "] "
    _ -> id

newtype PrettyContext = PrettyContext [Constraint]

instance Pretty PrettyContext where
  pprintsPrec _ (PrettyContext cs) = case cs of
    [] -> id
    [c] -> raw " where " . pprints c
    c:cs -> raw " where (" . cat ", " 0 c 0 cs . raw ")"

instance Pretty Literal where
  pprint = \case
    LInteger i -> show i
    LChar c -> show c
    LFloat d -> show d
    LString s -> show s

instance Pretty Pattern where
  pprintsPrec prec = \case
    PVar d p -> pprintsPrec prec d . maybe id (\p -> raw "@" . pprintsPrec 10 p) p
    PWildcard -> raw "_"
    PDecon s [] -> pprintsPrec prec s
    PDecon s ts -> paren (9 < prec) (cat " " 9 s 10 ts)
    PLit l -> pprintsPrec prec l

instance Pretty PatternDef where
  pprintsPrec prec def = pprintsPrec prec (def^.ident)

instance Pretty Expr where
  pprintsPrec prec = \case
    EVar s -> pprintsPrec prec s
    ECon s -> pprintsPrec prec s
    EApp a b -> paren (9 < prec) (pprintsPrec 9 a . raw " " . pprintsPrec 10 b)
    ELit l -> pprintsPrec prec l
    ELet (bind :| binds) e -> paren (1 < prec) $
      raw "let " .
      cat ", " 0 bind 0 binds .
      raw " in " .
      pprintsPrec (if 1 < prec then 0 else prec) e
    ELam (alt :| alts) -> paren (0 < prec) $
      raw "fun " .
      cat " | " 1 alt 1 alts

instance Pretty LocalDef where
  pprintsPrec _ def =
    pprints (def^.ident) .
    maybe id (\s -> raw " : " . pprints s) (def^?scheme.typed) .
    maybe id (\e -> raw " = " . pprints e) (def^.body)

instance Pretty Alt where
  pprintsPrec prec ((p :| ps) :-> body) =
    cat " " 10 p 10 ps . raw " -> " . pprintsPrec prec body

instance Pretty Value where
  pprintsPrec _ = \case
    VVar id -> pprints id
    VDef id -> pprints id
    VLocalDef id -> pprints id
    VClassMethod id -> pprints id
    VPatternDef id -> pprints id

instance Pretty ValueCon where
  pprint = \case
    ValueConData s -> pprint s

instance Pretty Def where
  pprintsPrec _ def =
    raw "val " .
    pprints (def^.ident) .
    maybe id (\s -> raw " : " . pprints s) (def^?scheme.typed) .
    maybe id (\e -> raw " = " . pprints e) (def^.body)

instance Pretty DataTypeCon where
  pprintsPrec _ con =
    raw "data " . cat " " 0 (con^.ident) 10 (con^.parameters)

instance Pretty DataValueCon where
  pprintsPrec _ con =
    raw "con " . cat " " 0 (con^.ident) 10 (con^.fields)

instance Pretty ClassCon where
  pprintsPrec _ cls =
    raw "class " . cat " " 0 (cls^.ident) 10 (cls^.parameters) .
    (pprints . PrettyFundeps) (cls^.fundeps) .
    (pprints . PrettyContext) (cls^.superclasses)

instance Pretty ClassMethod where
  pprintsPrec _ method =
    raw "val " .
    pprints (method^.ident) .
    (\s -> raw " : " . pprints s) (method^.scheme) .
    maybe id (\e -> raw " = " . pprints e) (method^.defaultBody)

instance Pretty Instance where
  pprintsPrec _ inst =
    raw "instance " .
    (pprints . PrettyQuantification) (inst^.quantification) .
    cat " " 0 (inst^.cls) 10 (inst^.arguments) .
    (pprints . PrettyContext) (inst^.context)

instance Pretty Default where
  pprintsPrec _ d =
    raw "default" .
    items (d^.candidates)

instance Pretty DumpType where
  pprintsPrec _ = \case
    DumpEverything -> id
    DumpTypeSignature -> raw "(type)"
    DumpKindSignature -> raw "(kind)"

instance Pretty Decl where
  pprintsPrec _ = \case
    DDef d -> pprints d
    DData c cs -> pprints c . items cs
    DClass c vs -> pprints c . items vs
    DInstance c -> pprints c
    DDefault d -> pprints d
    DDump dt d -> raw "dump" . pprints dt . raw " " . pprints d

instance Pretty Program where
  pprintsPrec _ program = case program^.decls of
    [] -> raw ""
    decl:decls -> cat " " 0 decl 0 decls

cat :: (Pretty a, Pretty b) => String -> Int -> a -> Int -> [b] -> ShowS
cat sep precx x precxs xs =
  foldr1 (\a b -> a . raw sep . b) (pprintsPrec precx x : map (pprintsPrec precxs) xs)

raw :: String -> ShowS
raw = showString

paren :: Bool -> ShowS -> ShowS
paren = showParen

items :: Pretty a => [a] -> ShowS
items = \case
  [] -> id
  item:items -> raw " { " . cat " " 0 item 0 items . raw " }"
