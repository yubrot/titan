module Titan.PrettyPrinter
  ( PrettyCode(..)
  , PrettySuffix(..)
  , PrettyPrefix(..)
  ) where

import Data.Text.Prettyprint.Doc hiding (parens, brackets, braces, angles)
import Titan.Prelude
import Titan.TT

class PrettyCode a where
  {-# MINIMAL prettyBlock | prettyInline #-}
  prettyBlock :: Int -> a -> Doc ann
  prettyBlock = prettyInline
  prettyInline :: Int -> a -> Doc ann
  prettyInline prec = group . prettyBlock prec

infixl 3 <++

class PrettySuffix a where
  (<++) :: Doc ann -> a -> Doc ann

infixr 4 ++>

class PrettyPrefix a where
  (++>) :: a -> Doc ann -> Doc ann

instance PrettySuffix a => PrettySuffix (Maybe a) where
  d <++ ma = maybe d (d <++) ma

instance PrettyPrefix a => PrettyPrefix (Maybe a) where
  ma ++> d = maybe d (++> d) ma

instance PrettyCode (Id a) where
  prettyBlock _ id = pretty (id^.name)

instance PrettyCode Kind where
  prettyBlock prec = \case
    KVar s -> "_" <> prettyInline prec s
    KType -> "*"
    KConstraint -> "?"
    KRow k -> parensIf (9 < prec) $ "#" <+> prettyInline 10 k
    KFun a b -> parensIf (0 < prec) $ prettyBlock 1 a <+> "->" <++> prettyBlock 0 b

instance PrettyCode Label where
  prettyBlock _ = \case
    LName n -> pretty n
    LIndex i -> pretty i

instance PrettyCode Type where
  prettyBlock prec = \case
    TVar s _ _ -> "_" <> prettyInline prec s
    TCon s -> prettyBlock prec s
    a :--> b -> parensIf (0 < prec) $ prettyBlock 1 a <+> "->" <++> prettyBlock 0 b
    TRecord TEmptyRow -> "{}"
    TupleCreate xs -> parens $ punctuate "," $ map (prettyBlock 0) xs
    TRecord (TRowExtend l a b) -> braces $ punctuateRow l a b
    TRecord s -> braces [prettyBlock 0 s]
    TRowExtend l a b -> angles $ punctuateRow l a b
    TApp a b -> parensIf (9 < prec) $ prettyInline 9 a <+> prettyInline 10 b
    TGen s -> prettyBlock prec s
   where
    punctuateRow l a b =
      let l' = prettyInline 0 l <+> ":" <+> prettyBlock 0 a in
      case b of
        TEmptyRow -> [l']
        TRowExtend l b c -> (l' <> ",") : punctuateRow l b c
        b -> [l' <> " |", prettyBlock 0 b]

instance PrettyCode TypeCon where
  prettyBlock prec = \case
    TypeConData s -> prettyBlock prec s
    TypeConArrow -> "(->)"
    TypeConRecord -> "{_}"
    TypeConEmptyRow -> "<>"
    TypeConRowExtend l -> "<+" <> prettyInline 0 l <> ">"

instance PrettyCode Parameter where
  prettyBlock prec parameter = case parameter^.kind of
    Typed _ k ->
      parensIf (9 < prec) $ nest 2 $
        prettyInline 0 (parameter^.ident) <++> ":" <+> align (prettyInline 0 k)
    _ ->
      prettyInline 0 (parameter^.ident)

instance PrettyCode (Fundep a) where
  prettyBlock _ (as :~> bs) = p as <+> "~>" <+> p bs
   where
    p = hsep . map (prettyInline 0)

instance PrettySuffix [Fundep a] where
  d <++ [] = d
  d <++ fds = group $ d <++> "|" <+> (align . sep . punctuate "," . map (prettyInline 0)) fds

instance PrettyCode Constraint where
  prettyBlock prec = \case
    CClass s [] -> prettyInline 9 s
    CClass s ts -> parensIf (9 < prec) $ hsep $ prettyInline 9 s : map (prettyInline 10) ts

instance PrettyPrefix [Parameter] where
  ps ++> d = group $ brackets (map (prettyInline 10) ps) <++> d

instance PrettySuffix [Constraint] where
  d <++ [] = d
  d <++ [c] = d <++> "where" <+> prettyInline 0 c
  d <++ cs = d <++> "where" <+> (parens . punctuate "," . map (prettyInline 0)) cs

instance PrettyCode Scheme where
  prettyBlock _ scheme =
    scheme^?quantification.typed ++> prettyInline 0 (scheme^.body) <++ scheme^.context

instance PrettySuffix Scheme where
  d <++ s = d <++> ":" <+> align (prettyInline 0 s)

instance PrettyCode Literal where
  prettyBlock _ = \case
    LInteger i -> pretty i
    LChar c -> viaShow c
    LFloat d -> pretty d
    LString s -> viaShow s

instance PrettyCode Pattern where
  prettyBlock prec = \case
    PVar d p -> prettyInline prec d <> maybe mempty (\p -> "@" <> prettyBlock 10 p) p
    PWildcard -> "_"
    PDecon s [] -> prettyInline 9 s
    PDecon s ts -> parensIf (9 < prec) $ hsep $ prettyInline 9 s : map (prettyInline 10) ts
    PLit l -> prettyBlock prec l

instance PrettyCode PatternDef where
  prettyBlock prec def = prettyBlock prec (def^.ident)

instance PrettyCode Expr where
  prettyBlock prec = \case
    EVar s -> prettyBlock prec s
    ECon s -> prettyBlock prec s
    ERecordSelect l a -> prettyBlock 10 a <> "." <> prettyInline 0 l
    TupleCreate xs -> parens $ punctuate "," $ map (prettyBlock 0) xs
    RecordCreate fs -> braces $ punctuate "," $ map (prettyBlock 0) fs
    RecordUpdate fs@(_:_) r -> "%" <> braces (punctuate "," $ map (prettyBlock 0) fs) <+> prettyInline 10 r
    EApp a b -> parensIf (9 < prec) $ prettyInline 9 a <+> prettyInline 10 b
    ELit l -> prettyBlock prec l
    ELet bs e -> parensIf (1 < prec) $ align $
      nest 4 ("let" <+> vsep (punctuate "," $ map (prettyInline 0) $ toList bs)) <++>
      "in" <++>
      prettyBlock (if 1 < prec then 0 else prec) e
    ELam (a :| as) -> parensIf (0 < prec) $ align $ case as of
      [] ->
        "fun" <+> prettyBlock 1 a
      as ->
        "fun" <++>
        nest 2 (flatAlt "| " mempty <> prettyInline 1 a) <++>
        vsep (map (\a -> nest 2 ("| " <> prettyInline 1 a)) as)

instance PrettySuffix Expr where
  d <++ e = d <++> "=" <+> align (prettyBlock 0 e)

instance PrettyCode (Label, Expr) where
  prettyBlock _ (l, a) = prettyInline 0 l <+> "=" <+> prettyBlock 0 a

instance PrettyCode LocalDef where
  prettyBlock _ def = nest 2 $
    prettyInline 0 (def^.ident) <++ def^?scheme.typed <++ def^.body

instance PrettyCode Alt where
  prettyBlock prec (ps :-> body) = nest 2 $
    hsep (map (prettyInline 10) (toList ps)) <+> "->" <++>
    prettyBlock prec body

instance PrettyCode Value where
  prettyBlock prec = \case
    VVar id -> prettyBlock prec id
    VDef id -> prettyBlock prec id
    VLocalDef id -> prettyBlock prec id
    VClassMethod id -> prettyBlock prec id
    VPatternDef id -> prettyBlock prec id

instance PrettyCode ValueCon where
  prettyBlock prec = \case
    ValueConData s -> prettyBlock prec s
    ValueConEmptyRecord -> "{}"
    ValueConRecordSelect l -> "{." <> prettyInline 0 l <> "}"
    ValueConRecordRestrict l -> "{-" <> prettyInline 0 l <> "}"
    ValueConRecordExtend l -> "{+" <> prettyInline 0 l <> "}"
    ValueConRecordUpdate l -> "{%" <> prettyInline 0 l <> "}"

instance PrettyCode Def where
  prettyBlock _ def = nest 2 $
    "val" <+> prettyInline 0 (def^.ident) <++ def^?scheme.typed <++ def^.body

instance PrettyCode DataTypeCon where
  prettyBlock _ con = nest 4 $
    "data" <+> sep (prettyInline 9 (con^.ident) : map (prettyInline 10) (con^.parameters))

instance PrettyCode DataValueCon where
  prettyBlock _ con = nest 4 $
    "con" <+> sep (prettyInline 9 (con^.ident) : map (prettyInline 10) (con^.fields))

instance PrettyCode ClassCon where
  prettyBlock _ cls = nest 4 $
    "class" <+> sep (prettyInline 9 (cls^.ident) : map (prettyInline 10) (cls^.parameters)) <++
    cls^.fundeps <++
    cls^.superclasses

instance PrettyCode ClassMethod where
  prettyBlock _ method = nest 2 $
    "val" <+> prettyInline 0 (method^.ident) <++ method^.scheme <++ method^.defaultBody

instance PrettyCode Instance where
  prettyBlock _ inst = nest 4 $
    "instance" <+> (
      inst^?quantification.typed ++>
      sep (prettyInline 9 (inst^.cls) : map (prettyInline 10) (inst^.arguments)) <++
      inst^.context
    )

instance PrettyCode Default where
  prettyBlock _ d =
    "default" `withItems` map (prettyInline 10) (d^.candidates)

instance PrettyCode DumpType where
  prettyBlock _ = \case
    DumpEverything -> mempty
    DumpTypeSignature -> "(type)"
    DumpKindSignature -> "(kind)"

instance PrettyCode Decl where
  prettyBlock prec = \case
    DDef d -> prettyBlock prec d
    DData c cs -> prettyInline prec c `withItems` map (prettyBlock 0) cs
    DClass c vs -> prettyInline prec c `withItems` map (prettyBlock 0) vs
    DInstance c -> prettyInline prec c
    DDefault d -> prettyBlock prec d
    DDump dt d -> "dump" <> prettyInline 0 dt <+> prettyBlock prec d

instance PrettyCode Program where
  prettyBlock _ program = vsep $ map (prettyBlock 0) (program^.decls)

vblock :: Doc ann -> Doc ann -> [Doc ann] -> Doc ann
vblock head tail body = nest 2 (head <> line <> vsep body) <> line <> tail

vblock' :: Doc ann -> Doc ann -> [Doc ann] -> Doc ann
vblock' head tail body = nest 2 (head <> line' <> vsep body) <> line' <> tail

block :: Doc ann -> Doc ann -> [Doc ann] -> Doc ann
block head tail body = group $ vblock head tail body

block' :: Doc ann -> Doc ann -> [Doc ann] -> Doc ann
block' head tail body = group $ vblock' head tail body

withItems :: Doc ann -> [Doc ann] -> Doc ann
withItems d [] = d
withItems d ds = d <+> vblock "{" "}" ds

parens :: [Doc ann] -> Doc ann
parens = block' "(" ")"

brackets :: [Doc ann] -> Doc ann
brackets = block' "[" "]"

braces :: [Doc ann] -> Doc ann
braces = block "{" "}"

angles :: [Doc ann] -> Doc ann
angles = block' "<" ">"

infixr 5 <++>
(<++>) :: Doc ann -> Doc ann -> Doc ann
l <++> r = l <> line <> r

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True d = parens [d]
parensIf False d = d
