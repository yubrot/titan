module Titan.Parser
  ( Parse(..)
  , Parser
  ) where

import Control.Monad.Combinators.NonEmpty (some, sepBy1)
import qualified Data.Char as Char
import qualified Data.List.NonEmpty as NonEmpty
import Text.Megaparsec hiding (parse, some, sepBy1)
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Titan.Prelude hiding (many, some)
import Titan.Error
import Titan.TT hiding (kind, scheme, fundeps, quantification, context)

type Parser = Parsec Void String

class Parse a where
  parse :: String -> String -> Either Error a
  parse = parsing p
  p :: Parser a

instance Parse Kind where
  p = kind E

instance Parse Type where
  p = ty E

instance Parse Parameter where
  p = parameter

instance Parse Constraint where
  p = constraint

instance Parse Scheme where
  p = scheme

instance Parse Literal where
  p = literal

instance Parse Pattern where
  p = pat E

instance Parse Expr where
  p = expr E

instance Parse Decl where
  p = decl

instance Parse Program where
  p = program

------
-- Parser
------

inferrable :: Parser a -> Parser (Typing a)
inferrable p = maybe Untyped (Typed Explicit) <$> optional p

anyId :: Parser Name -> Parser (Id a)
anyId rep = try $ do
  s <- rep
  when (elem s reservedWords) $ unexpected $ Label $ NonEmpty.fromList "reserved"
  pure $ Id s

parameterId :: Parser (Id Parameter)
parameterId = anyId lowerIdentifier

valueId :: Parser (Id Value)
valueId = anyId lowerIdentifier

valueId' :: OnValue a => Parser (Id a)
valueId' = do
  id <- anyId lowerIdentifier
  let _ = onValue id
  return id

dataTypeConId :: Parser (Id DataTypeCon)
dataTypeConId = anyId upperIdentifier

dataValueConId :: Parser (Id DataValueCon)
dataValueConId = anyId upperIdentifier

classConId :: Parser (Id ClassCon)
classConId = anyId upperIdentifier

data E = E | T | F

kind :: E -> Parser Kind
kind = \case
  E -> foldr1 (-->) <$> ((:) <$> kind T <*> many (reserved "->" *> kind E))
  T -> kind F
  F -> choice
    [ KType <$ reserved "Type"
    , KConstraint <$ reserved "Constraint"
    , parens (kind E)
    ]

ty :: E -> Parser Type
ty = \case
  E -> foldr1 (-->) <$> ((:) <$> ty T <*> many (reserved "->" *> ty E))
  T -> foldl1 (@@) <$> some (ty F)
  F -> choice
    [ TGen <$> parameterId
    , TCon <$> typeCon
    , parens (ty E)
    ]

typeCon :: Parser TypeCon
typeCon = choice
  [ TypeConArrow <$ symbol "(->)"
  , TypeConData <$> dataTypeConId
  ]

parameter :: Parser Parameter
parameter = choice
  [ Parameter <$> parameterId <*> pure Untyped
  , parens (Parameter <$> parameterId <*> (Typed Explicit <$ reserved ":" <*> kind E))
  ]

fundep :: Parser (Id a) -> Parser (Fundep a)
fundep id = (:~>) <$> many id <* reserved "~>" <*> many id

constraint :: Parser Constraint
constraint = choice
  [ CClass <$> classConId <*> many (ty F)
  ]

scheme :: Parser Scheme
scheme = Scheme <$> inferrable quantification <*> ty E <*> context

fundeps :: Parser [Fundep Parameter]
fundeps = option mempty $ reserved "|" *> (fundep parameterId `sepBy` symbol ",")

quantification :: Parser [Parameter]
quantification = symbol "[" *> many parameter <* symbol "]"

context :: Parser [Constraint]
context = option mempty $ reserved "where" *> choice
  [ parens (constraint `sepBy` symbol ",")
  , pure <$> constraint
  ]

literal :: Parser Literal
literal = choice
  [ try $ LFloat <$> signed float
  , try $ LInteger <$> signed integer
  , LChar <$> char
  , LString <$> string
  ]

pat :: E -> Parser Pattern
pat = \case
  E -> pat T
  T -> choice
    [ PDecon <$> valueCon <*> many (pat F)
    , pat F
    ]
  F -> choice
    [ PWildcard <$ reserved "_"
    , PVar <$> patternDef <*> optional (reserved "@" *> pat F)
    , PDecon <$> valueCon <*> pure []
    , PLit <$> literal
    , parens (pat E)
    ]

patternDef :: Parser PatternDef
patternDef = PatternDef <$> valueId'

expr :: E -> Parser Expr
expr = \case
  E -> choice
    [ ELet <$ reserved "let" <*> (localDef `sepBy1` symbol ",") <* reserved "in" <*> expr E
    , ELam <$ reserved "fun" <* option () (reserved "|") <*> (alt `sepBy1` reserved "|")
    , expr T
    ]
  T -> foldl1 (@@) <$> some (expr F)
  F -> choice
    [ EVar . VVar <$> valueId
    , ECon <$> valueCon
    , ELit <$> literal
    , parens (expr E)
    ]

localDef :: Parser LocalDef
localDef = LocalDef <$> valueId' <*> inferrable (reserved ":" *> scheme) <*> optional (reserved "=" *> expr E)

alt :: Parser Alt
alt = (:->) <$> some (pat F) <* reserved "->" <*> expr E

valueCon :: Parser ValueCon
valueCon = choice
  [ ValueConData <$> dataValueConId
  ]

def :: Parser Def
def = Def <$> valueId' <*> inferrable (reserved ":" *> scheme) <*> optional (reserved "=" *> expr E)

dataTypeCon :: Parser DataTypeCon
dataTypeCon = DataTypeCon <$ reserved "data" <*> dataTypeConId <*> many parameter

dataValueCon :: Parser DataValueCon
dataValueCon = DataValueCon <$ reserved "con" <*> dataValueConId <*> many (ty F)

classCon :: Parser ClassCon
classCon = ClassCon <$ reserved "class" <*> classConId <*> many parameter <*> fundeps <*> context

classMethod :: Parser ClassMethod
classMethod = ClassMethod <$ reserved "val" <*> valueId' <* reserved ":" <*> scheme <*> optional (reserved "=" *> expr E)

inst :: Parser Instance
inst = Instance <$ reserved "instance" <*> inferrable quantification <*> classConId <*> many (ty F) <*> context

dflt :: Parser Default
dflt = Default <$ reserved "default" <*> items (ty F)

dumpType :: Parser DumpType
dumpType = option DumpEverything $ parens $ choice
  [ DumpTypeSignature <$ reserved "type"
  , DumpKindSignature <$ reserved "kind"
  ]

decl :: Parser Decl
decl = choice
  [ DDef <$ reserved "val" <*> def
  , DData <$> dataTypeCon <*> items dataValueCon
  , DClass <$> classCon <*> items classMethod
  , DInstance <$> inst
  , DDefault <$> dflt
  , DDump <$ reserved "dump" <*> dumpType <*> decl
  ]

items :: Parser a -> Parser [a]
items p = braces (many p) <|> pure []

program :: Parser Program
program = Program <$> many decl

------
-- Lexer
------

reservedWords :: [Name]
reservedWords = ["let", "fun", "in", "val", "con", "data", "class", "instance", "default", "where", "dump"]

amb :: Parser ()
amb = L.space (void C.spaceChar) lineComment blockComment
 where
  lineComment = L.skipLineComment "//"
  blockComment = L.skipBlockComment "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme amb

lowerIdentifier :: Parser Name
lowerIdentifier = lexeme $ (:) <$> C.lowerChar <*> many identifierChar

upperIdentifier :: Parser Name
upperIdentifier = lexeme $ (:) <$> C.upperChar <*> many identifierChar

identifierChar :: Parser Char
identifierChar = C.alphaNumChar <|> C.char '_'

signed :: Num a => Parser a -> Parser a
signed = L.signed amb

integer :: Parser Integer
integer = lexeme L.decimal

float :: Parser Double
float = lexeme L.float

char :: Parser Char
char = lexeme (C.char '\'' *> L.charLiteral <* C.char '\'')

string :: Parser String
string = lexeme (C.char '"' *> manyTill L.charLiteral (C.char '"'))

symbol :: String -> Parser ()
symbol = lexeme . void . C.string

reserved :: Name -> Parser ()
reserved s = if
  | Char.isLetter (head s) ->
      lexeme $ try $ void (C.string s) >> notFollowedBy identifierChar
  | otherwise ->
      lexeme $ try $ void (C.string s) >> notFollowedBy (satisfy (`elem` s))

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

parsing :: Parser a -> String -> String -> Either Error a
parsing p path text = case runParser (amb *> p <* eof) path text of
  Left e -> Left $ ParseError $ errorBundlePretty e
  Right r -> Right r
