module Titan.TT where

import Titan.Prelude

data Typing a
  = Untyped
  | Typed { _explicitness :: Explicitness, _typed :: a }
  deriving (Show, Data, Typeable, Functor, Foldable, Traversable)

instance Eq a => Eq (Typing a) where
  Untyped   == Untyped   = True
  Typed _ a == Typed _ b = a == b
  _         == _         = False

instance Ord a => Ord (Typing a) where
  compare Untyped     Untyped     = EQ
  compare Untyped     _           = LT
  compare _           Untyped     = GT
  compare (Typed _ a) (Typed _ b) = compare a b

class Fun a where
  fun :: Prism' a (a, a)

pattern (:-->) :: Fun a => a -> a -> a
pattern (:-->) a b <- (preview fun -> Just (a, b))
  where (:-->) a b = review fun (a, b)

infixr 0 :-->

class App a where
  app :: Prism' a (a, a)

pattern (:@@) :: App a => a -> a -> a
pattern (:@@) a b <- (preview app -> Just (a, b))
  where (:@@) a b = review app (a, b)

infixl 1 :@@

data Explicitness
  = Explicit
  | Inferred
  deriving (Eq, Ord, Show, Data, Typeable)

type Name = String

type Arity = Int

newtype Id a = Id
  { _name :: Name
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Kind
  = KVar (Id Kind)
  | KType
  | KConstraint
  | KFun Kind Kind
  deriving (Eq, Ord, Show, Data, Typeable)

instance Fun Kind where
  fun = prism (uncurry KFun) $ \case
    KFun a b -> Right (a, b)
    k -> Left k

newtype Level = Level
  { _value :: Int
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Type
  = TVar (Id Type) Kind Level
  | TCon TypeCon
  | TApp Type Type
  | TGen (Id Parameter)
  deriving (Eq, Ord, Show, Data, Typeable)

instance Fun Type where
  fun = prism (uncurry TFun) $ \case
    TFun a b -> Right (a, b)
    k -> Left k

instance App Type where
  app = prism (uncurry TApp) $ \case
    TApp a b -> Right (a, b)
    k -> Left k

pattern TFun :: Type -> Type -> Type
pattern TFun a b = TCon TypeConArrow :@@ a :@@ b

-- FIXME: Do not depend on well-known types lexically.

pattern TChar :: Type
pattern TChar = TCon (TypeConData (Id "Char"))

pattern TListCon :: Type
pattern TListCon = TCon (TypeConData (Id "List"))

data TypeCon
  = TypeConData (Id DataTypeCon)
  | TypeConArrow
  deriving (Eq, Ord, Show, Data, Typeable)

data Parameter = Parameter
  { _ident :: Id Parameter
  , _kind :: Typing Kind -- determined by KI
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Fundep a = (:~>)
  { _given :: [Id a]
  , _determines :: [Id a]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Constraint
  = CClass (Id ClassCon) [Type]
  deriving (Eq, Ord, Show, Data, Typeable)

-- FIXME: Do not depend on well-known classes lexically.

pattern CNum :: Type -> Constraint
pattern CNum a = CClass (Id "Num") [a]

pattern CFractional :: Type -> Constraint
pattern CFractional a = CClass (Id "Fractional") [a]

data Scheme = Scheme
  { _quantification :: Typing [Parameter] -- determined by Resolver
  , _body :: Type
  , _context :: [Constraint]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Literal
  = LInteger Integer
  | LChar Char
  | LFloat Double
  | LString String
  deriving (Eq, Ord, Show, Data, Typeable)

data Pattern
  = PVar PatternDef (Maybe Pattern)
  | PWildcard
  | PDecon ValueCon [Pattern]
  | PLit Literal
  deriving (Eq, Ord, Show, Data, Typeable)

data PatternDef = PatternDef
  { _ident :: Id PatternDef
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Expr
  = EVar Value
  | ECon ValueCon
  | EApp Expr Expr
  | ELit Literal
  | ELet (NonEmpty LocalDef) Expr
  | ELam (NonEmpty Alt)
  deriving (Eq, Ord, Show, Data, Typeable)

instance App Expr where
  app = prism (uncurry EApp) $ \case
    EApp a b -> Right (a, b)
    k -> Left k

data LocalDef = LocalDef
  { _ident :: Id LocalDef
  , _scheme :: Typing Scheme -- determined by TI
  , _body :: Maybe Expr
  }
  deriving (Eq, Ord, Show, Data, Typeable)

pattern ELet1 :: LocalDef -> Expr -> Expr
pattern ELet1 d e = ELet (d :| []) e

pattern ELam1 :: Alt -> Expr
pattern ELam1 a = ELam (a :| [])

data Alt = (:->)
  { _patterns :: NonEmpty Pattern
  , _body :: Expr
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Value
  = VVar (Id Value) -- determined by Resolver
  | VDef (Id Def)
  | VLocalDef (Id LocalDef)
  | VClassMethod (Id ClassMethod)
  | VPatternDef (Id PatternDef)
  deriving (Eq, Ord, Show, Data, Typeable)

data ValueCon
  = ValueConData (Id DataValueCon)
  deriving (Eq, Ord, Show, Data, Typeable)

data Def = Def
  { _ident :: Id Def
  , _scheme :: Typing Scheme -- determined by TI
  , _body :: Maybe Expr
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data DataTypeCon = DataTypeCon
  { _ident :: Id DataTypeCon
  , _parameters :: [Parameter]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data DataValueCon = DataValueCon
  { _ident :: Id DataValueCon
  , _fields :: [Type]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data ClassCon = ClassCon
  { _ident :: Id ClassCon
  , _parameters :: [Parameter]
  , _fundeps :: [Fundep Parameter]
  , _superclasses :: [Constraint]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data ClassMethod = ClassMethod
  { _ident :: Id ClassMethod
  , _scheme :: Scheme
  , _defaultBody :: Maybe Expr
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Instance = Instance
  { _quantification :: Typing [Parameter] -- determined by Resolver
  , _cls :: Id ClassCon
  , _arguments :: [Type]
  , _context :: [Constraint]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Default = Default
  { _candidates :: [Type]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data DumpType
  = DumpEverything
  | DumpTypeSignature
  | DumpKindSignature
  deriving (Eq, Ord, Show, Data, Typeable)

data Decl
  = DDef Def
  | DData DataTypeCon [DataValueCon]
  | DClass ClassCon [ClassMethod]
  | DInstance Instance
  | DDefault Default
  | DDump DumpType Decl
  deriving (Eq, Ord, Show, Data, Typeable)

newtype Program = Program
  { _decls :: [Decl]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

makeFieldsNoPrefix ''Typing
makeFieldsNoPrefix ''Id
makeFieldsNoPrefix ''Level
makeFieldsNoPrefix ''Parameter
makeFieldsNoPrefix ''Fundep
makeFieldsNoPrefix ''Scheme
makeFieldsNoPrefix ''PatternDef
makeFieldsNoPrefix ''LocalDef
makeFieldsNoPrefix ''Alt
makeFieldsNoPrefix ''Def
makeFieldsNoPrefix ''DataTypeCon
makeFieldsNoPrefix ''DataValueCon
makeFieldsNoPrefix ''ClassCon
makeFieldsNoPrefix ''ClassMethod
makeFieldsNoPrefix ''Instance
makeFieldsNoPrefix ''Default
makeFieldsNoPrefix ''Program

instance Applicative Typing where
  pure = Typed Explicit
  Typed i f <*> m = case fmap f m of
    Typed i' a -> Typed (max i i') a
    a -> a
  Untyped   <*> _ = Untyped

instance Alternative Typing where
  empty = Untyped
  Untyped <|> r = r
  l       <|> _ = l

ids :: [Id a]
ids = do
  i <- [1..]
  s <- replicateM i ['a'..'z']
  return $ Id s

topLevel :: Level
topLevel = Level 0

upLevel :: Level -> Level
upLevel = value %~ succ

isOnLevel :: Level -> Level -> Bool
isOnLevel (Level a) (Level b) = a <= b

downToLevel :: Level -> Level -> Level
downToLevel (Level a) (Level b) = Level (min a b)

instance Plated Kind
instance Plated Type
instance Plated Pattern
instance Plated Expr

class Identified a where
  identity :: a -> Id a
  default identity :: HasIdent a (Id a) => a -> Id a
  identity = view ident

instance Identified Parameter
instance Identified PatternDef
instance Identified LocalDef
instance Identified Def
instance Identified DataTypeCon
instance Identified DataValueCon
instance Identified ClassCon
instance Identified ClassMethod

class OnValue a where
  onValue :: Id a -> (Id Value, Value)
  onValue = toValueId &&& toValue
  toValueId :: Id a -> Id Value
  toValueId (Id name) = Id name
  toValue :: Id a -> Value

instance OnValue LocalDef where
  toValue = VLocalDef

instance OnValue PatternDef where
  toValue = VPatternDef

instance OnValue Def where
  toValue = VDef

instance OnValue ClassMethod where
  toValue = VClassMethod

class Var a where
  var :: Name -> a

instance Var Type where
  var s = TGen $ Id s

instance Var Parameter where
  var s = Parameter (Id s) Untyped

instance Var Pattern where
  var s = PVar (var s) Nothing

instance Var PatternDef where
  var s = PatternDef (Id s)

instance Var Expr where
  var = EVar . var

instance Var Value where
  var s = VVar $ Id s

class Con a p | a -> p where
  con :: Name -> [p] -> a

instance Con Type Type where
  con c = foldl (:@@) (TCon $ TypeConData $ Id c)

instance Con Constraint Type where
  con c = CClass (Id c) . toList

instance Con Pattern Pattern where
  con c = PDecon (ValueConData $ Id c)

instance Con Expr Expr where
  con c = foldl (:@@) (ECon $ ValueConData $ Id c)
