{-# LANGUAGE UndecidableInstances #-}
module Titan.Scope where

import Data.Data.Lens (biplate)
import qualified Data.Map as Map
import Titan.Prelude
import Titan.Error
import Titan.TT

type DataType = (DataTypeCon, Map (Id DataValueCon) DataValueCon)

type Class = (ClassCon, Map (Id ClassMethod) ClassMethod)

data Global = Global
  { _defs :: Map (Id Def) Def
  , _dataTypes :: Map (Id DataTypeCon) DataType
  , _classes :: Map (Id ClassCon) Class
  , _instances :: Map (Id ClassCon) [Instance]
  , _defaultTypes :: Maybe Default
  , _values :: Map (Id Value) Value
  , _dataValueAssocs :: Map (Id DataValueCon) (Id DataTypeCon)
  , _classMethodAssocs :: Map (Id ClassMethod) (Id ClassCon)
  , _dumps :: [(DumpType, Decl)]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

emptyGlobal :: Global
emptyGlobal = Global mempty mempty mempty mempty Nothing mempty mempty mempty mempty

data Scope = Scope
  { _global :: Global
  , _parameters :: Map (Id Parameter) Parameter
  , _values :: Map (Id Value) Value
  , _patternDefs :: Map (Id PatternDef) PatternDef
  , _localDefs :: Map (Id LocalDef) LocalDef
  , _typeVariables :: Map (Id Parameter) Type
  , _patternDefTypes :: Map (Id PatternDef) Type
  , _level :: Level
  }
  deriving (Eq, Ord, Show, Data, Typeable)

emptyScope :: Global -> Scope
emptyScope global = Scope global mempty mempty mempty mempty mempty mempty topLevel

makeFieldsNoPrefix ''Global
makeFieldsNoPrefix ''Scope

program :: Global -> Program
program global = Program $ concat
  [ DDef <$> global^..defs.traverse
  , uncurry DData <$> global^..dataTypes.traverse.to (second toList)
  , uncurry DClass <$> global^..classes.traverse.to (second toList)
  , DInstance <$> global^..instances.traverse.each
  , DDefault <$> global^..defaultTypes.each
  ]

dump :: Global -> [Decl]
dump global = mapMaybe (uncurry dumpDecl) (global^.dumps)
 where
  equalInst = (==) `on` (quantification .~ Untyped)
  dumpDecl DumpEverything d = case d of
    DDef def -> DDef <$> global^?defs.ix (identity def)
    DData ty _ -> uncurry DData <$> global^?dataTypes.ix (identity ty).to (second toList)
    DClass cls _ -> uncurry DClass <$> global^?classes.ix (identity cls).to (second toList)
    DInstance inst -> DInstance <$> global^?instances.ix (inst^.cls).folded.filtered (equalInst inst)
    DDefault _ -> DDefault <$> global^.defaultTypes
    DDump _ d -> dumpDecl DumpEverything d
  dumpDecl DumpTypeSignature d = fmap ?? dumpDecl DumpEverything d $ \case
    DDef def -> DDef (def & body .~ Nothing)
    d -> d
  dumpDecl DumpKindSignature d = fmap ?? dumpDecl DumpEverything d $ \case
    DData ty _ -> DData ty []
    DClass cls _ -> DClass cls []
    d -> d

class Scoped a where
  scoped :: (MonadError Error m, MonadReader Scope m) => a -> m b -> m b

instance {-# OVERLAPPABLE #-} (Foldable f, Scoped a) => Scoped (f a) where
  scoped = foldr (\a b -> scoped a . b) id

instance Scoped Parameter where
  scoped p = local $ parameters %~ at (identity p) .~ Just p

instance Scoped (Parameter, Type) where
  scoped (p, ty) =
    local (typeVariables.at (identity p) .~ Just ty) .
    scoped p

instance Scoped Scheme where
  scoped scheme = case scheme^.quantification of
    Typed Explicit scopedParams -> scoped scopedParams
    _ -> id

instance Scoped LocalDef where
  scoped def = local $ \scope ->
    let id = identity def
        (vid, v) = onValue id
        def' = def & scheme.typed %~ replaceScopedTypeVariables (scope^.typeVariables)
    in
    scope & values.at vid .~ Just v & localDefs.at id .~ Just def'

instance Scoped PatternDef where
  scoped def = local $ \scope ->
    let id = identity def
        (vid, v) = onValue id
    in
    scope & values.at vid .~ Just v & patternDefs.at id .~ Just def

-- NOTE: Embedding type?
instance Scoped (PatternDef, Type) where
  scoped (def, ty) =
    local (patternDefTypes.at (identity def) .~ Just ty) .
    scoped def

instance Scoped Pattern where
  scoped p = scoped [def | PVar def _ <- universe p]

instance Scoped Def where
  scoped def = local $ global.defs.ix (identity def) .~ def

instance Scoped ClassMethod where
  scoped cm m = do
    let id = identity cm
    id' <- resolveUse id
    local (global.classes.ix id'._2.ix id .~ cm) m

scopedLevel :: MonadReader Scope m => m a -> m a
scopedLevel = local (level %~ upLevel)

captureScopedTypeVariables :: MonadReader Scope m => Scheme -> m Scheme
captureScopedTypeVariables scheme = replaceScopedTypeVariables <$> view typeVariables <*> pure scheme

replaceScopedTypeVariables :: Map (Id Parameter) Type -> Scheme -> Scheme
replaceScopedTypeVariables map scheme = transformOn biplate ?? scheme $ \case
  TGen id | Just t <- map'^.at id -> t
  t -> t
 where
  map' = foldr Map.delete map (scheme^..quantification.typed.each.ident)

class Resolvable a b where
  tryResolveUse :: Id a -> Scope -> Maybe b

  default tryResolveUse :: (Resolvable a (Id b), Resolvable b b) => Id a -> Scope -> Maybe b
  tryResolveUse id scope = do
    id <- tryResolveUse id scope
    tryResolveUse' id scope

  resolveUse :: (MonadReader Scope m, MonadError Error m) => Id a -> m b
  resolveUse id = asks (tryResolveUse id) >>= \case
    Just b -> pure b
    _ -> throwError $ InternalError "Resolver" $ "Escaped use of " ++ id^.name

tryResolveUse' :: Resolvable a a => Id a -> Scope -> Maybe a
tryResolveUse' = tryResolveUse

resolveUse' :: (Resolvable a a, MonadReader Scope m, MonadError Error m) => Id a -> m a
resolveUse' = resolveUse

instance Resolvable PatternDef PatternDef where
  tryResolveUse id scope = scope^?patternDefs.ix id

instance Resolvable PatternDef Type where
  tryResolveUse id scope = scope^?patternDefTypes.ix id

instance Resolvable LocalDef LocalDef where
  tryResolveUse id scope = scope^?localDefs.ix id

instance Resolvable Parameter Parameter where
  tryResolveUse id scope = scope^?parameters.ix id

instance Resolvable Value Value where
  tryResolveUse id scope = scope^?values.ix id <|> scope^?global.values.ix id

instance Resolvable Def Def where
  tryResolveUse id scope = scope^?global.defs.ix id

instance Resolvable DataTypeCon DataTypeCon where
  tryResolveUse id scope = scope^?global.dataTypes.ix id._1

instance Resolvable DataTypeCon (Map (Id DataValueCon) DataValueCon) where
  tryResolveUse id scope = scope^?global.dataTypes.ix id._2

instance Resolvable DataValueCon (Id DataTypeCon) where
  tryResolveUse id scope = scope^?global.dataValueAssocs.ix id

instance Resolvable DataValueCon DataTypeCon

instance Resolvable DataValueCon DataValueCon where
  tryResolveUse id scope = do
    id' <- tryResolveUse id scope
    scope^?global.dataTypes.ix id'._2.ix id

instance Resolvable ClassCon ClassCon where
  tryResolveUse id scope = scope^?global.classes.ix id._1

instance Resolvable ClassCon (Map (Id ClassMethod) ClassMethod) where
  tryResolveUse id scope = scope^?global.classes.ix id._2

instance Resolvable ClassMethod (Id ClassCon) where
  tryResolveUse id scope = scope^?global.classMethodAssocs.ix id

instance Resolvable ClassMethod ClassCon

instance Resolvable ClassMethod ClassMethod where
  tryResolveUse id scope = do
    id' <- tryResolveUse id scope
    scope^?global.classes.ix id'._2.ix id

instance Resolvable ClassCon [Instance] where
  tryResolveUse id scope = Just $ scope^..global.instances.ix id.each

class KindOf a where
  kindOf :: (MonadReader Scope m, MonadError Error m) => a -> m Kind

instance (Resolvable a a, KindOf a) => KindOf (Id a) where
  kindOf id = resolveUse' id >>= kindOf

instance KindOf Type where
  kindOf = \case
    TVar _ k _ -> pure k
    TCon tc -> kindOf tc
    TApp a b -> do
      ak <- kindOf a
      bk <- kindOf b
      case ak of
        KFun k k' | k == bk -> pure k'
        _ -> throwError $ InternalError "KI" "Kind mismatch"
    TGen p -> kindOf p

instance KindOf TypeCon where
  kindOf = \case
    TypeConData id -> kindOf id
    TypeConArrow -> pure $ KType :--> KType :--> KType

instance KindOf Parameter where
  kindOf p = case p^?kind.typed of
    Just k -> pure k
    _ -> throwError $ InternalError "KI" "Escaped untyped kind"

instance KindOf DataTypeCon where
  kindOf ty = foldr (:-->) KType <$> mapM kindOf (ty^.parameters)

instance KindOf ClassCon where
  kindOf cls = foldr (:-->) KConstraint <$> mapM kindOf (cls^.parameters)

class TypeOf a where
  typeOf :: (MonadReader Scope m, MonadError Error m) => a -> m Scheme

instance (Resolvable a a, TypeOf a) => TypeOf (Id a) where
  typeOf id = resolveUse' id >>= typeOf

instance TypeOf PatternDef where
  typeOf p = do
    ty <- resolveUse @_ @Type (identity p)
    return $ Scheme (Typed Inferred []) ty []

instance TypeOf LocalDef where
  typeOf def = case def^.scheme of
    Typed _ scheme -> return scheme
    Untyped -> throwError $ InternalError "TI" "Escaped untyped scheme"

instance TypeOf Value where
  typeOf = \case
    VVar _ -> throwError $ InternalError "Resolver" "Escaped unresolved variable"
    VDef id -> typeOf id
    VLocalDef id -> typeOf id
    VClassMethod id -> typeOf id
    VPatternDef id -> typeOf id

instance TypeOf ValueCon where
  typeOf = \case
    ValueConData id -> typeOf id

instance TypeOf Def where
  typeOf def = case def^.scheme of
    Typed _ scheme -> return scheme
    Untyped -> throwError $ InternalError "TI" "Escaped untyped scheme"

instance TypeOf DataValueCon where
  typeOf vc = do
    ty <- resolveUse @_ @DataTypeCon (identity vc)
    let body = foldr (:-->) (foldl (:@@) (TCon (TypeConData (identity ty))) [TGen (identity p) | p <- ty^.parameters]) (vc^.fields)
    return $ Scheme (Typed Explicit (ty^.parameters)) body mempty

instance TypeOf ClassMethod where
  typeOf cm = do
    cls <- resolveUse @_ @ClassCon (identity cm)
    return $ cm^.scheme
      & quantification.typed %~ ((cls^.parameters) <>)
      & context %~ (CClass (identity cls) [TGen (identity p) | p <- cls^.parameters] :)
