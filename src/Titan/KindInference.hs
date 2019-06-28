module Titan.KindInference
  ( ki
  ) where

import Data.Data.Lens (biplate)
import qualified Data.Map as Map
import Titan.Prelude
import Titan.Error
import Titan.TT
import Titan.Scope
import Titan.Unification
import Titan.DependencyAnalyzer (depGroups)

data KIState = KIState
  { _subst :: Subst Kind
  , _kindIds :: [Id Kind]
  }

emptyKIState :: KIState
emptyKIState = KIState emptySubst ids

makeFieldsNoPrefix ''KIState

ki :: MonadError Error m => Global -> m Global
ki g = evalStateT ?? emptyKIState $ do
  g <- initialize g
  runReaderT (kiAll g) (emptyScope g)
  produce g

initialize :: MonadState KIState m => Global -> m Global
initialize global = traverseOf biplate ?? global $ \case
  Untyped -> Typed Inferred <$> newKVar
  k -> pure k

produce :: MonadState KIState m => Global -> m Global
produce g = apply <$> use subst <*> pure g

type KI m = (MonadReader Scope m, MonadState KIState m, MonadError Error m)

kiAll :: KI m => Global -> m ()
kiAll g = do
  mapM_ kiDataTypes $ depGroups $ Map.assocs (g^.dataTypes)
  mapM_ kiClasses $ depGroups $ Map.assocs (g^.classes & traverse._2.traverse.defaultBody .~ Nothing)
  mapM_ kiDef (g^.defs)
  mapM_ kiClassMethodBodies (g^.classes)
  mapM_ kiInstance (g^..instances.traverse.each)
  mapM_ kiDefault (g^..defaultTypes.traverse)

kiType :: KI m => Type -> m Kind
kiType = \case
  TVar _ _ _ ->
    throwError $ InternalError "Input" "Escaped type variable"
  TCon tc ->
    kindOf tc
  TApp a b -> do
    ak <- kiType a
    bk <- kiType b
    k <- newKVar
    unify (bk :--> k) ak
    return k
  TGen id ->
    kindOf id

kiConstraint :: KI m => Constraint -> m ()
kiConstraint = \case
  CClass id tys -> do
    k <- kindOf id
    k' <- foldr (:-->) KConstraint <$> mapM kiType tys
    unify k k'

kiScheme :: KI m => Scheme -> m ()
kiScheme (Scheme params ty cs) = do
  scoped params $ do
    k <- kiType ty
    unify k KType
    mapM_ kiConstraint cs

kiExpr :: KI m => Expr -> m ()
kiExpr = traverseOf_ biplate kiLocalDef

kiLocalDef :: KI m => LocalDef -> m ()
kiLocalDef def = do
  mapM_ kiScheme (def^.scheme)
  mapM_ defaults (def^.scheme)
  scoped (def^.scheme) $ mapM_ kiExpr (def^.body)

kiDef :: KI m => Def -> m ()
kiDef def = do
  mapM_ kiScheme (def^.scheme)
  mapM_ defaults (def^.scheme)
  scoped (def^.scheme) $ mapM_ kiExpr (def^.body)

kiDataTypes :: KI m => [DataType] -> m ()
kiDataTypes dataTypes = do
  forM_ dataTypes $ \(ty, vs) ->
    scoped (ty^.parameters) $
      forM_ vs $ \v ->
        forM_ (v^.fields) $ \field -> do
          k <- kiType field
          unify k KType
  mapM_ defaults dataTypes

kiClasses :: KI m => [Class] -> m ()
kiClasses classes = do
  forM_ classes $ \(cls, cms) ->
    scoped (cls^.parameters) $ do
      mapM_ kiConstraint (cls^.superclasses)
      mapM_ kiScheme (cms^..traverse.scheme)
  forM_ classes $ \(cls, cms) -> do
    defaults cls
    mapM_ defaults (cms^..traverse.scheme)

kiClassMethodBodies :: KI m => Class -> m ()
kiClassMethodBodies (cls, cms) =
  scoped (cls^.parameters) $
    forM_ cms $ \cm ->
      scoped (cm^.scheme) $ mapM_ kiExpr (cm^.defaultBody)

kiInstance :: KI m => Instance -> m ()
kiInstance inst = do
  scoped (inst^.quantification) $ do
    kiConstraint $ CClass (inst^.cls) (inst^.arguments)
    mapM_ kiConstraint (inst^.context)
  defaults (inst^.quantification)

kiDefault :: KI m => Default -> m ()
kiDefault dflt = mapM_ kiType (dflt^.candidates)

defaults :: (Data a, KI m) => a -> m ()
defaults a = do
  s <- use subst
  mapM_ (unify KType . KVar) $ vars topLevel (apply s a)

unify :: KI m => Kind -> Kind -> m ()
unify k1 k2 = do
  s <- use subst
  s' <- mgu (apply s k1) (apply s k2)
  subst %= extend s'

newKVar :: MonadState KIState m => m Kind
newKVar = kindIds %%= \ids -> (KVar $ head ids, tail ids)
