{-# LANGUAGE UndecidableInstances #-}
module Titan.Resolver
  ( resolve
  ) where

import Data.Data.Lens (biplate)
import Titan.Prelude
import Titan.Error
import Titan.TT
import Titan.Scope

resolve :: MonadError Error m => Global -> m Global
resolve global = runReaderT (justifyUse global) (emptyScope global)

class JustifyUse a where
  justifyUse :: (MonadError Error m, MonadReader Scope m) => a -> m a

instance {-# OVERLAPPABLE #-} (JustifyUse a, Traversable f) => JustifyUse (f a) where
  justifyUse = mapM justifyUse

instance (Resolvable a a, Identified a) => JustifyUse (Id a) where
  justifyUse id = asks (tryResolveUse' id) >>= \case
    Just a -> return $ identity a
    Nothing -> throwError $ CannotResolve (id^.name)

instance JustifyUse Kind where
  justifyUse = \case
    KVar id -> throwError $ InternalError "Input" $ "Escaped kind variable _" <> id^.name
    KType -> pure KType
    KConstraint -> pure KConstraint
    KRow a -> KRow <$> justifyUse a
    KFun a b -> KFun <$> justifyUse a <*> justifyUse b

instance JustifyUse Type where
  justifyUse = \case
    TVar id _ _ -> throwError $ InternalError "Input" $ "Escaped type variable _" <> id^.name
    TCon tc -> TCon <$> justifyUse tc
    TApp a b -> TApp <$> justifyUse a <*> justifyUse b
    TGen id -> pure $ TGen id -- collect later: see quantifyFreeParams / verifyNoFreeParams

instance JustifyUse TypeCon where
  justifyUse = \case
    TypeConData id -> TypeConData <$> justifyUse id
    TypeConArrow -> pure TypeConArrow
    TypeConRecord -> pure TypeConRecord
    TypeConEmptyRow -> pure TypeConEmptyRow
    TypeConRowExtend l -> pure $ TypeConRowExtend l

instance JustifyUse Parameter where
  justifyUse (Parameter id kind) = Parameter id <$> justifyUse kind

instance JustifyUse (Fundep a) where
  justifyUse = pure

instance JustifyUse Constraint where
  justifyUse = \case
    CClass id ts -> CClass <$> justifyUse id <*> justifyUse ts

instance JustifyUse Scheme where
  justifyUse (Scheme q ty ctx) = do
    q <- justifyUse q
    let mbody = (,) <$> justifyUse ty <*> justifyUse ctx
    case q^?typed of
      Just params -> scoped params $ do
        (ty, ctx) <- mbody
        verifyNoFreeParams (ty, ctx)
        return $ Scheme q ty ctx
      Nothing -> do
        (ty, ctx) <- mbody
        q <- quantifyFreeParams (ty, ctx)
        return $ Scheme q ty ctx

instance JustifyUse Pattern where
  justifyUse = \case
    PVar def p -> PVar <$> justifyUse def <*> justifyUse p
    PWildcard -> pure PWildcard
    PDecon vc ps -> PDecon <$> justifyUse vc <*> justifyUse ps
    PLit l -> pure $ PLit l

instance JustifyUse PatternDef where
  justifyUse = pure

instance JustifyUse Expr where
  justifyUse = \case
    EVar v -> EVar <$> justifyUse v
    ECon vc -> ECon <$> justifyUse vc
    EApp a b -> EApp <$> justifyUse a <*> justifyUse b
    ELit l -> pure $ ELit l
    ELet binds e -> scoped binds $ ELet <$> justifyUse binds <*> justifyUse e
    ELam alts -> ELam <$> justifyUse alts

instance JustifyUse LocalDef where
  justifyUse (LocalDef id scheme body) = do
    scheme <- justifyUse scheme
    body <- scoped scheme $ justifyUse body
    return $ LocalDef id scheme body

instance JustifyUse Alt where
  justifyUse (ps :-> e) =
    (:->) <$> justifyUse ps <*> scoped ps (justifyUse e)

instance JustifyUse Value where
  justifyUse = \case
    VVar id ->
      asks (tryResolveUse' id) >>= \case
        Just v -> justifyUse v
        Nothing -> throwError $ CannotResolve (id^.name)
    VDef id -> VDef <$> justifyUse id
    VLocalDef id -> VLocalDef <$> justifyUse id
    VClassMethod id -> VClassMethod <$> justifyUse id
    VPatternDef id -> VPatternDef <$> justifyUse id

instance JustifyUse ValueCon where
  justifyUse = \case
    ValueConData id -> ValueConData <$> justifyUse id
    ValueConEmptyRecord -> pure ValueConEmptyRecord
    ValueConRecordSelect l -> pure $ ValueConRecordSelect l
    ValueConRecordRestrict l -> pure $ ValueConRecordRestrict l
    ValueConRecordExtend l -> pure $ ValueConRecordExtend l
    ValueConRecordUpdate l -> pure $ ValueConRecordUpdate l

instance JustifyUse Def where
  justifyUse (Def id scheme body) = do
    scheme <- justifyUse scheme
    body <- scoped scheme $ justifyUse body
    return $ Def id scheme body

instance JustifyUse DataType where
  justifyUse (DataTypeCon id params, vs) =
    (,) <$> (DataTypeCon id <$> justifyUse params) <*> scoped params (justifyUse vs)

instance JustifyUse DataValueCon where
  justifyUse (DataValueCon id fields) = do
    fields <- justifyUse fields
    verifyNoFreeParams fields
    return $ DataValueCon id fields

instance JustifyUse Class where
  justifyUse (ClassCon id params fundeps supers, cms) = do
    params <- justifyUse params
    fundeps <- justifyUse fundeps
    supers <- justifyUse supers
    scoped params $ verifyNoFreeParams (fundeps, supers)
    cms <- scoped params $ justifyUse cms
    return (ClassCon id params fundeps supers, cms)

instance JustifyUse ClassMethod where
  justifyUse (ClassMethod id scheme body) = do
    scheme <- justifyUse scheme
    body <- scoped scheme (justifyUse body)
    return $ ClassMethod id scheme body

instance JustifyUse Instance where
  justifyUse (Instance q cls args ctx) = do
    q <- justifyUse q
    cls <- justifyUse cls
    let mbody = (,) <$> justifyUse args <*> justifyUse ctx
    case q^?typed of
      Just params -> scoped params $ do
        (args, ctx) <- mbody
        verifyNoFreeParams (args, ctx)
        return $ Instance q cls args ctx
      Nothing -> do
        (args, ctx) <- mbody
        q <- quantifyFreeParams (args, ctx)
        return $ Instance q cls args ctx

instance JustifyUse Default where
  justifyUse (Default tys) = do
    tys <- justifyUse tys
    verifyNoFreeParams tys
    return $ Default tys

instance JustifyUse Global where
  justifyUse global = execStateT ?? global $ do
    modifyM $ defs %%~ justifyUse
    modifyM $ dataTypes %%~ justifyUse
    modifyM $ classes %%~ justifyUse
    modifyM $ instances %%~ justifyUse
    modifyM $ defaultTypes %%~ justifyUse

freeParams :: (Data t, MonadReader Scope m) => t -> m [Id Parameter]
freeParams t = filterM (fmap isNothing . asks . tryResolveUse') [id | TGen id <- universeOn biplate t]

quantifyFreeParams :: (Data t, MonadReader Scope m) => t -> m (Typing [Parameter])
quantifyFreeParams t = do
  params <- freeParams t
  return $ Typed Inferred $ map (\id -> Parameter id Untyped) $ nubOrd params

verifyNoFreeParams :: (Data t, MonadReader Scope m, MonadError Error m) => t -> m ()
verifyNoFreeParams t = do
  params <- freeParams t
  forM_ params $ \id -> throwError $ CannotResolve (id^.name)
