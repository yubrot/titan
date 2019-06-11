module Titan.Binder
  ( bind
  ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Titan.Prelude
import Titan.Error
import Titan.TT
import Titan.Scope

bind :: MonadError Error m => Global -> Program -> m Global
bind global program = execStateT (bindAll program) global

type Bind m = (MonadError Error m, MonadState Global m)

bindAll :: Bind m => Program -> m ()
bindAll (Program decls) = mapM_ bindDecl decls

bindDecl :: Bind m => Decl -> m ()
bindDecl = \case
  DDef d -> do
    mapM_ (verifyScheme []) (d^.scheme)
    mapM_ verifyExpr (d^.body)
    bindOn defs (identity d) d
    bindOnValues (identity d)
  DData ty vs -> do
    verifyLocalBinds (ty^.parameters)
    bindOn dataTypes (identity ty) (ty, Map.fromList [(identity v, v) | v <- vs])
    forM_ vs $ \v ->
      bindOn dataValueAssocs (identity v) (identity ty)
  DClass cls cms -> do
    verifyLocalBinds (cls^.parameters)
    bindOn classes (identity cls) (cls, Map.fromList [(identity cm, cm) | cm <- cms])
    forM_ cms $ \cm -> do
      verifyScheme (cls^.parameters) (cm^.scheme)
      mapM_ verifyExpr (cm^.defaultBody)
      bindOn classMethodAssocs (identity cm) (identity cls)
      bindOnValues (identity cm)
  DInstance inst -> do
    mapM_ verifyLocalBinds (inst^.quantification)
    instances.at (inst^.cls) <>= Just [inst]
  DDefault d ->
    modifyM $ defaultTypes %%~ \case
      Nothing -> return $ Just d
      Just _ -> throwError MultipleDefault
  DDump dt d -> do
    dumps <>= [(dt, d)]
    bindDecl d

bindOn :: (At s, Index s ~ Id k, IxValue s ~ a, Bind m) => Lens' Global s -> Id k -> a -> m ()
bindOn l id a = modifyM $ l.at id %%~ \case
  Nothing -> return $ Just a
  Just _ -> throwError $ MultipleDeclarationsOf (id^.name)

bindOnValues :: (Bind m, OnValue a) => Id a -> m ()
bindOnValues id =
  let (vid, v) = onValue id in
  bindOn values vid v

verifyScheme :: MonadError Error m => [Parameter] -> Scheme -> m ()
verifyScheme unusableParams scheme = case scheme^.quantification of
  Typed _ params -> verifyLocalBinds $ unusableParams ++ params
  _ -> return ()

verifyExpr :: MonadError Error m => Expr -> m ()
verifyExpr = mapMOf_ cosmos $ \case
  ELet defs _ -> do
    verifyLocalBinds defs
    mapM_ verifyLocalDef defs
  ELam alts -> mapM_ verifyAlt alts
  _ -> pure ()
 where
  verifyLocalDef d = do
    mapM_ (verifyScheme []) (d^.scheme)
    mapM_ verifyExpr (d^.body)
  verifyAlt (ps :-> e) = do
    verifyLocalBinds [def | PVar def _ <- universeOn folded ps]
    verifyExpr e

verifyLocalBinds :: (Foldable f, Identified a, MonadError Error m) => f a -> m ()
verifyLocalBinds = foldM_ collect Set.empty
 where
  collect set a =
    let n = identity a ^. name in
    if Set.member n set
      then throwError $ MultipleDeclarationsOf n
      else return $ Set.insert n set
