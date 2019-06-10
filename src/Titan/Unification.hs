module Titan.Unification
  ( Subst(..)
  , emptySubst
  , (+->)
  , extend
  , occurs
  , apply
  , vars
  , mgu
  , match
  ) where

import Data.Data.Lens (biplate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Titan.Prelude
import Titan.Error
import Titan.TT
import Titan.Scope

newtype Subst a = Subst (Map (Id a) a)
  deriving (Eq, Ord, Show)

emptySubst :: Subst a
emptySubst = Subst mempty

(+->) :: Id a -> a -> Subst a
id +-> a = Subst $ Map.singleton id a

-- Extend `a` by merging `a'`.
-- `a'` is calculated on `a`; substitutions of `a` has already been applied to `a'` and
-- therefore we only need to apply `a'` to `a`.
extend :: Substitutable a => Subst a -> Subst a -> Subst a
extend (Subst a') (Subst a) = Subst $ Map.union a' $ Map.map (apply (Subst a')) a

occurs :: (Substitutable a, Data t) => Id a -> t -> Bool
occurs id a = id `elem` vars topLevel a

apply :: (Substitutable a, Data t) => Subst a -> t -> t
apply subst = over biplate (apply' subst)

vars :: forall a t. (Substitutable a, Data t) => Level -> t -> Set (Id a)
vars lv = view (biplate.to (vars' lv))

-- Compute the most general unifier.
mgu :: forall a t m. (Mgu a, Data t, MonadReader Scope m, MonadError Error m) => t -> t -> m (Subst a)
mgu a b = mguElems emptySubst (a^..biplate) (b^..biplate)
 where
  mguElems s (a:as) (b:bs) = do
    s' <- mgu' (apply s a) (apply s b)
    mguElems (extend s' s) as bs
  mguElems s [] [] = return s
  mguElems _ _ _ = throwError $ InternalError "KI" "Structure mismatch"

-- Compute a substitution from lhs to rhs.
-- If there are no suitable substitution, MatchFailed is thrown.
match :: forall a t m. (Match a, Eq a, Data t, MonadReader Scope m, MonadError Error m) => t -> t -> m (Subst a)
match a b = matchElems emptySubst (a^..biplate) (b^..biplate)
 where
  matchElems (Subst s) (a:as) (b:bs) = do
    Subst s' <- match' a b
    if and [s'^.at id == s^.at id | id <- Map.keys $ Map.intersection s' s]
      then matchElems (Subst (Map.union s' s)) as bs
      else throwError MatchFailed
  matchElems s [] [] = return s
  matchElems _ _ _ = throwError MatchFailed

class Data a => Substitutable a where
  apply' :: Subst a -> a -> a
  vars' :: Level -> a -> Set (Id a)

instance Substitutable Type where
  apply' (Subst map) = transform $ \case
    t@(TVar id _ _) | Just t' <- map^.at id, t /= t' -> apply' (Subst map) t'
    t -> t
  vars' lv t = Set.fromList [id' | TVar id' _ lv' <- universe t, isOnLevel lv lv']

instance Substitutable Kind where
  apply' (Subst map) = transform $ \case
    KVar id | Just k <- map^.at id -> k
    k -> k
  vars' _ k = Set.fromList [id | KVar id <- universe k]

class Substitutable a => Mgu a where
  mgu' :: (MonadReader Scope m, MonadError Error m) => a -> a -> m (Subst a)

instance Mgu Kind where
  mgu' a b = case (a, b) of
    (KFun l r, KFun l' r') -> mgu [l, r] [l', r']
    (KVar id, k) -> varBind id k
    (k, KVar id) -> varBind id k
    (a, b) -> do
      when (a /= b) $ throwError $ CannotUnifyKind a b Mismatch
      return emptySubst
   where
    varBind id k = if
      | k == KVar id ->
          return emptySubst
      | occurs id k ->
          throwError $ CannotUnifyKind (KVar id) k OccursCheckFailed
      | otherwise ->
          return $ id +-> k

instance Mgu Type where
  mgu' a b = case (a, b) of
    (TApp l r, TApp l' r') -> mgu [l, r] [l', r']
    (TVar id k lv, t) -> varBind (id, k, lv) t
    (t, TVar id k lv) -> varBind (id, k, lv) t
    (a, b) -> do
      when (a /= b) $ throwError $ CannotUnifyType a b Mismatch
      return emptySubst
   where
    varBind (id, k, lv) t = if
      | t == TVar id k lv ->
          return emptySubst
      | occurs id t ->
          throwError $ CannotUnifyType (TVar id k lv) t OccursCheckFailed
      | otherwise -> do
          tk <- kindOf t
          when (k /= tk) $ throwError $ InternalError "KI" "Kind mismatch"
          let adjustedVars = Map.fromList [(id', TVar id' k' (downToLevel lv lv')) | TVar id' k' lv' <- universe t, isOnLevel (upLevel lv) lv']
          return $ Subst $ Map.insert id t adjustedVars

class Substitutable a => Match a where
  match' :: (MonadReader Scope m, MonadError Error m) => a -> a -> m (Subst a)

instance Match Type where
  match' a b = case (a, b) of
    (TApp l r, TApp l' r') -> match [l, r] [l', r']
    (TVar id k lv, t) -> do
      k' <- kindOf t
      when (k /= k') $ throwError MatchFailed
      let outerVars = [id' | TVar id' _ lv' <- universe t, isOnLevel (upLevel lv) lv']
      unless (null outerVars) $ throwError MatchFailed
      return $ id +-> t
    (a, b) -> do
      when (a /= b) $ throwError MatchFailed
      return emptySubst
