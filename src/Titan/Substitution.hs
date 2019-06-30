module Titan.Substitution
  ( Subst(..)
  , emptySubst
  , (+->)
  , extend
  , occurs
  , apply
  , worthApply
  , vars
  ) where

import Data.Data.Lens (biplate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Titan.Prelude
import Titan.TT

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

apply :: (Substitutable a, Data t) => Subst a -> t -> t
apply subst = over biplate (apply' subst)

worthApply :: Subst a -> Set (Id a) -> Bool
worthApply (Subst map) set = not (Map.keysSet map `Set.disjoint` set)

occurs :: (Substitutable a, Data t) => Id a -> t -> Bool
occurs id a = id `elem` vars topLevel a

vars :: forall a t. (Substitutable a, Data t) => Level -> t -> Set (Id a)
vars lv = view (biplate.to (vars' lv))

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
