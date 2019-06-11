module Titan.FunctionalDependency where

import Data.Data.Lens (biplate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Titan.Prelude
import Titan.Error
import Titan.TT
import Titan.Scope

tv :: (FVar a, Data t) => t -> [Id a]
tv = view (biplate.to tv')

class FVar a where
  tv' :: Type -> [Id a]

instance FVar Type where
  tv' t = [id | TVar id _ _ <- universe t]

instance FVar Parameter where
  tv' t = [id | TGen id <- universe t]

-- J^+_F is the smallest set such that:
-- J \subseteq J^+_F ; and
-- If (X \leadsto Y) \in F , and X \subseteq J^+_F , then Y \subseteq J^+_F
closure :: Set (Id a) -> [Fundep a] -> Set (Id a)
closure tvs fundeps = case find induce fundeps of
  Just (_ :~> y) -> closure (foldr Set.insert tvs y) fundeps
  Nothing -> tvs
 where
  induce (x :~> y) = any (`Set.notMember` tvs) y && all (`Set.member` tvs) x

-- F_C = \{ TV(t_X) \leadsto TV(t_Y) \mid (C \: t) \in P, (X \leadsto Y) \in F_C \}
inducedFundeps :: forall a m. (FVar a, MonadReader Scope m, MonadError Error m) => [Constraint] -> m [Fundep a]
inducedFundeps ctx = do
  fss <- forM ctx $ \case
    CClass id args -> do
      cls <- resolveUse' id
      let t = indexParams (cls^.parameters) args
      return [tv (t x) :~> tv (t y) | x :~> y <- cls^.fundeps]
  return $ concat fss

-- t_X
indexParams :: Functor f => [Parameter] -> [a] -> f (Id Parameter) -> f a
indexParams params xs = fmap (assocs Map.!)
 where
  assocs = Map.fromList [(identity p, x) | (p, x) <- zip params xs]
