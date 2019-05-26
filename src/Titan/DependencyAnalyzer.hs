module Titan.DependencyAnalyzer
  ( depGroups
  ) where

import Data.Graph (stronglyConnComp)
import Data.Data.Lens (biplate)
import Titan.Prelude

depGroups :: (Data a, Ord k, Typeable k) => [(k, a)] -> [[a]]
depGroups inputs = map toList sccs
 where
  edges = [(a, k, a^..biplate) | (k, a) <- inputs]
  sccs = stronglyConnComp edges
