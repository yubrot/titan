module Titan.Prelude
  ( module Prelude
  , module Control.Applicative
  , module Control.Arrow
  , module Control.Lens
  , module Control.Monad
  , module Control.Monad.Except
  , module Control.Monad.Reader
  , module Control.Monad.Writer
  , module Control.Monad.State
  , module Data.Data
  , module Data.Either
  , module Data.Foldable
  , module Data.List.NonEmpty
  , module Data.Map
  , module Data.Maybe
  , module Data.Set
  , module Data.Traversable
  , module Data.Void
  , module Debug.Trace
  , modifyM
  , nubOrd
  ) where

import Prelude
import Control.Applicative
import Control.Arrow
import Control.Lens hiding (Level)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer hiding (Alt)
import Control.Monad.State
import Data.Data hiding (DataType, typeOf)
import Data.Either
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import Data.Maybe
import Data.Set (Set)
import Data.Traversable
import Data.Void
import Debug.Trace
import qualified Data.Set as Set

modifyM :: MonadState s m => (s -> m s) -> m ()
modifyM f = get >>= f >>= put

nubOrd :: Ord a => [a] -> [a]
nubOrd = go mempty
 where
  go set = \case
    x:xs | Set.member x set -> go set xs
         | otherwise -> x : go (Set.insert x set) xs
    [] -> []
