module Titan.Row
  ( Fields
  , (+:>)
  , unifyLabels
  , pattern Row
  ) where

import Titan.Prelude
import Titan.TT
import qualified Data.Map as Map
import qualified Data.List.NonEmpty as NonEmpty

newtype Fields a = Fields (Map Label (NonEmpty a))
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

instance Semigroup (Fields a) where
  Fields a <> Fields b = Fields $ Map.unionWith (<>) a b

instance Monoid (Fields a) where
  mempty = Fields mempty

(+:>) :: Label -> a -> Fields a
l +:> a = Fields $ Map.singleton l (a :| [])

unifyLabels :: Fields a -> Fields a -> (Fields (a, a), Fields a, Fields a)
unifyLabels a b = go mempty (open a) (open b)
 where
  open (Fields a) = (mempty, Map.toAscList a)
  close (m, a) = Fields (m <> Map.fromAscList a)
  go u (ma, ass@((la, a):as)) (mb, bss@((lb, b):bs)) = case compare la lb of
    LT ->
      go u (Map.insert la a ma, as) (mb, bss)
    GT ->
      go u (ma, ass) (Map.insert lb b mb, bs)
    EQ ->
      let l = la
          us = NonEmpty.zip a b
          a' = NonEmpty.drop (length us) a
          b' = NonEmpty.drop (length us) b
          insertRest l (x:xs) = Map.insert l (x :| xs)
          insertRest _ [] = id
      in
      go (Map.insert l us u) (insertRest l a' ma, as) (insertRest l b' mb, bs)
  go u a b = (Fields u, close a, close b)

class Row a where
  row :: Prism' a (Fields a, a)

pattern Row :: Row a => Fields a -> a -> a
pattern Row r a <- (preview row -> Just (r, a))
  where Row r a = review row (r, a)

instance Row Type where
  row = prism apply unapply
   where
    apply (Fields a, r) = foldr (\(l, a) r -> foldr (TRowExtend l) r a) r (Map.assocs a)
    unapply = \case
      tv@(TVar _ (KRow KType) _) -> Right (mempty, tv)
      TEmptyRow -> Right (mempty, TEmptyRow)
      TRowExtend l a (Row r b) -> Right ((l +:> a) <> r, b)
      t -> Left t
