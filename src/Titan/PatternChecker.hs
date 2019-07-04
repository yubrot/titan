{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
module Titan.PatternChecker
  ( CheckResult(..)
  , check
  , uselessCheck
  , exhaustivenessCheck
  , Pat(..)
  , Tag(..)
  , Literal(..)
  , Name
  , Arity
  , Row
  , Matrix
  ) where

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Text as Text
import Titan.Prelude
import Titan.TT (Name, Arity, Literal(..))

data CheckResult
  = Useless [Pat]
  | NonExhaustive [Row]
  | Complete
  deriving (Eq, Ord, Show, Typeable)

check :: [Row] -> CheckResult
check rows = either id id $ do
  mat <- foldM uselessCheck' [] rows
  exhaustivenessCheck' mat
  return Complete
 where
  uselessCheck' mat row = case uselessCheck mat row of
    Right mat -> return mat
    Left ps -> throwError $ Useless ps
  exhaustivenessCheck' mat = case exhaustivenessCheck mat of
    [] -> return ()
    rows -> throwError $ NonExhaustive rows

uselessCheck :: Matrix -> Row -> Either [Pat] Matrix
uselessCheck mat row =
  let mat' = filter (not . (## row)) mat in
  case u' (dotMatrixP mat') (dotMatrixP [row]) of
    E [] -> Right $ filter (\row' -> u [row] [row']) mat @. [row]
    E ps -> Left ps
    T -> Left row

exhaustivenessCheck :: Matrix -> [Row]
exhaustivenessCheck mat = i mat (length (head mat))

data Pat
  = Constructor Tag [Pat]
  | Or Pat Pat
  | Wildcard
  deriving (Eq, Ord, Typeable)

data Tag
  = TagLit Literal
  | TagClosed (Name, Arity) [(Name, Arity)]
  deriving (Eq, Ord, Typeable)

tagArity :: Tag -> Arity
tagArity = \case
  TagLit _ -> 0
  TagClosed (_, arity) _ -> arity

data TagSiblings
  = Finite [Tag]
  | Infinite

tagSiblings :: Tag -> TagSiblings
tagSiblings = \case
  TagLit _ -> Infinite
  TagClosed _ vs -> Finite [TagClosed v vs | v <- vs]

isComplete :: Set Tag -> Bool
isComplete tags = case Set.lookupMin tags of
  Just (TagClosed _ vs) -> Set.size tags == length vs
  _ -> False

type Row = [Pat]

type Matrix = [Row]

isRowEmpty :: Matrix -> Bool
isRowEmpty = null

isColumnEmpty :: Matrix -> Bool
isColumnEmpty = all null

collectTags :: Matrix -> Set Tag
collectTags m = foldr put Set.empty (map head m)
 where
  put = \case
    Constructor t _ -> Set.insert t
    Or a b -> put a . put b
    Wildcard -> id

-- Row-wise concat: [[..], [..]] ++ [[..], [..]]
(@.) :: Matrix -> Matrix -> Matrix
a @. b = a ++ b

-- Column-wise concat: [[..] ++ [..], [..] ++ [..]]
(&.) :: Matrix -> Matrix -> Matrix
a &. b = zipWith (++) a b

-- Erase column j
(\.) :: Matrix -> Int -> Matrix
mat \. j  = map (\row -> take j row ++ drop (j+1) row) mat

-- Reduce mat to its column j
(//.) :: Matrix -> Int -> Matrix
mat //. j = map (\row -> [row !! j]) mat

instance Show Pat where
  show = \case
    Constructor tag [] -> show tag
    Constructor tag ps -> "(" ++ show tag ++ " " ++ show ps ++ ")"
    Or p1 p2 -> "(" ++ show p1 ++ " | " ++ show p2 ++ ")"
    Wildcard -> "_"
  showList = \case
    [] -> id
    ps -> (foldr1 (\a b -> a ++ " " ++ b) (map show ps) ++)

instance Show Tag where
  show = \case
    TagLit l -> case l of
      LInteger i -> show i
      LChar c -> show c
      LFloat d -> show d
      LString s -> show s
    TagClosed (name, _) _ -> Text.unpack name

class Incompatible a where
  (##) :: a -> a -> Bool

instance Incompatible Row where
  ps ## vs = or $ zipWith (##) ps vs

instance Incompatible Pat where
  Constructor t ps ## Constructor t' vs = t /= t' || (ps ## vs)
  Or p1 p2         ## v                 = (p1 ## v) && (p2 ## v)
  _                ## _                 = False

-- Is vector q useful with respect to matrix P?
-- (Exists some vector v where P does not relates v and q relates v)
u :: Matrix -> Matrix -> Bool
u p q = if
  | isRowEmpty p -> True
  | isColumnEmpty p -> False
  | otherwise -> case q of
      [Constructor t _:_] ->
        u (s t p) (s t q)
      [Wildcard:qn] ->
        let tags = collectTags p in
        if isComplete tags
          then any (\t -> u (s t p) (s t q)) tags
          else u (d p) [qn]
      [Or r1 r2:qn] ->
        u p [r1 : qn] || u p [r2 : qn]
      _ ->
        error "assert (length q == 1 && all (\row -> length row == length (head q)) p)"

-- Extract specialized rows for t.
s :: Tag -> [Row] -> [Row]
s t rows = rows >>= \case
  [] -> []
  p1:pn -> case p1 of
    Constructor t' rs
      | t == t' -> [rs ++ pn]
      | otherwise -> [] -- unrelated
    Wildcard -> [replicate (tagArity t) Wildcard ++ pn]
    Or r1 r2 -> s t [r1 : pn, r2 : pn]

-- Inverse of s.
sInv :: Tag -> [Row] -> [Row]
sInv t rows = [Constructor t args : pn | row <- rows, let (args, pn) = List.splitAt (tagArity t) row]

-- Extract the new "default" rows of width n-1.
d :: [Row] -> [Row]
d rows = rows >>= \case
  [] -> []
  p1:pn -> case p1 of
    Constructor _ _ -> []
    Wildcard -> [pn]
    Or a b -> d [a : pn, b : pn]

-- Computes a pattern such that all the instances of p are non-matching values.
i :: Matrix -> Int -> [Row]
i p n = if
  | isRowEmpty p -> [replicate n Wildcard]
  | isColumnEmpty p -> []
  | otherwise ->
      let tags = collectTags p in
      if isComplete tags then do
        t <- toList tags
        sInv t $ i (s t p) (tagArity t + n - 1)
      else do
        tail <- i (d p) (n - 1)
        head <- case toList tags of
          [] -> return Wildcard
          tags@(t:_) -> case tagSiblings t of
            Infinite -> return Wildcard
            Finite siblings -> do
              t <- siblings List.\\ tags
              return $ Constructor t (replicate (tagArity t) Wildcard)
        return $ head : tail

type DotRow = (Row, Row, Row)

type DotMatrix = (Matrix, Matrix, Matrix)

dotMatrixP :: Matrix -> DotMatrix
dotMatrixP m = (m, map (const []) m, map (const []) m)

dotMatrixPQ :: Matrix -> Matrix -> DotMatrix
dotMatrixPQ m m' = (m, m', map (const []) m)

concatMapRows :: (DotRow -> [DotRow]) -> DotMatrix -> DotMatrix
concatMapRows f (ps, qs, rs) = unzip3 $ zip3 ps qs rs >>= f

shiftQ :: DotMatrix -> DotMatrix
shiftQ = concatMapRows $ \((p1:pn), q, r) -> return (pn, p1:q, r)

shiftR :: DotMatrix -> DotMatrix
shiftR = concatMapRows $ \((p1:pn), q, r) -> return (pn, q, p1:r)

data E = T | E [Pat]

u' :: DotMatrix -> DotMatrix -> E
u' (ps, qs, rs) (p, q, r) = case p of
  [p1:pn] -> case p1 of
    Constructor t ss ->
      u' (s' t (ps, qs, rs)) ([ss ++ pn], q, r)
    Wildcard
      | all ((== Wildcard) . head) ps ->
          u' (map tail ps, qs, rs) (map tail p, q, r)
      | otherwise ->
          u' (shiftQ (ps, qs, rs)) (shiftQ (p, q, r))
    Or _ _ ->
      u' (shiftR (ps, qs, rs)) (shiftR (p, q, r))
  [[]]
    | isColumnEmpty r -> if
        | u qs q -> E []
        | otherwise -> T
    | otherwise ->
        foldr orE (E []) $ map e [0..z-1]
       where
        e j = case (et1, et2) of
          (T, T) -> T
          (E a, E b) -> E (a ++ b)
          (E a, T) -> E (a ++ [t2])
          (T, E b) -> E ([t1] ++ b)
         where
          Or t1 t2 = head r !! j
          et1 = u' (dotMatrixPQ ((rs //. j)          ) (((rs \. j) &. qs)                   )) (dotMatrixPQ [[t1]] ((r \. j) &. q))
          et2 = u' (dotMatrixPQ ((rs //. j) @. [[t1]]) (((rs \. j) &. qs) @. ((r \. j) &. q))) (dotMatrixPQ [[t2]] ((r \. j) &. q))
        z = length $ head r
        orE _ T = T
        orE T _ = T
        orE (E a) (E b) = E (a ++ b)
  _ ->
    error "assert (length p == 1)"

s' :: Tag -> DotMatrix -> DotMatrix
s' t = concatMapRows $ \(p, q, r) -> fmap (\p' -> (p', q, r)) (s t [p])
