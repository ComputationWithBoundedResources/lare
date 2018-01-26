{-# LANGUAGE RecordWildCards, TypeOperators #-}
module Lare where

import Data.List ((\\), nub)
import Data.Function ((&))


--- * Cfg ------------------------------------------------------------------------------------------------------------

data Edge v e = Edge
  { src :: v
  , att :: e
  , dst :: v
  } deriving (Eq, Ord, Show)

edge :: v -> e -> v -> Edge v e
edge src att dst = Edge { src = src, att = att, dst = dst }

lift1 :: (e -> e) -> Edge v e -> Edge v e
lift1 k e = edge (src e) (k $ att e) (dst e)

lift2 :: (e1 -> e2 -> e) -> Edge v e1 -> Edge v e2 -> Edge v e
lift2 k e1 e2 = edge (src e1) (att e1 `k` att e2) (dst e2)

type Cfg v e = [Edge v e]

nodes :: Eq v => Cfg v e -> [v]
nodes cfg = nub $ fmap src cfg ++ fmap dst cfg

sources :: Eq v => Cfg v e ->  [v]
sources cfg = fmap src cfg \\ fmap dst cfg

sinks :: Eq v => Cfg v e -> [v]
sinks cfg = fmap dst cfg \\ fmap src cfg

data V v = V v | Out v | In v
  deriving (Eq, Ord, Show)



--- * Program --------------------------------------------------------------------------------------------------------

data Top v e = Top (Cfg (V v) e) [Tree v e]
  deriving Show

data Tree v e = Tree
  { program     :: Cfg (V v) e
  , outer       :: [v]
  , inner       :: [v]
  , cuts        :: [v]
  , subprograms :: [Tree v e] }
  deriving Show


draw :: (Show e, Show v) => Top e v -> [String]
draw (Top p ps) = ("P: " ++ show p)  : drawSubTrees ps where
  draw' t@Tree{} = ("p:" ++ show (program t) ++ " c: " ++ show (cuts t))  : drawSubTrees (subprograms t)
  shift first other = zipWith (++) (first : repeat other)
  drawSubTrees []     = []
  drawSubTrees [t]    = "|" : shift "`- " "   " (draw' t)
  drawSubTrees (t:ts) = "|" : shift "+- " "|  " (draw' t) ++ drawSubTrees ts


--- * Attribute Domain -----------------------------------------------------------------------------------------------

class Att e where
  epsilon   :: e
  compose   :: e -> e -> e
  alternate :: e -> e -> e
  closure   :: e -> e
  loop      :: e -> e

compose', alternate' :: Att e => Edge v e -> Edge v e -> Edge v e
compose'   = lift2 compose
alternate'   = lift2 alternate

closure' :: Att e => Edge v e -> Edge v e
closure' = lift1 closure

-- loop' :: Att e => Edge v e -> Edge v e -> Edge v e
-- loop'    = lift2 loop

loop' :: Att e => Edge v e -> Edge v e
loop'    = lift1 loop


--- * Rip ------------------------------------------------------------------------------------------------------------


type T v e = Cfg v e -> Cfg v e

-- alternate is semigroup
-- compose is monoid?

ripOne :: (Eq v, Att e) => v -> T v e
ripOne v cfg =
  let
  (vvs, uvs, vws, uws)
    = partition3
      (\e -> src e == v && dst e == v)
      (\e -> src e == v)
      (\e -> dst e == v) cfg
  in
  mergeParallel alternate' $ uws ++ chainAll (combinator vvs) uvs vws

  where


  combinator [] e1 e2 = e1 `compose'` e2
  combinator es e1 e2 = e1 `compose'` closure' (foldr1 alternate' es) `compose'` e2

  chainAll k es ds = [ k e1 e2 | e1 <- es, e2 <- ds ]

  mergeParallel k = foldr (mergeOne k) []

  mergeOne _ e1 []                         = [e1]
  mergeOne k e1 (e2:es)
    | src e1 == src e2 && dst e1 == dst e2 = k e1 e2: es
    | otherwise                            = e2 : mergeOne k e1 es

rip :: (Eq v, Att e) => [v] -> T v e
rip vs cfg = foldr ripOne cfg vs

ripWith :: (Eq v, Att e) => [v] -> T v e
ripWith vs cfg = loop' <$> rip vs cfg


convert :: (Eq v, Att e) => Top v e -> Cfg (V v) e
convert (Top p ps) =
  p
    & mappend (concatMap convert' ps)
    & mappend [ edge (V v) epsilon (In v)  | v <- inner ]
    & mappend [ edge (Out v) epsilon (V v) | v <- inner ]
    & rip [In v  | v <- inner ]
    & rip [Out v | v <- inner ]
  where inner = concatMap outer ps

convert' :: (Eq v, Att e) => Tree v e -> Cfg (V v) e
convert' Tree{..}
  | null program = []
  | otherwise    =
    program
      & mappend (concatMap convert' subprograms)
      & mappend [ edge (V v) epsilon (In v)  | v <- inner ]
      & mappend [ edge (Out v) epsilon (V v) | v <- inner ]
      & rip [In v  | v <- inner ]
      & rip [Out v | v <- inner ]
      & mappend [ edge (In v) epsilon (V v)  | v <- outer ]
      & mappend [ edge (V v) epsilon (Out v) | v <- outer ]
      & \g -> ripWith (nodes g \\ ([ In v | v <- outer ] ++ [ Out v | v <- outer ])) g




--- * Util -----------------------------------------------------------------------------------------------------------

partition3 :: (a -> Bool) -> (a -> Bool) -> (a -> Bool) -> [a] -> ([a],[a],[a],[a])
partition3 p1 p2 p3 = foldr select ([],[],[],[]) where
  select x ~(xs1,xs2,xs3,xs4)
    | p1 x       = (x:xs1, xs2,   xs3,   xs4)
    | p2 x       = (xs1,   x:xs2, xs3,   xs4)
    | p3 x       = (xs1,   xs2,   x:xs3, xs4)
    | otherwise  = (xs1,   xs2,   xs3,   x:xs4)



--- *  RE ------------------------------------------------------------------------------------------------------------

data RE v a 
  = Sym a 
  | Epsilon 
  | Concatenate (RE v a) (RE v a) 
  | Alternate (RE v a) (RE v a) 
  | Star (RE v a) 
  | Loop (RE v a)
  deriving Show

instance Att (RE v a) where
  epsilon   = Epsilon
  compose   = Concatenate
  alternate = Alternate
  closure   = Star
  loop      = Loop

ppcfg :: (Show v, Show e) => Cfg v e -> String
ppcfg = unlines . map k 
  where k e = show (src e) ++ "\t~>\t" ++ show (dst e) ++ "\t\t" ++ show (att e)

ex :: Top String (RE String String)
ex = 
  Top 
    [a,b,e]
    [ Tree 
      { program     = [c,d]
      , outer       = ["B","C"]
      , inner       = []
      , cuts        = ["c"]
      , subprograms = [] }
    ]
  where
    a = edge (V "I") Epsilon        (V "A")
    b = edge (V "A") (Sym "copy12") (V "B")
    c = edge (V "B") (Sym "E")      (V "C")
    d = edge (V "C") (Sym "sum352") (V "B")
    e = edge (V "C") (Sym "copy52") (V "F")


