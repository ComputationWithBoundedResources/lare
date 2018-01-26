{-# LANGUAGE RecordWildCards, TypeOperators, FlexibleInstances #-}
module Lare where

import Data.List ((\\), nub)
import Data.Function ((&))
import Data.Monoid ((<>))

import Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import Debug.Trace


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
sources cfg = nub (fmap src cfg) \\ nub (fmap dst cfg)

sinks :: Eq v => Cfg v e -> [v]
sinks cfg = nub (fmap dst cfg) \\ nub (fmap src cfg)

data V v = V v | Out v | In v
  deriving (Eq, Ord, Show)



--- * Program --------------------------------------------------------------------------------------------------------

data Top v e = Top (Cfg (V v) e) [Tree v e]
  deriving Show

data Tree v e = Tree
  { program     :: Cfg (V v) e
  , loopid      :: Int
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
  loop      :: Int -> e -> e

compose', alternate' :: Att e => Edge v e -> Edge v e -> Edge v e
compose'   = lift2 compose
alternate' = lift2 alternate

closure' :: Att e => Edge v e -> Edge v e
closure' = lift1 closure

loop' :: Att e => Int ->  Edge v e -> Edge v e
loop' i    = lift1 $ loop i

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
      (\e -> dst e == v)
      (\e -> src e == v) cfg
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

ripWith :: (Eq v, Att e) => Int -> [v] -> T v e
ripWith i vs cfg = loop' i <$> rip vs cfg


convert :: (Eq v, Att e, Show v, Show e, Pretty e) => Top v e -> Cfg (V v) e
convert (Top p ps) =
  p
    & mappend (concatMap convert' ps)
    & debug "T:append subtrees"
    & mappend [ edge (V v) epsilon (In v)  | v <- inner ]
    & mappend [ edge (Out v) epsilon (V v) | v <- inner ]
    & debug "T:add inner ports subtrees"
    & debug "T:rip inner ports"
    & rip [In v  | v <- inner ]
    & rip [Out v | v <- inner ]
    & debug "T:rip inner ports"
    & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
    & \g -> traceShow (nodes g) g
    & \g -> traceShow (sources g) g
    & \g -> traceShow (sinks g) g
    & \g -> rip (nodes g \\ (sources g ++ sinks g)) g
    & debug "result"
  where inner = concatMap outer ps

convert' :: (Eq v, Att e, Show v, Show e, Pretty e) => Tree v e -> Cfg (V v) e
convert' Tree{..}
  | null program = []
  | otherwise    = trace ("> tree\n" ++ ppcfg p ++ "<\n") p
    where 
    p = 
      program
        & debug "cfg"
        & mappend (concatMap convert' subprograms)
        & debug "add subprogram"
        & mappend [ edge (V v) epsilon (In v)  | v <- inner ]
        & mappend [ edge (Out v) epsilon (V v) | v <- inner ]
        & debug "add inner ports"
        & rip [In v  | v <- inner ]
        & rip [Out v | v <- inner ]
        & debug "rip inner nodes"
        & mappend [ edge (In v) epsilon (V v)  | v <- outer ]
        & mappend [ edge (V v) epsilon (Out v) | v <- outer ]
        & debug "add outer ports"
        & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
        -- & \g -> loop foldr (\v g' -> trace ("rip\n" ++ ppcfg g') ripOne v g') g (nodes g \\ (sources g ++ sinks g))
        & \g -> ripWith loopid (nodes g \\ (sources g ++ sinks g)) g
        & debug "rip internal nodes"

debug s cfg = trace ("[" ++ s ++ "]\n" ++ ppcfg cfg) cfg


--- * Util -----------------------------------------------------------------------------------------------------------

partition3 :: (a -> Bool) -> (a -> Bool) -> (a -> Bool) -> [a] -> ([a],[a],[a],[a])
partition3 p1 p2 p3 = foldr select ([],[],[],[]) where
  select x ~(xs1,xs2,xs3,xs4)
    | p1 x       = (x:xs1, xs2,   xs3,   xs4)
    | p2 x       = (xs1,   x:xs2, xs3,   xs4)
    | p3 x       = (xs1,   xs2,   x:xs3, xs4)
    | otherwise  = (xs1,   xs2,   xs3,   x:xs4)



--- *  RE ------------------------------------------------------------------------------------------------------------

data RE a
  = Sym a 
  | Epsilon 
  | Concatenate (RE a) (RE a) 
  | Alternate (RE a) (RE a) 
  | Star (RE a) 
  | Loop Int (RE a)
  deriving Show

instance Pretty (RE Char) where
  pretty (Sym c)                 = PP.char c
  pretty Epsilon                 = PP.char '_'
  pretty (Concatenate Epsilon a) = pretty a
  pretty (Concatenate a Epsilon) = pretty a
  pretty (Concatenate a b)       = pretty a <> pretty b
  pretty (Alternate a b)         = PP.parens $ pretty a <> PP.char '|' <> pretty b
  pretty (Star (Sym c))          = PP.char c <> PP.char '*'
  pretty (Star a)                = PP.parens (PP.pretty a) <> PP.char '*'
  pretty (Loop i a)              = PP.brackets $ PP.int i <> PP.space <> PP.pretty a


-- instance Show a => Show (RE a) where
--   show (Sym a)                 = show a
--   show Epsilon                 = "_"
--   show (Concatenate Epsilon b) = show b
--   show (Concatenate a Epsilon) = show a
--   show (Concatenate a b)       = show a ++ show b
--   show (Alternate Epsilon b)   = "(_|" ++ show b ++ ")"
--   show (Alternate a Epsilon)   = "(" ++ show a ++ "|_)"
--   show (Alternate a b)         = "(" ++ show a ++ "|" ++ show b ++ ")"
--   show (Star a)                = "(" ++ show a ++ show ")*"
--   show (Loop i a)              = "["++ show i ++ " " ++ show a ++ "]"


instance Att (RE v) where
  epsilon   = Epsilon
  compose   = Concatenate
  alternate = Alternate
  closure   = Star
  loop      = Loop



ppcfg :: (Pretty e, Show v, Show e) => Cfg v e -> String
ppcfg = unlines . map k 
  where k e = show (src e) ++ "\t~>\t" ++ show (dst e) ++ "\t\t" ++ (show $ pretty (att e))

ex1 :: Top Char (RE Char)
ex1 = 
  Top 
    [a,b,e]
    [ Tree 
      { program     = [c,d]
      , loopid      = 1
      , outer       = ['C','B']
      , inner       = []
      , cuts        = ['c']
      , subprograms = [] }
    ]
  where
    a = edge (V 'I') (Sym 'a') (V 'A')
    b = edge (V 'A') (Sym 'b') (V 'B')
    d = edge (V 'C') (Sym 'd') (V 'B')
    c = edge (V 'B') (Sym 'c') (V 'C')
    e = edge (V 'C') (Sym 'e') (V 'F')

