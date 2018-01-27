{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE TypeFamilies     #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
module Lare where

import           Data.Function                ((&))
import           Data.List                    (nub, (\\))
import           Data.Monoid                  ((<>))

import           Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Debug.Trace

import Dep (Dom(..), Annot)



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


data Top a b = Top a [Tree b]
  deriving Show

data Tree a = Tree a [Tree a]
  deriving Show








--- * Loop -----------------------------------------------------------------------------------------------------------

data Loop v e = Loop
  { program :: Cfg (V v) e
  , loopid  :: Annot e
  , outer   :: [v]
  , inner   :: [v]
  , cuts    :: [v] }

type Program v e = Top (Cfg (V v) e) (Loop v e)






--- * Attribute Domain -----------------------------------------------------------------------------------------------

identity' :: Dom st e -> e
identity' Dom{..} = identity ctx

concatenate', alternate' :: Dom st e -> Edge v e -> Edge v e -> Edge v e
concatenate' Dom{..} = lift2 (concatenate ctx)
alternate' Dom{..}   = lift2 (alternate ctx)

closure', iterate' :: Dom st e -> Maybe (Annot e) -> Edge v e -> Edge v e
closure' Dom{..} a e = lift1 (closure ctx a) e
iterate' Dom{..} a e = lift1 (iterate ctx a) e

-- --- * Rip ------------------------------------------------------------------------------------------------------------


type T v e = Cfg v e -> Cfg v e

ripOne :: Eq v => Dom st e -> Maybe (Annot e) -> v -> T v e
ripOne dom a v cfg =
  let
  (vvs, uvs, vws, uws)
    = partition3
      (\e -> src e == v && dst e == v)
      (\e -> dst e == v)
      (\e -> src e == v) cfg
  in
  mergeParallel (alternate' dom) $ uws ++ chainAll (combinator vvs) uvs vws

  where

  compose' = concatenate' dom

  combinator [] e1 e2 = e1 `compose'` e2
  combinator es e1 e2 = e1 `compose'` (closure' dom a) (foldr1 (alternate' dom) es) `compose'` e2

  chainAll k es ds = [ k e1 e2 | e1 <- es, e2 <- ds ]

  mergeParallel k = foldr (mergeOne k) []

  mergeOne _ e1 []                         = [e1]
  mergeOne k e1 (e2:es)
    | src e1 == src e2 && dst e1 == dst e2 = k e1 e2: es
    | otherwise                            = e2 : mergeOne k e1 es

rip :: Eq v => Dom st e -> Maybe (Annot e) -> [v] -> T v e
rip dom a vs cfg = foldr (ripOne dom a) cfg vs

ripWith :: Eq v => Dom st e -> Maybe (Annot e) -> [v] -> T v e
ripWith dom a vs cfg = iterate' dom a <$> (rip dom a) vs cfg



convert dom (Top p ps) = Top p' ps'
  where
  ps' = map (convert' dom) ps
  p' =
    p
    & mappend (concatMap (\(Tree es _) -> es) ps')
    & debug "T:append subtrees"
    & mappend [ edge (V v)   (identity' dom) (In v)  | v <- inner ]
    & mappend [ edge (Out v) (identity' dom) (V v) | v <- inner ]
    & debug "T:add inner ports subtrees"
    & debug "T:rip inner ports"
    & rip dom Nothing [In v  | v <- inner ]
    & rip dom Nothing [Out v | v <- inner ]
    & debug "T:rip inner ports"
    & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
    & \g -> traceShow (nodes g) g
    & \g -> traceShow (sources g) g
    & \g -> traceShow (sinks g) g
    & \g -> rip dom Nothing (nodes g \\ (sources g ++ sinks g)) g
    & debug "result"
    where inner = concatMap (\(Tree l _) -> outer l) ps


convert' :: (Eq v, Show v, Show e, Pretty e) => Dom st e -> Tree (Loop v e) -> Tree [Edge (V v) e]
convert' dom (Tree Loop{..} ps) = Tree p' ps'
  where
  ps' = map (convert' dom) ps
  p' =
    program
      & debug "cfg"
      & mappend (concatMap (\(Tree es _) -> es) ps')
      & debug "add subprogram"
      & mappend [ edge (V v)   (identity' dom) (In v)  | v <- inner ]
      & mappend [ edge (Out v) (identity' dom) (V v) | v <- inner ]
      & debug "add inner ports"
      & rip dom (Just loopid) [In v  | v <- inner ]
      & rip dom (Just loopid) [Out v | v <- inner ]
      & debug "rip inner nodes"
      & mappend [ edge (In v) (identity' dom) (V v)  | v <- outer ]
      & mappend [ edge (V v) (identity' dom) (Out v) | v <- outer ]
      & debug "add outer ports"
      & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
      -- & \g -> loop foldr (\v g' -> trace ("rip\n" ++ ppcfg g') ripOne v g') g (nodes g \\ (sources g ++ sinks g))
      & \g -> ripWith dom (Just loopid) (nodes g \\ (sources g ++ sinks g)) g
      & debug "rip internal nodes"

debug s cfg = trace ("[" ++ s ++ "]\n" ++ ppcfg cfg) cfg


-- --- * Util -----------------------------------------------------------------------------------------------------------

partition3 :: (a -> Bool) -> (a -> Bool) -> (a -> Bool) -> [a] -> ([a],[a],[a],[a])
partition3 p1 p2 p3 = foldr select ([],[],[],[]) where
  select x ~(xs1,xs2,xs3,xs4)
    | p1 x       = (x:xs1, xs2,   xs3,   xs4)
    | p2 x       = (xs1,   x:xs2, xs3,   xs4)
    | p3 x       = (xs1,   xs2,   x:xs3, xs4)
    | otherwise  = (xs1,   xs2,   xs3,   x:xs4)



--- *  RE ------------------------------------------------------------------------------------------------------------

type instance Annot (RE a) = Int

data RE a
  = Sym a
  | Epsilon
  | Concatenate (RE a) (RE a)
  | Alternate (RE a) (RE a)
  | Star (RE a)
  | Iterate Int (RE a)
  deriving Show

rex :: Dom () (RE a)
rex = Dom
  { ctx         = ()
  , identity    = const Epsilon
  , concatenate = const Concatenate
  , alternate   = const Alternate
  , closure     = const (\_ -> Star)
  , iterate     = (\_ x e -> case x of {Just i -> Iterate i e; Nothing -> error "err"})
  }


ppcfg :: (Pretty e, Show v, Show e) => Cfg v e -> String
ppcfg = unlines . map k
  where k e = show (src e) ++ "\t~>\t" ++ show (dst e) ++ "\t\t" ++ (show $ pretty (att e))

ex1 =
  Top
    [a,b,e]
    [ Tree
      Loop
      { program     = [c,d]
      , loopid      = 1
      , outer       = ['C','B']
      , inner       = []
      , cuts        = ['c'] }
      []
    ]
  where
    a = edge (V 'I') (Sym 'a') (V 'A')
    b = edge (V 'A') (Sym 'b') (V 'B')
    d = edge (V 'C') (Sym 'd') (V 'B')
    c = edge (V 'B') (Sym 'c') (V 'C')
    e = edge (V 'C') (Sym 'e') (V 'F')

--- * Pretty ---------------------------------------------------------------------------------------------------------

render :: Pretty a => a -> String
render = show . pretty

prettyTrees [] = PP.empty
prettyTrees ts = (PP.vcat $ zipWith (<>) (repeat $ PP.text "+ ") (map (PP.align . pretty) ts))

instance (Pretty a, Pretty b) => Pretty (Top a b) where
  pretty (Top t []) = pretty t
  pretty (Top t ts) = pretty t PP.<$$> prettyTrees ts

instance Pretty a => Pretty (Tree a) where
  pretty (Tree t []) = pretty t
  pretty (Tree t ts) = pretty t PP.<$> prettyTrees ts


instance Pretty (RE Char) where
  pretty (Sym c)                 = PP.char c
  pretty Epsilon                 = PP.char '_'
  pretty (Concatenate Epsilon a) = pretty a
  pretty (Concatenate a Epsilon) = pretty a
  pretty (Concatenate a b)       = pretty a <> pretty b
  pretty (Alternate a b)         = PP.parens $ pretty a <> PP.char '|' <> pretty b
  pretty (Star (Sym c))          = PP.char c <> PP.char '*'
  pretty (Star a)                = PP.parens (PP.pretty a) <> PP.char '*'
  pretty (Iterate i a)           = PP.brackets $ PP.int i <> PP.space <> PP.pretty a


instance {-# Overlapping #-} (Pretty v, Pretty e) => Pretty [Edge v e] where
  pretty = PP.vcat . map pretty

instance (Pretty v, Pretty e) => Pretty (Edge v e) where
  pretty Edge{..} = pretty src <> PP.string "\t ~> \t" <> pretty dst <> PP.string " \t " <> pretty att

instance Pretty v => Pretty (V v) where
  pretty (V v)   = pretty v
  pretty (In v)  = PP.char '>' <> pretty v
  pretty (Out v) = PP.char '<' <> pretty v

