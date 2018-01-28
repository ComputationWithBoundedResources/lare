{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE TypeFamilies     #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
module Lare.Analysis where

import           Data.Function                ((&))
import           Data.List                    (nub, (\\))
import           Data.Monoid                  ((<>))

import           Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Debug.Trace

import Lare.Domain
import Lare.RE
import           Lare.Flow (F, E ((:>)))
import qualified Lare.Flow as F



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
  { program :: [Edge v e]
  , loopid  :: Annot e
  , outer   :: [v]
  , cuts    :: [Edge v e] }

inner ts = concatMap (\(Tree l _) -> outer l) ts


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



convert :: (Eq v, Pretty e, Show v, Show e) =>
  Dom st e
  -> Top [Edge (V v) e] (Loop (V v) e)
  -> Top (Cfg (V v) e) [Edge (V v) e]
convert dom (Top p ps) = Top p' ps'
  where
  ps' = map (convert' dom) ps
  p' =
    p
    & mappend (concatMap (\(Tree es _) -> es) ps')
    & debug "T:append subtrees"
    & mappend [ edge (V v)   (identity' dom) (In v)  | Out v <- inner ps ]
    & mappend [ edge (Out v) (identity' dom) (V v) | Out v <- inner ps ]
    & debug "T:add inner ports subtrees"
    & debug "T:rip inner ports"
    & rip dom Nothing [In v  | Out v <- inner ps ]
    & rip dom Nothing [Out v | Out v <- inner ps ]
    & debug "T:rip inner ports"
    & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
    & \g -> traceShow (nodes g) g
    & \g -> traceShow (sources g) g
    & \g -> traceShow (sinks g) g
    & \g -> rip dom Nothing (nodes g \\ (sources g ++ sinks g)) g
    & debug "result"


convert' :: (Show e, Show v, Pretty e, Eq v) =>
  Dom st e -> Tree (Loop (V v) e) -> Tree [Edge (V v) e]
convert' dom (Tree Loop{..} ps) = Tree p' ps'
  where
  ps' = map (convert' dom) ps
  p' =
    program
      & debug "cfg"
      & mappend (concatMap (\(Tree es _) -> es) ps')
      & debug "add subprogram"
      & mappend [ edge (V v)   (identity' dom) (In v)  | Out v <- inner ps ]
      & mappend [ edge (Out v) (identity' dom) (V v) | Out v <- inner ps]
      & debug "add inner ports"
      & rip dom (Just loopid) [In v  | Out v <- inner ps ]
      & rip dom (Just loopid) [Out v | Out v <- inner ps ]
      & debug "rip inner nodes"
      & mappend [ edge (In v) (identity' dom) (V v)  | Out v <- outer ]
      & mappend [ edge (V v) (identity' dom) (Out v) | Out v <- outer ]
      & debug "add outer ports"
      & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
      -- & \g -> loop foldr (\v g' -> trace ("rip\n" ++ ppcfg g') ripOne v g') g (nodes g \\ (sources g ++ sinks g))
      & \g -> ripWith dom (Just loopid) (nodes g \\ (sources g ++ sinks g)) g
      & debug "rip internal nodes"

debug s cfg = trace ("[" ++ s ++ "]\n" ++ ppcfg cfg) cfg

--- * Intermediate Representation ------------------------------------------------------------------------------------

 
data Var v = Var v | Ann v | Counter | K | Huge deriving (Eq, Ord, Show)


data Bound var         = Unknown | Sum [(Int, var)] deriving Show
newtype Assignment var = Assignment [ (var, Bound var) ] deriving Show

type Program v e = Top [Edge (V v) e] (Loop (V v) e)

type instance Annot (Assignment v) = (v, Bound v)


-- TODO:
-- * implement iterate correct
-- * implement closure; Ann v = Bound compose X = X + Bound compose Invariant

-- toFlow' :: [Var v] -> Tree (Loop n (Assignment (Var v))) -> Tree (Loop n (F.F (Var v)))
toFlow' vs t = go t
  where
    k es = [ e { att = withAssignment vs (att e) } | e <- es ]
    g (v, Unknown) = (v, [(F.Identity, Huge :> Counter)])
    g (v, Sum bs)  = (v, (F.Additive, Counter :> Counter) : [ (F.fromK k, v :> b) | (k,b) <- bs ])
    go (Tree Loop{..} ts) = 
      Tree
        Loop
          { program = k program 
          , loopid  = g loopid
          , outer   = outer
          , cuts    = k cuts }
        (map go ts)


fromAssignment :: Assignment (Var v) -> [F.U (Var v)]
fromAssignment (Assignment as) = do
  (v,b) <- as
  case b of
    Unknown -> return (F.Identity, Huge :> v)
    Sum bs  -> [ (F.fromK k, v :> b) | (k,b) <- bs ]


withAssignment :: Ord v => [Var v] -> Assignment (Var v) -> F (Var v)
withAssignment vs a@(Assignment as) = F.complete $ idep ++ assign
  where
  idep   = [ (F.Identity, v :> v) | v <- (vs \\ [ v  | (v,_) <- as ]) ]
  assign = fromAssignment a
  

-- data Loop v e = Loop
--   { program :: [Edge v e]
--   , loopid  :: Annot e
--   , outer   :: [v]
--   , cuts    :: [Edge v e] }

--- * Util -----------------------------------------------------------------------------------------------------------

partition3 :: (a -> Bool) -> (a -> Bool) -> (a -> Bool) -> [a] -> ([a],[a],[a],[a])
partition3 p1 p2 p3 = foldr select ([],[],[],[]) where
  select x ~(xs1,xs2,xs3,xs4)
    | p1 x       = (x:xs1, xs2,   xs3,   xs4)
    | p2 x       = (xs1,   x:xs2, xs3,   xs4)
    | p3 x       = (xs1,   xs2,   x:xs3, xs4)
    | otherwise  = (xs1,   xs2,   xs3,   x:xs4)





ppcfg :: (Pretty e, Show v, Show e) => Cfg v e -> String
ppcfg = unlines . map k
  where k e = show (src e) ++ "\t~>\t" ++ show (dst e) ++ "\t\t" ++ (show $ pretty (att e))


ex1 :: Program Char (RE Char)
ex1 =
  Top
    [a,b,e]
    [ Tree
      Loop
      { program     = [c,d]
      , loopid      = 1
      , outer       = [Out 'C', Out 'B']
      , cuts        = [] }
      []
    ]
  where
    a = edge (V 'I') (Sym 'a') (V 'A')
    b = edge (V 'A') (Sym 'b') (V 'B')
    d = edge (V 'C') (Sym 'd') (V 'B')
    c = edge (V 'B') (Sym 'c') (V 'C')
    e = edge (V 'C') (Sym 'e') (V 'F')

runex2 = convert (F.flow [1..5]) ex2

ex2 =
  Top
    [a,b,e]
    [ Tree
      Loop
      { program     = [c,d]
      , loopid      = (5, [])
      , outer       = [Out 'C', Out 'B']
      , cuts        = [] }
      []
    ]
  where
    a = edge (V 'I') (F.skip vs) (V 'A')
    b = edge (V 'A') (F.copy vs 1 3) (V 'B')
    c = edge (V 'B') (F.copy vs 2 3) (V 'C')
    d = edge (V 'C') (F.plus vs 3 1 2) (V 'B')
    e = edge (V 'C') (F.copy vs 4 3) (V 'F')
    vs = [1..5] :: [Int]

ex3 =
  Top
    [a,e]
    [ Tree
      Loop
      { program     = [d]
      , loopid      = (Var 'X', Sum [(1, Var 'j')])
      , outer       = [Out 2]
      , cuts        = [] }
      [ Tree 
        Loop 
          { program     = [b,c]
          , loopid      = (Var 'X', Sum [(1, Var 'j')])
          , outer       = [Out 3]
          , cuts        = [] }
        []
      ]
    ]
  where
    a = edge (V 1) (Assignment [ (v, Sum [(1, Var 'n')]) | v <- vs ]) (V 2)
    b = edge (V 2) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 3)
    c = edge (V 3) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 2)
    d = edge (V 3) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 2)
    e = edge (V 2) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 4)
    vs = [Var 'n', Var 'i', Var 'j']

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


instance {-# Overlapping #-} (Pretty v, Pretty e) => Pretty [Edge v e] where
  pretty = PP.vcat . map pretty

instance (Pretty v, Pretty e) => Pretty (Edge v e) where
  pretty Edge{..} = pretty src <> PP.string "\t ~> \t" <> pretty dst PP.<$$> PP.indent 2 (pretty att)

instance Pretty v => Pretty (V v) where
  pretty (V v)   = pretty v
  pretty (In v)  = PP.char '>' <> pretty v
  pretty (Out v) = PP.char '<' <> pretty v

