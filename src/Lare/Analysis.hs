-- | This module provides the \rip\ algorithm, which abstracts Flowchart programs to flow properties from start nodes
-- to exit nodes.
{-# LANGUAGE DeriveFoldable, DeriveFunctor, FlexibleInstances, RecordWildCards #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module Lare.Analysis where


import           Control.Monad                (unless)
import           Data.Function                ((&))
import           Data.Monoid                  ((<>))
import           Text.PrettyPrint.ANSI.Leijen (Doc, Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Lare.Domain                  (Dom)
import qualified Lare.Domain                  as D
import           Lare.Util

-- import           Debug.Trace

-- debug :: Pretty a => String -> a -> a
-- debug s cfg = trace ("[" ++ s ++ "]\n" ++ render (PP.indent 2 $ PP.align $ pretty cfg)) cfg

debug :: String -> a -> a
debug = const id

-- * Cfg

data Edge v e = Edge
  { src :: v
  , att :: e
  , dst :: v
  } deriving (Eq, Ord, Show, Functor)

edge :: v -> e -> v -> Edge v e
edge src att dst = Edge { src = src, att = att, dst = dst }

lift2 :: (e1 -> e2 -> e) -> Edge v e1 -> Edge v e2 -> Edge v e
lift2 k e1 e2 = edge (src e1) (att e1 `k` att e2) (dst e2)

-- | A @Cfg v e@ is a multi-edge graph with vertices @v@ and edge-labels @e@.
type Cfg v e = [Edge v e]

nodes :: Ord v => Cfg v e -> [v]
nodes cfg = nub $ fmap src cfg ++ fmap dst cfg

sources :: Ord v => Cfg v e ->  [v]
sources cfg = nub (fmap src cfg) \\ nub (fmap dst cfg)

sinks :: Ord v => Cfg v e -> [v]
sinks cfg = nub (fmap dst cfg) \\ nub (fmap src cfg)

innards :: Ord v => Cfg v e -> [v]
innards cfg = nodes cfg \\ (sources cfg ++ sinks cfg)

-- | A wrapper for the vertex type.
data Vtx v
  = V v -- ^ standard vertices
  | O v -- ^ denotes an output port for subprograms
  | I v -- ^ denotes an input port for subprograms
  deriving (Eq, Ord, Show)


-- * Program

data Top a b = Top a [Tree b]
  deriving (Show, Functor, Foldable)

data Tree a = Tree a [Tree a]
  deriving (Show, Functor, Foldable)

-- | A Simp
data SimpleLoop v e = SimpleLoop
  { program' :: [Edge v e]
  , loopid'  :: e }
  deriving Show

-- | A Loop is an 'SimpleLoop' with additional information.
data Loop v e = Loop
  { program :: [Edge v e]
  , loopid  :: e
  , outer   :: [v]
  , inflow  :: [v]
  , outflow :: [v] }
  deriving (Show, Functor)

-- | Expected input of `rip`.
--
-- A program is a rooted tree with following syntactical properties:
--
--   * The root contains the whole CFG, with at least one start and exit node (ie. nodes with no incoming and outgoing edges respectively).
--   * The CFG of the children are distinct (proper) subsets.
--   * The loopid is unique.
--
type Program v e = Top  [Edge (Vtx v) e] (Loop (Vtx v) e)

-- | Output of `rip`.
type Proof   v e = Tree [Edge (Vtx v) e]

toLoop :: (Ord v, Ord e) => Cfg v e -> [v] -> (SimpleLoop v e) -> Loop (Vtx v) e
toLoop cfg ns SimpleLoop{program'=cfg',..} =
  Loop
    { program = [ edge (V $ src e) (att e) (V $ dst e) | e <- cfg'  ]
    , loopid  = loopid'
    , outer   = [ V v | v <- ns `intersect` nodes cfg' ]
    , inflow  = nub [ V (src e1) | e1 <- cfg', e2 <- cfg \\ cfg', dst e2 == src e1 ]
    , outflow = nub [ V (dst e1) | e1 <- cfg', e2 <- cfg \\ cfg', dst e1 == src e2 ] }

-- | Transforms a loop structure with `SimpleLoop` to a program that can be applied to `rip`.
toProgram :: (Ord v, Ord e) => Top [Edge v e] (SimpleLoop v e) -> Program v e
toProgram (Top cfg ts) =
  Top
    [ edge (V $ src e) (att e) (V $ dst e) | e <- cfg  ]
    (fmap (toLoop cfg $ nodes cfg) `fmap` ts)

inner, innerflows, outerflows :: Ord v => [Tree (Loop v e)] -> [v]
inner ts = nub $ concatMap (\(Tree l _) -> outer l) ts
innerflows ts = nub $ concatMap (\(Tree l _) -> inflow l) ts
outerflows ts = nub $ concatMap (\(Tree l _) -> outflow l) ts

cutset :: (Ord v, Ord e) => [Edge v e] -> [Tree (Loop v e)] -> [Edge v e]
cutset p ts = p \\ concatMap (\(Tree l _) -> program l) ts


-- * Abstract Domain

unity :: Dom st e -> e
unity D.Dom{..} = unity ctx

alternate :: Dom st e -> Edge v e -> Edge v e -> Edge v e
alternate D.Dom{..} = lift2 (alternate ctx)

rip :: Dom st e -> [Edge v e] -> Edge v e -> Edge v e -> Edge v e
rip D.Dom{..} es      = lift2 (rip ctx [att e | e <- es])

ripWith :: Dom st e -> e -> [Edge v e] -> Edge v e -> Edge v e -> Edge v e
ripWith D.Dom{..} a es = lift2 (ripWith ctx a [att e | e <- es])

closeWith :: Dom st e -> e -> Edge v e -> Edge v e
closeWith D.Dom{..} a = fmap (closeWith ctx a)


-- * Rip


type T v e = Cfg v e -> Cfg v e

ripOne :: Eq v => Dom st e -> (Cfg v e -> Edge v e -> Edge v e -> Edge v e) -> v -> T v e
ripOne dom ripper v cfg =
  let
  (vvs, uvs, vws, uws)
    = partition3
      (\e -> src e == v && dst e == v)
      (\e -> dst e == v)
      (\e -> src e == v) cfg
  in
  mergeParallel (alternate dom) $ uws ++ chainAll (ripper vvs) uvs vws
  where

  chainAll k es ds = [ k e1 e2 | e1 <- es, e2 <- ds ]

  mergeParallel k = foldr (mergeOne k) []

  mergeOne _ e1 []                         = [e1]
  mergeOne k e1 (e2:es)
    | src e1 == src e2 && dst e1 == dst e2 = k e1 e2: es
    | otherwise                            = e2 : mergeOne k e1 es

ripAll :: Eq v => Dom st e -> [v] -> T v e
ripAll dom vs cfg = foldr (ripOne dom $ rip dom) cfg vs

ripAllWith :: Eq v => Dom st e -> e -> [v] -> T v e
ripAllWith dom a vs cfg = foldr (ripOne dom $ ripWith dom a) cfg vs

convertN :: (Show e, Show v, Pretty e, Ord v, Ord e, Pretty v) => Dom st e -> Tree (Loop (Vtx v) e) -> Tree [Edge (Vtx v) e]
convertN dom (Tree Loop{program = cfg,..} []) = Tree cfg' [] where
  cfg' =
    cfg
    & debug "CFG"
    & mappend [ edge (I v) (unity dom) (V v) | V v <- inflow ]
    & mappend [ edge (V v) (unity dom) (O v) | V v <- outflow ]
    & debug "Add Outer Ports"
    & (ripAllWith dom loopid =<< innards)
    & debug "Rip internal nodes"
    & fmap (closeWith dom loopid)
    & debug "Close"
convertN dom (Tree Loop{..} ps) = Tree cfg' ps'
  where
  ps' = map (convertN dom) ps
  cfg = cutset program ps
  cfg' =
    cfg
    & debug "CFG"
    & mappend [ edge (V v) (unity dom) (I v) | V v <- innerflows ps ]
    & mappend [ edge (O v) (unity dom) (V v) | V v <- outerflows ps ]
    & debug "Add inner ports"
    & mappend (concatMap (\(Tree es _) -> es) ps')
    & debug "Add subprogram"
    & ripAll dom [I v | V v <- innerflows ps ]
    & ripAll dom [O v | V v <- outerflows ps ]

    & debug "rip existing outer nodes"
    & mappend [ edge (I v) (unity dom) (V v) | V v <- inflow ]
    & mappend [ edge (V v) (unity dom) (O v) | V v <- outflow ]
    & debug "Add outer ports"
    & (ripAllWith dom loopid =<< innards)
    & debug "Rip internal nodes"
    & fmap (closeWith dom loopid)
    & debug "Close"

convert :: (Ord v, Ord e, Pretty e, Show v, Show e, Pretty v) =>
  Dom st e
  -> Top [Edge (Vtx v) e] (Loop (Vtx v) e)
  -> Tree [Edge (Vtx v) e]
convert dom (Top p ps) = Tree p' ps'
  where
  ps' = map (convertN dom) ps
  cfg = cutset p ps
  p' =
    cfg
    & debug "T:CFG"
    & mappend [ edge (V v) (unity dom) (I v) | V v <- innerflows ps ]
    & mappend [ edge (O v) (unity dom) (V v) | V v <- outerflows ps ]
    & debug "T:Add inner ports"
    & mappend (concatMap (\(Tree es _) -> es) ps')
    & debug "T:Add subprogram"
    & (ripAll dom =<< innards)
    & debug "T:Rip internal nodes"
    & debug "Fin"


-- | Like convert but includes some sanity checks.
convertWith :: (Pretty v, Pretty e, Show e, Show v, Ord e, Ord v) => Dom st e -> Top (Cfg (Vtx v) e) (Loop (Vtx v) e) -> Either [Char] (Tree [Edge (Vtx v) e])
convertWith dom t@(Top cfg _) = do
  unless (hasSource cfg) $ err "missing source"
  unless (hasSink cfg)   $ err "missing link"
  let proof@(Tree flow _) = convert dom t
  unless (hasValidFlow cfg flow) $ err "invalid flow"
  return proof
  where err msg = Left $ "convertWith: " ++ msg ++ "."

hasSource, hasSink :: Ord v => Cfg v e -> Bool
hasSource = not . null . sources
hasSink   = not . null . sinks

hasValidFlow :: Ord v => Cfg v e -> Cfg v e -> Bool
hasValidFlow cfg flow = and [ any (\e -> src e == iv && dst e == ov) flow | iv <- ivs, ov <- ovs ]
  where (ivs, ovs) = (sources cfg, sinks cfg)


-- * Pretty

instance (Pretty n, Pretty v) => Pretty (Loop n v) where
  pretty Loop{..} = PP.vcat
    [ PP.bold (PP.text "Loop: ") <> PP.pretty loopid
    , PP.indent 2 $ PP.align $ pretty program ]

prettyTrees :: Pretty a => [a] -> Doc
prettyTrees [] = PP.empty
prettyTrees ts = (PP.vcat $ zipWith (<>) (repeat $ PP.text "+ ") (map (PP.align . pretty) ts))

instance (Pretty a, Pretty b) => Pretty (Top a b) where
  pretty (Top t []) = pretty t
  pretty (Top t ts) = pretty t PP.<$$> prettyTrees ts

instance Pretty a => Pretty (Tree a) where
  pretty (Tree t []) = pretty t
  pretty (Tree t ts) = pretty t PP.<$> prettyTrees ts

instance {-# Overlapping #-} (Pretty v, Pretty e) => Pretty [Edge v e] where
  pretty es = PP.vcat [ k e | e <- es ]
    where
    k Edge{..} =
      PP.fill ilen (pretty src)
      <> PP.text " ~> "
      <> PP.fill olen (pretty dst)
      <> PP.char ' '
      PP.</> PP.nest 2 (pretty att)
    ilen = maximum [ length $ show $ pretty (src e) | e <- es ]
    olen = maximum [ length $ show $ pretty (dst e) | e <- es ]

instance (Pretty v, Pretty e) => Pretty (Edge v e) where
  pretty Edge{..} = pretty src <> PP.text "\t ~> \t" <> pretty dst PP.</> pretty att

instance Pretty v => Pretty (Vtx v) where
  pretty w = case w of
    (V v) -> PP.space <> pretty v <> PP.space
    (I v) -> PP.char '<' <> pretty v <> PP.space
    (O v) -> PP.space <> pretty v <> PP.char '>'

