-- | This module provides the \rip\ algorithm, which abstracts Flowchart programs to flow properties.
{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, RecordWildCards,
             TypeFamilies, TypeOperators, ViewPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module Lare.Analysis where

import           Control.Monad                (unless)
import           Data.Function                ((&))
import           Data.List                    ((\\))
import           Data.Monoid                  ((<>))
import           Text.PrettyPrint.ANSI.Leijen (Doc, Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Lare.Domain                  (Dom)
import qualified Lare.Domain                  as D
import           Lare.Util                    (partition3, render, snub)

import           Debug.Trace


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
nodes cfg = snub $ fmap src cfg ++ fmap dst cfg

sources :: Ord v => Cfg v e ->  [v]
sources cfg = snub (fmap src cfg) \\ snub (fmap dst cfg)

sinks :: Ord v => Cfg v e -> [v]
sinks cfg = snub (fmap dst cfg) \\ snub (fmap src cfg)


-- | A wrapper for the vertex type.
data Vtx v
  = V v -- ^ standard vertices
  | O v -- ^ denotes an output port for subprograms
  | I v -- ^ denotes an input port for subprograms
  deriving (Eq, Ord, Show)


--- * Program

data Top a b = Top a [Tree b]
  deriving (Show, Functor, Foldable, Traversable)

data Tree a = Tree a [Tree a]
  deriving (Show, Functor, Foldable, Traversable)

data Loop v e = Loop
  { program :: [Edge v e]
  , loopid  :: e
  , outer   :: [v]
  , inflow  :: [v]
  , outflow :: [v] }
  deriving (Show, Functor)

type Program v e = Top  [Edge (Vtx v) e] (Loop (Vtx v) e)
type Proof   v e = Tree [Edge (Vtx v) e]


inner, innerflows, outerflows :: Ord v => [Tree (Loop v e)] -> [v]
inner ts = snub $ concatMap (\(Tree l _) -> outer l) ts
innerflows ts = snub $ concatMap (\(Tree l _) -> inflow l) ts
outerflows ts = snub $ concatMap (\(Tree l _) -> outflow l) ts


cutset :: (Eq v, Eq e) => [Edge v e] -> [Tree (Loop v e)] -> [Edge v e]
cutset p ts = p \\ concatMap (\(Tree l _) -> program l) ts

--- * Attribute Domain -----------------------------------------------------------------------------------------------

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


-- --- * Rip ------------------------------------------------------------------------------------------------------------


debug :: Pretty a => String -> a -> a
debug s cfg = trace ("[" ++ s ++ "]\n" ++ render (PP.indent 2 $ PP.align $ pretty cfg)) cfg

type T v e = Cfg v e -> Cfg v e

ripOne :: Eq v => Dom st e -> ([Edge v e] -> Edge v e -> Edge v e -> Edge v e) -> v -> T v e
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

overIn, overOut :: Eq v => Dom st e -> [Vtx v] -> [Edge (Vtx v) e] -> [Edge (Vtx v) e]
overIn dom ifs cfg =
  [ edge (src e) a (I v)
    | V v <- ifs
    , e   <- cfg
    , dst e == (V v)
    , let a = if src e == (V v) then unity dom else att e ]

overOut dom ofs cfg =
  [ edge (O v) a (dst e)
    | V v <- ofs
    , e   <- cfg
    , src e == (V v)
    , let a = if dst e == (V v) then unity dom else att e ]

convertN :: (Show e, Show v, Pretty e, Ord v, Eq e, Pretty v) => Dom st e -> Tree (Loop (Vtx v) e) -> Tree [Edge (Vtx v) e]
convertN dom (Tree Loop{..} []) = Tree cfg' []
  where
    cfg = program
    cfg' =
      cfg
      & debug "CFG"
      & mappend [ edge (I v) (unity dom) (V v) | V v <- inflow ]
      & mappend [ edge (V v) (unity dom) (O v) | V v <- outflow ]
      & debug "Add outer ports"
      & \g -> ripAllWith dom loopid (nodes g \\ (sources g ++ sinks g)) g
      & debug "Rip internal nodes"
      & fmap (closeWith dom loopid)
      & debug "Close"
convertN dom (Tree Loop{..} ps) = Tree cfg' ps'
  where
  ps' = map (convertN dom) ps
  cfg = cutset program ps
  cfg' =
    cfg

    -- & debug "CFG"
    -- & mappend (overIn  dom (innerflows ps) cfg)
    -- & mappend (overOut dom (outerflows ps) cfg)
    -- & debug "Add inner ports"
    -- & mappend (concatMap (\(Tree es _) -> es) ps')
    -- & debug "Add subprogram"

    -- & debug "CFG"
    -- & mappend [ edge (V v) (unity dom) (I v) | V v <- innerflows ps ]
    -- & mappend [ edge (O v) (unity dom) (V v) | V v <- outerflows ps ]
    -- & debug "Add inner ports"
    -- & mappend (concatMap (\(Tree es _) -> es) ps')
    -- & debug "Add subprogram"
    -- & ripAll dom [I v | V v <- inflow ]
    -- & ripAll dom [O v | V v <- outflow ]



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
    & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
    & \g -> ripAllWith dom loopid (nodes g \\ (sources g ++ sinks g)) g
    & debug "Rip internal nodes"
    & fmap (closeWith dom loopid)
    & debug "Close"

convert :: (Ord v, Eq e, Pretty e, Show v, Show e, Pretty v) =>
  Dom st e
  -> Top [Edge (Vtx v) e] (Loop (Vtx v) e)
  -> Tree [Edge (Vtx v) e]
convert dom (Top p ps) = Tree p' ps'
  where
  ps' = map (convertN dom) ps
  cfg = cutset p ps
  p' =
    cfg

    -- & debug "T:CFG"
    -- & mappend (overIn  dom (innerflows ps) cfg)
    -- & mappend (overOut dom (outerflows ps) cfg)
    & debug "CFG"
    & mappend [ edge (V v) (unity dom) (I v) | V v <- innerflows ps ]
    & mappend [ edge (O v) (unity dom) (V v) | V v <- outerflows ps ]

    & debug "T:Add inner ports"
    & mappend (concatMap (\(Tree es _) -> es) ps')
    & debug "T:Add subprogram"
    & \g -> traceShow ((sources g ++ sinks g)) g
    & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
    & \g -> ripAll dom (nodes g \\ (sources g ++ sinks g)) g
    & debug "T:Rip internal nodes"
    & debug "result"






ppcfg :: (Pretty e, Show v, Show e) => Cfg v e -> String
ppcfg = unlines . map k
  where k e = show (src e) ++ "\t~>\t" ++ show (dst e) ++ "\t\n" ++ (render $ PP.indent 2 $ pretty (att e))



convertWith :: (Pretty v, Pretty e, Show e, Show v, Eq e, Ord v) => Dom st e -> Top (Cfg (Vtx v) e) (Loop (Vtx v) e) -> Either [Char] (Tree [Edge (Vtx v) e])
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


--ex1 :: Program (V Char) (RE String)
--ex1 =
--  Top
--    [a,b,e]
--    [ Tree
--      Loop
--      { program     = [c,d]
--      , loopid      = Sym "L"
--      , outer       = [Out 'C', Out 'B'] }
--      []
--    ]
--  where
--    a = edge (V 'I') (Sym "skip;") (V 'A')
--    b = edge (V 'A') (Sym "x1:=x3;") (V 'B')
--    c = edge (V 'B') (Sym "x2:=x3;") (V 'C')
--    d = edge (V 'C') (Sym "x3:=x3+x2;") (V 'B')
--    e = edge (V 'C') (Sym "x4:=x3;") (V 'F')

--runex1 = convert (rex) ex1

---- ex1' :: Program Char (RE String)
---- ex1' =
----   Top
----     [i,f,a,b,c,d,e]
----     [ Tree
----       Loop
----       { program     = [a,b,c,d,e]
----       , loopid      = 1
----       , outer       = [Out 'A']
----       , cuts        = [] }
----       [ Tree
----       Loop
----       { program     = [b,c,d]
----       , loopid      = 2
----       , outer       = [Out 'C', Out 'B']
----       , cuts        = [] }
----       []
----       ]
----     ]
----   where
----     i = edge (V 'I') (Sym "s") (V 'A')
----     f = edge (V 'A') (Sym "f") (V 'F')

----     a = edge (V 'A') (Sym "a") (V 'B')
----     b = edge (V 'B') (Sym "b") (V 'C')
----     c = edge (V 'C') (Sym "c") (V 'D')
----     d = edge (V 'D') (Sym "d") (V 'B')
----     e = edge (V 'B') (Sym "e") (V 'A')

---- runex1' = convert (rex) ex1'

-- runex2 = convert (F.flow [1..6]) ex2

-- ex2 =
--   Top
--     [a,b,e]
--     [ Tree
--       Loop
--       { program     = [c,d]
--       , loopid      = F.copy vs 6 5
--       , outer       = [Out 'C', Out 'B'] }
--       []
--     ]
--   where
--     a = edge (V 'I') (F.skip vs) (V 'A')
--     b = edge (V 'A') (F.copy vs 1 3) (V 'B')
--     c = edge (V 'B') (F.copy vs 2 3) (V 'C')
--     d = edge (V 'C') (F.plus vs 3 1 2) (V 'B')
--     e = edge (V 'C') (F.copy vs 4 3) (V 'F')
--     vs = [1..6] :: [Int]


---- ex3 =
----   Top
----     [a,e]
----     [ Tree
----       Loop
----       { program     = [d]
----       , loopid      = (Var 'X', Just $ Sum [(1, Var 'j')])
----       , outer       = [Out 2]
----       , cuts        = [] }
----       [ Tree
----         Loop
----           { program     = [b,c]
----           , loopid      = (Var 'X', Just $ Sum [(1, Var 'j')])
----           , outer       = [Out 3]
----           , cuts        = [] }
----         []
----       ]
----     ]
----   where
----     a = edge (V 1) (Assignment [ (v, Sum [(1, Var 'n')]) | v <- vs ]) (V 2)
----     b = edge (V 2) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 3)
----     c = edge (V 3) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 2)
----     d = edge (V 3) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 2)
----     e = edge (V 2) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 4)
----     vs = [Var 'n', Var 'i', Var 'j']


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
  pretty v = case v of
    (V v) -> PP.space <> pretty v <> PP.space
    (I v) -> PP.char '<' <> pretty v <> PP.space
    (O v) -> PP.space <> pretty v <> PP.char '>'

