{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts, FlexibleInstances, RecordWildCards, TypeFamilies, TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
module Lare.Analysis where

import           Data.Function                ((&))
import           Data.List                    (nub, (\\))
import           Data.Monoid                  ((<>))

import           Data.Map.Strict              (Map)
import qualified Data.Map.Strict              as M
import           Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Debug.Trace


import           Lare.Domain
import           Lare.Flow                    (E ((:>)), F, (<*.), (<+.), (<=.))
import qualified Lare.Flow                    as F
import           Lare.RE



--- * Cfg ------------------------------------------------------------------------------------------------------------

data Edge v e = Edge
  { src :: v
  , att :: e
  , dst :: v
  } deriving (Eq, Ord, Show, Functor)

edge :: v -> e -> v -> Edge v e
edge src att dst = Edge { src = src, att = att, dst = dst }

lift1 :: (e1 -> e2) -> Edge v e1 -> Edge v e2
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

unVar :: V v -> v
unVar (V v)   = v
unVar (Out v) = v
unVar (In v)  = v

--- * Program --------------------------------------------------------------------------------------------------------


data Top a b = Top a [Tree b]
  deriving (Show, Functor, Foldable, Traversable)

data Tree a = Tree a [Tree a]
  deriving (Show, Functor, Foldable, Traversable)


--- * Loop -----------------------------------------------------------------------------------------------------------

data Loop v e = Loop
  { program :: [Edge v e]
  , loopid  :: e
  , outer   :: [v] }
  deriving (Show, Functor)


inner ts = concatMap (\(Tree l _) -> outer l) ts


--- * Attribute Domain -----------------------------------------------------------------------------------------------

identity' :: Dom st e -> e
identity' Dom{..} = identity ctx

concatenate', alternate' :: Dom st e -> Edge v e -> Edge v e -> Edge v e
concatenate' Dom{..} = lift2 (concatenate ctx)
alternate' Dom{..}   = lift2 (alternate ctx)

closure', iterate' :: Dom st e -> e -> Edge v e -> Edge v e
closure' Dom{..} a e = lift1 (closure ctx a) e
iterate' Dom{..} a e = lift1 (iterate ctx a) e

-- --- * Rip ------------------------------------------------------------------------------------------------------------


type T v e = Cfg v e -> Cfg v e

ripOne :: Eq v => Dom st e -> Maybe e -> v -> T v e
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

  combinator es = lift2 (concatenate2 dom (ctx dom) a [ att e | e <- es ])

  chainAll k es ds = [ k e1 e2 | e1 <- es, e2 <- ds ]

  mergeParallel k = foldr (mergeOne k) []

  mergeOne _ e1 []                         = [e1]
  mergeOne k e1 (e2:es)
    | src e1 == src e2 && dst e1 == dst e2 = k e1 e2: es
    | otherwise                            = e2 : mergeOne k e1 es

rip :: Eq v => Dom st e -> [v] -> T v e
rip dom vs cfg = foldr (ripOne dom Nothing) cfg vs

ripWith :: Eq v => Dom st e -> e -> [v] -> T v e
ripWith dom a vs cfg = iterate' dom a <$> foldr (ripOne dom $ Just a) cfg vs


-- FIXME: add inner
-- use epsilon for outer part; but use predecessor for inner part


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
    --
    -- & mappend [ e { dst = In v}  | e <- p, Out v <- inner ps, V v == dst e ]
    -- & mappend [ e { src = Out v}  | e <- p, Out v <- inner ps, V v == src e ]
    & mappend [ edge (V v)   (identity' dom) (In v) | Out v <- inner ps ]
    & mappend [ edge (Out v) (identity' dom) (V v) | Out v <- inner ps ]

    & debug "T:add inner ports subtrees"
    & rip dom [In v  | Out v <- inner ps ]
    -- & debug "T:rip inner In ports"
    & rip dom [Out v | Out v <- inner ps ]
    -- & debug "T:rip inner Out ports"
    -- & \g -> traceShow (sources g ++ sinks g ++ [ In $ unVar v | v <- sources p] ++ [Out $ unVar v | v <- sinks p]) g
    -- & \g -> traceShow (nodes g \\ (sources g ++ sinks g ++ [ In $ unVar v | v <- sources p] ++ [Out $ unVar v | v <- sinks p])) g
    -- & \g -> rip dom Nothing (nodes g \\ (sources g ++ sinks g ++ [ In $ unVar v | v <- sources p] ++ [Out $ unVar v | v <- sinks p])) g
    & \g -> traceShow ((sources g ++ sinks g)) g
    & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
    & \g -> rip dom (nodes g \\ (sources g ++ sinks g)) g
    & debug "T:rip internal ports"
    & debug "result"
-- FIXME

-- p 27 source sinks; cin -> cout?
-- if v is final in p then vout; if v is initial in p then pin

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
      & ripWith dom loopid [In v  | Out v <- inner ps ]
      & ripWith dom loopid [Out v | Out v <- inner ps ]
      & debug "rip inner nodes"
      & mappend [ edge (In v) (identity' dom) (V v)  | Out v <- outer ]
      & mappend [ edge (V v) (identity' dom) (Out v) | Out v <- outer ]
      & debug "add outer ports"
      & \g -> traceShow (nodes g \\ (sources g ++ sinks g)) g
      -- & \g -> loop foldr (\v g' -> trace ("rip\n" ++ ppcfg g') ripOne v g') g (nodes g \\ (sources g ++ sinks g))
      & \g -> ripWith dom loopid (nodes g \\ (sources g ++ sinks g)) g
      & debug "rip internal nodes"

debug s cfg = trace ("[" ++ s ++ "]\n" ++ ppcfg cfg) cfg

--- * Intermediate Representation ------------------------------------------------------------------------------------


data Var v = Var v | Ann v | Counter | K | Huge deriving (Eq, Ord, Show)


data Bound var         = Unknown | Sum [(Int, var)] deriving (Eq, Show)
newtype Assignment var = Assignment [ (var, Bound var) ] deriving (Eq, Show)

type Program n e = Top [Edge n e] (Loop n e)

toFlow0 :: Ord v => [Var v] -> Program n (Assignment (Var v)) -> Program n (F (Var v))
toFlow0 vs (Top es ts) = Top (fmap k `fmap` es) (fmap (fmap k) `fmap` ts)
  where k = withAssignment vs
 

fromAssignment :: Assignment (Var v) -> [F.U (Var v)]
fromAssignment (Assignment as) = do
  (v,b) <- as
  case b of
    Unknown       -> return $ v <=. Huge
    Sum []        -> return $ v <=. K
    Sum [(_,K)]   -> return $ v <=. K
    Sum [(k,w)]
      | k == 1    -> return  $ v <=. w
      | otherwise -> return  $ v <*. w
    Sum bs  -> [ g k w | (k,w) <- bs, k /= 0 ] where
      g 1 w = (v <+. w)
      g _ w = (v <*. w)






withAssignment :: Ord v => [Var v] -> Assignment (Var v) -> F (Var v)
withAssignment vs a@(Assignment as) = F.complete $ idep ++ assign
  where
  idep   = [ ( v <=. v) | v <- (vs \\ [ v  | (v,_) <- as ]) ]
  assign = fromAssignment a



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
  where k e = show (src e) ++ "\t~>\t" ++ show (dst e) ++ "\t\n" ++ (render $ PP.indent 2 $ pretty (att e))


ex1 :: Program (V Char) (RE String)
ex1 =
  Top
    [a,b,e]
    [ Tree
      Loop
      { program     = [c,d]
      , loopid      = Sym "L"
      , outer       = [Out 'C', Out 'B'] }
      []
    ]
  where
    a = edge (V 'I') (Sym "skip;") (V 'A')
    b = edge (V 'A') (Sym "x1:=x3;") (V 'B')
    c = edge (V 'B') (Sym "x2:=x3;") (V 'C')
    d = edge (V 'C') (Sym "x3:=x3+x2;") (V 'B')
    e = edge (V 'C') (Sym "x4:=x3;") (V 'F')

runex1 = convert (rex) ex1

-- ex1' :: Program Char (RE String)
-- ex1' =
--   Top
--     [i,f,a,b,c,d,e]
--     [ Tree
--       Loop
--       { program     = [a,b,c,d,e]
--       , loopid      = 1
--       , outer       = [Out 'A']
--       , cuts        = [] }
--       [ Tree
--       Loop
--       { program     = [b,c,d]
--       , loopid      = 2
--       , outer       = [Out 'C', Out 'B']
--       , cuts        = [] }
--       []
--       ]
--     ]
--   where
--     i = edge (V 'I') (Sym "s") (V 'A')
--     f = edge (V 'A') (Sym "f") (V 'F')

--     a = edge (V 'A') (Sym "a") (V 'B')
--     b = edge (V 'B') (Sym "b") (V 'C')
--     c = edge (V 'C') (Sym "c") (V 'D')
--     d = edge (V 'D') (Sym "d") (V 'B')
--     e = edge (V 'B') (Sym "e") (V 'A')

-- runex1' = convert (rex) ex1'

runex2 = convert (F.flow [1..5]) ex2

ex2 =
  Top
    [a,b,e]
    [ Tree
      Loop
      { program     = [c,d]
      , loopid      = F.copy vs 5 1
      , outer       = [Out 'C', Out 'B'] }
      []
    ]
  where
    a = edge (V 'I') (F.skip vs) (V 'A')
    b = edge (V 'A') (F.copy vs 1 3) (V 'B')
    c = edge (V 'B') (F.copy vs 2 3) (V 'C')
    d = edge (V 'C') (F.plus vs 3 1 2) (V 'B')
    e = edge (V 'C') (F.copy vs 4 3) (V 'F')
    vs = [1..5] :: [Int]


-- ex3 =
--   Top
--     [a,e]
--     [ Tree
--       Loop
--       { program     = [d]
--       , loopid      = (Var 'X', Just $ Sum [(1, Var 'j')])
--       , outer       = [Out 2]
--       , cuts        = [] }
--       [ Tree
--         Loop
--           { program     = [b,c]
--           , loopid      = (Var 'X', Just $ Sum [(1, Var 'j')])
--           , outer       = [Out 3]
--           , cuts        = [] }
--         []
--       ]
--     ]
--   where
--     a = edge (V 1) (Assignment [ (v, Sum [(1, Var 'n')]) | v <- vs ]) (V 2)
--     b = edge (V 2) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 3)
--     c = edge (V 3) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 2)
--     d = edge (V 3) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 2)
--     e = edge (V 2) (Assignment [ (v, Sum [(1,v)]) | v <- vs ]) (V 4)
--     vs = [Var 'n', Var 'i', Var 'j']


--- * Pretty ---------------------------------------------------------------------------------------------------------

render :: Pretty a => a -> String
-- render = flip PP.displayS "" . PP.renderCompact . pretty
render = flip PP.displayS "" . (PP.renderPretty 0.5 240) . pretty



instance Pretty v => Pretty (Bound v) where
  pretty Unknown  = PP.text "unknwon"
  pretty (Sum cs) = PP.encloseSep PP.empty PP.empty (PP.text " + ") $ k `fmap` cs where
    k (i,v) 
     | i == 1    = PP.pretty v
     | otherwise = PP.int i <> PP.char '*' <> pretty v

instance Pretty v => Pretty (Assignment v) where
  pretty (Assignment as) = PP.list $ k `fmap` as
    where k (v,b) = pretty v <> PP.text " <= " <> pretty b

instance Pretty v => Pretty (Var v) where
  pretty (Var v) = pretty v
  pretty (Ann v) = pretty v
  pretty Counter = PP.text "tick"
  pretty Huge    = PP.text "huge"
  pretty K       = PP.text "K"

instance (Pretty n, Pretty v) => Pretty (Loop n v) where
  pretty Loop{..} = PP.vcat
    [ PP.bold (PP.text "Loop: ") <> PP.pretty loopid 
    , PP.indent 2 $ PP.align $ pretty program ]

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
  pretty Edge{..} = pretty src <> PP.string "\t ~> \t" <> pretty dst PP.<$> PP.indent 2 (pretty att)

instance Pretty v => Pretty (V v) where
  pretty v = case v of
    (V v)   -> pp v
    (In v)  -> pp v
    (Out v) -> pp v
    -- where pp = PP.bold . pretty
    where pp = pretty

