-- | This module provides the dependency flow analysis.
{-# LANGUAGE FlexibleInstances, RecordWildCards, ViewPatterns #-}
module Lare.Flow where

import           Data.Monoid                  ((<>))
import           Data.Set                     (Set)
import qualified Data.Set                     as S
import           Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Lare.Domain                  as D
import Lare.Util (ppList)


-- * Flow Domain ----------------------------------------------------------------------------------------------------

type Flow v = D.Dom [v] (F v)

flow :: Ord v => [v] -> Flow v
flow vs = D.Dom
  { D.ctx       = vs
  , D.unity     = unity
  , D.rip       = rip
  , D.ripWith   = ripWith
  , D.alternate = const alternate
  , D.closeWith = const closeWith }


-- * Dependency -----------------------------------------------------------------------------------------------------

data E v =  v :> v deriving (Eq, Ord, Show)
data D = Identity | Additive | Multiplicative | Exponential
  deriving (Eq, Ord, Show, Enum)



-- | A unary flow describes how a variable influences another.
-- @(Additive, w :> v)@
type U v = (D, E v)

from, to :: U v -> v
from (_, v :> _) = v
to (_, _ :> w)   = w

(<=.), (<+.), (<*.), (<^.) :: v -> v -> U v
v <=. w = (Identity, w :> v)
v <+. w = (Additive, w :> v)
v <*. w = (Multiplicative, w :> v)
v <^. w = (Exponential, w :> v)

-- | A binary Flow keeps track duplicating dependencies.
type B v = (E v, E v)

-- | The \Flow\ abstraction domain.
data F v = F
  { annot  :: Maybe v  -- ^ 
  , unary  :: Set (U v) 
  , binary :: Set (B v) }
  deriving (Eq, Ord, Show)

withAnnotation :: F v -> v -> F v
withAnnotation f v = f { annot = Just v }

empty :: F v
empty = F { annot = Nothing, unary = S.empty, binary = S.empty}

isSubsetOf :: Ord v => F v -> F v -> Bool
isSubsetOf f1 f2 =
  unary f1 `S.isSubsetOf` unary f2 &&
  binary f1 `S.isSubsetOf` binary f2

union :: Ord v => F v -> F v -> F v
union f1 f2 = F
  { annot  = Nothing
  , unary  = unary f1 `S.union` unary f2
  , binary = binary f1 `S.union` binary f2 }

-- | The unary Identity dependencies for a given set of variables.
idep :: [v] -> [U v]
idep vs = [ (Identity, v :> v) | v <- vs ]

-- | Computes binary dependencies.
complete :: Ord v => [U v] -> F v
complete ds = F
  { annot  = Nothing
  , unary  = S.fromList ds
  , binary = S.fromList bs }  
  where 
  bs = [ (i :> k, j :> l)
       | (a, i :> k) <- ds
       , (b, j :> l) <- ds
       , i /= j || k /= l
       , a `max` b <= Additive ]


-- * Flowchart Statements -------------------------------------------------------------------------------------------

skip :: Ord v => [v] -> F v
skip = unity

copy :: Ord v => [v] -> v -> v -> F v
copy vs r s = complete $ (Identity, s :> r): [ (Identity, v :> v) | v <- vs, v /= r ]

plus :: Ord v => [v] -> v -> v -> v -> F v
plus vs r s t = complete $
  let ids =  [ (Identity, v :> v) | v <- vs, v /= r ] in
  if s == t
  then (Multiplicative, s :> r) : ids
  else (Additive, s :> r): (Additive, t :> r): ids

mult :: Ord v => [v] -> v -> v -> v -> F v
mult vs r s t = complete $
  (Multiplicative, s :> r) :(Multiplicative, t :> r) :[ (Identity, v :> v) | v <- vs, v /= r ]


fromK :: Int -> D
fromK k
  | k < 0     = fromK (-k)
  | k == 0    = Identity
  | k == 1    = Additive
  | otherwise = Multiplicative

-- (.=) :: v -> v -> U v
-- (.=) v1 v2 = (Identity , v1 :> v2)

-- (.+) :: v -> v -> U v
-- (.+) v1 v2 = (Additive , v1 :> v2)

-- (.*) :: v -> v -> U v
-- (.*) v1 v2 = (Multiplicative , v1 :> v2)

-- (.^) :: v -> v -> U v
-- (.^) v1 v2 = (Exponential , v1 :> v2)


-- --- * Operations -----------------------------------------------------------------------------------------------------

lfp :: Ord v => [v] -> F v -> F v
lfp vs f = go f f empty where
  go f new old
    | new `isSubsetOf` old = old
    | otherwise            = go f new' new
      where new' = complete [ (Identity, v :> v) | v <- vs ] `union` old `union` (old `concatenate` f)

correctWith :: Ord v => F v -> F v -> F v
correctWith F{..} f = correct a f
  where Just a = annot

correct :: Ord v => v -> F v -> F v
correct v f = f `union` f { unary = unary' }
  where unary' =  S.fromList [ (succ d, v :> j) | (d, j :> i) <- S.toList (unary f), j == i, d == Additive || d == Multiplicative ]

concatenate :: Ord v => F v -> F v -> F v
concatenate f1 f2 = F
  { annot = Nothing
  , unary =
      S.fromList $
        [ (d1 `max` d2   , i :> k) | (d1, i :> x) <- us1, (d2, z :> k) <- us2, x == z ] ++
        [ (Multiplicative, i :> k) | (i :> x, i' :> x') <- bs1, i == i', (z :> k, z' :> k') <- bs2, k == k', x == z && x' == z']

  , binary =
      S.fromList $
        [ (i :> k, i :> k')  | (d1, i :> x) <- us1, d1 <= Additive, (z :> k, z' :> k') <- bs2, x == z && x == z' ] ++
        [ (i :> k, i' :> k)  | (i :> x, i' :> x') <- bs1,  (d2, z :> k) <- us2, d2 <= Additive, x == z && x' == z]  ++
        [ (i :> k, i' :> k') | (i :> x, i' :> x') <- bs1, (z :> k, z' :> k') <- bs2, i /= i' || k /= k', x == z && x' == z' ] }
  where
    us1 = S.toList (unary f1)
    us2 = S.toList (unary f2)
    bs1 = S.toList (binary f1)
    bs2 = S.toList (binary f2)

unity :: Ord v => [v] -> F v
unity = complete . idep

rip :: Ord v => [v] -> [F v] -> F v -> F v -> F v
rip vs []  uv vw = uv `concatenate` vw
-- rip vs vvs uv vw = lfp vs $ uv `concatenate` (lfp vs $ foldr1 alternate vvs) `concatenate` vw
rip vs vvs uv vw = uv `concatenate` (foldr1 alternate vvs) `concatenate` vw

closeWith :: Ord v => F v -> F v -> F v
closeWith f1 f2 = f1 `concatenate` f2

ripWith :: Ord v => [v] -> F v -> [F v] -> F v -> F v -> F v
ripWith vs _ []  uv vw = uv `concatenate` vw
ripWith vs l vvs uv vw = correctWith l $ lfp vs $ uv `concatenate` vv `concatenate` vw
  where vv = correctWith l $ lfp vs $ foldr1 alternate vvs

alternate :: Ord v => F v -> F v -> F v
alternate f1 f2 = F
  { annot  = Nothing
  , unary  = unary f1  `S.union` unary f2
  , binary = binary f1 `S.union` binary f2}

-- * Pretty ---------------------------------------------------------------------------------------------------------

instance {-# Overlapping #-} Pretty v => Pretty (D, E v) where
  pretty (d, i :> j) = pretty i <> PP.text " ~" <> ppd d <> PP.text "> " <> pretty j where
    ppd Identity       = PP.char '='
    ppd Additive       = PP.char '+'
    ppd Multiplicative = PP.char '*'
    ppd Exponential    = PP.char '^'


instance (Eq v, Pretty v) => Pretty (F v) where
  -- pretty F{..} = PP.align $ PP.vcat [ pretty u | u <- S.toList unary]
  pretty F{..} = PP.list [ pretty u | u@(d, i:> j) <- S.toList unary, d /= Identity || i/=j ]

