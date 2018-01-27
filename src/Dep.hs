{-# LANGUAGE TypeFamilies #-}
module Dep where

import           Data.Set             (Set)
import qualified Data.Set             as S

import           Prelude              hiding (iterate)

-- FIXME: when do we need all variables; can we just use somethin like an special id flow?


data Dom st e = Dom
  { ctx         :: st
  , identity    :: st -> e
  , concatenate :: st -> e -> e -> e
  , alternate   :: st -> e -> e -> e
  , closure     :: st -> Maybe (Annot e) -> e -> e
  , iterate     :: st -> Maybe (Annot e) -> e -> e }


type family Annot a :: *
type instance Annot (F v) = v

type Flow v = Dom [v] (F v)

flow :: Ord v => [v] -> Flow v
flow vs = Dom
  { ctx         = vs
  , identity    = identity'
  , concatenate = const concatenate'
  , alternate   = const alternate'
  , closure     = closure'
  , iterate     = iterate' }


--- * Dependency -----------------------------------------------------------------------------------------------------

data E v =  v :> v deriving (Eq, Ord, Show)
data D = Identity | Additive | Multiplicative | Exponential 
  deriving (Eq, Ord, Show, Enum)

type U v = (D, E v)
type B v = (E v, E v)

data F v = F
  { unary  :: Set (U v)
  , binary :: Set (B v) }
  deriving Show


empty :: F v
empty = F { unary = S.empty, binary = S.empty}

isSubsetOf :: Ord v => F v -> F v -> Bool
isSubsetOf f1 f2 =
  unary f1 `S.isSubsetOf` unary f2 &&
  binary f1 `S.isSubsetOf` binary f2

union :: Ord v => F v -> F v -> F v
union f1 f2 = F
  { unary = unary f1 `S.union` unary f2
  , binary = binary f1 `S.union` binary f2 }

idep :: [v] -> [U v]
idep vs = [ (Identity, v :> v) | v <- vs ]

complete :: Ord v => [U v] -> F v
complete ds = F
  { unary  = S.fromList ds
  , binary = S.fromList bs }
  where
  bs = [ (i :> k, j :> l)
       | (d1, i :> k) <- ds
       , (d2, j :> l) <- ds
       , i /= j || k /= l
       , d1 `max` d2 <= Additive ]

-- skip :: Ord v => F v
-- skip =

-- plus :: Ord v => v -> v -> v -> Flow v
-- plus r s t = ask >>= \vs -> return $ complete $
--   let ids =  [ (Identity, v :> v) | v <- vs, v /= r ] in
--   if s /= t
--   then (Additive, s :> r): (Multiplicative, t :> r): ids
--   else (Multiplicative, s :> r) : ids

-- mult :: Ord v => v -> v -> v -> Flow v
-- mult r s t = ask >>= \vs -> return $ complete $
--   (Multiplicative, s :> r) :(Multiplicative, t :> r) : [ (Identity, v :> v) | v <- vs, v /= r ]

-- --- * Operations -----------------------------------------------------------------------------------------------------

identity' :: Ord v => [v] -> F v
identity' = complete . idep

alternate' :: Ord v => F v -> F v -> F v
alternate' f1 f2 = F
  { unary  = unary f1  `S.union` unary f2
  , binary = binary f1 `S.union` binary f2}

concatenate' :: Ord v => F v -> F v -> F v
concatenate' f1 f2 = F
  { unary =
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

closure' _ _ f = f

correct' :: Ord v => v -> F v -> F v
correct' v f = f `union` f { unary = unary' }
  where unary' =  S.fromList [ (succ d, v :> j) | (d, j :> i) <- S.toList (unary f), j == i, d == Additive || d == Multiplicative ]

iterate' _  Nothing f = error "oh no"
iterate' vs (Just v) f = correct' v $ lfp f empty f
  where
  lfp new old action
    | new `isSubsetOf` old = old
    | otherwise            = lfp new' new f
      where new' = complete [ (Identity, v :> v) | v <- vs ] `union` old `union` (old `concatenate'` action)


