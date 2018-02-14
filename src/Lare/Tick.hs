-- | This module provides counter instumentation for the `Flow` domain.
{-# LANGUAGE RecordWildCards #-}
module Lare.Tick where


import Data.List ((\\))
import Data.Monoid ((<>))
import qualified Data.Set                     as S (toList)
import           Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Lare.Analysis                (Edge (..), Program, Proof, Tree (..), Top(..))
import qualified Lare.Domain                  as D
import           Lare.Flow                    (E ((:>)), F, (<=.),(<+.),(<*.))
import qualified Lare.Flow                    as F
import           Lare.Util (ppList)


data Var v
  = Var v   -- ^ program variable
  | Ann v   -- ^ variables for bound annotation
  | Counter -- ^ a counter variable
  | K       -- ^ used to represent an arbitrary but fixed constant
  | Huge    -- ^ used to define \unbounded\ or \unknonw\ values
  deriving (Eq, Ord, Show)


-- | An extension to the `Flow` domain that supports counter.
ticked :: Ord v => F.Flow (Var v) -> F.Flow (Var v)
ticked f = f { D.closeWith = closeWith }

-- | Adds bounding information for subprograms.
--
-- Informally  @closeWith vs bound summary@ simulates @bound <= expresion; tick += bound; summary@.
closeWith :: Ord v => [Var v] -> F (Var v) -> F (Var v) -> F (Var v)
closeWith vs af f = af `F.concatenate` tick `F.concatenate` f  where
  Just a = F.annot af
  tick   = F.plus vs Counter Counter a


-- * Bound Assignments

data Bound var         = Unknown | Sum [(Int, var)] deriving (Eq, Ord, Show)
newtype Assignment var = Assignment [ (var, Bound var) ] deriving (Eq, Ord, Show)

toFlow :: Ord v => [Var v] -> Program n (Assignment (Var v)) -> Program n (F (Var v))
toFlow vs (Top es ts) = Top (fmap k `fmap` es) (fmap (fmap k) `fmap` ts)
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
withAssignment vs a@(Assignment as) =
  case as of
   [ (Ann v, _) ] -> F.complete (idep ++ fromAssignment a) `F.withAnnotation` Ann v
   _              -> F.complete (idep ++ fromAssignment a)
  where idep = [ ( v <=. v) | v <- (vs \\ [ v  | (v,_) <- as ]) ]




-- * Bound Inference

data Complexity = Constant | Linear | Polynomial | Primrec | Indefinite deriving Show

instance Eq Complexity  where c1 == c2 = rank c1 == rank c2
instance Ord Complexity where c1 <= c2 = rank c1 <= rank c2

rank :: Complexity -> Int
rank Constant   = 2
rank Linear     = 5
rank Polynomial = 11
rank Primrec    = 42
rank Indefinite = 99

-- | Computes bound of flow taking the concretiasation function into account.
bound :: Eq v => F (Var v) -> Complexity
bound F.F{..}
  | isIndefinite = Indefinite
  | null ds      = Constant
  | otherwise    =
    case maximum ds of
      F.Identity       -> Linear
      F.Additive       -> Linear
      F.Multiplicative -> Polynomial
      F.Exponential    -> Primrec
  where
    ds = [ b | (b, v :> w) <- S.toList unary, w == Counter, v /= K, v /= Counter ]
    isIndefinite = any (\(_, w :> v) -> w == Huge && v == Counter) (S.toList unary)

boundOfProof :: Eq v => Proof n (F (Var v)) -> Complexity
boundOfProof (Tree es _)
  | null es   = Indefinite
  | otherwise = maximum [ bound (att e) | e <- es ]


-- * Pretty

instance Pretty v => Pretty (Var v) where
  pretty (Var v) = pretty v
  pretty (Ann v) = pretty v
  pretty Counter = PP.text "tick"
  pretty Huge    = PP.text "huge"
  pretty K       = PP.text "K"

instance Pretty v => Pretty (Bound v) where
  pretty Unknown  = PP.text "unknwon"
  pretty (Sum cs) = PP.encloseSep PP.empty PP.empty (PP.text " + ") $ k `fmap` cs where
    k (i,v)
     | i == 1    = PP.pretty v
     | otherwise = PP.int i <> PP.char '*' <> pretty v

instance Pretty v => Pretty (Assignment v) where
  pretty (Assignment as) = ppList $ k `fmap` as
    where k (v,b) = pretty v <> PP.text " <= " <> pretty b

