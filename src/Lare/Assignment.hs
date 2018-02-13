-- | This module provides an intermediate representation of unary flow (cf `Flow).
module Lare.Assignment where


data Bound var         = Unknown | Sum [(Int, var)] deriving (Eq, Show)
newtype Assignment var = Assignment [ (var, Bound var) ] deriving (Eq, Show)

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
withAssignment vs a@(Assignment as) =
  case as of
   [ (Ann v, _) ] -> F.complete (idep ++ fromAssignment a) `F.withAnnotation` Ann v
   _              -> F.complete (idep ++ fromAssignment a)
  where idep = [ ( v <=. v) | v <- (vs \\ [ v  | (v,_) <- as ]) ]


