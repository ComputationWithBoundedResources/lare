-- | This module provides some motivating examples.
module Lare.Examples where


import qualified Data.Map.Strict as M

import           Lare.Analysis
import           Lare.Flow
import           Lare.RE
import           Lare.Tick


-- | An example using the regular expressions (`RE`) domain.
--
-- >>> putStrLn $ render ex1
--  I  ~>  A   skip;
--  A  ~>  B   x1:=x3;
--  B  ~>  C   x2:=x3;
--  C  ~>  B   x3:=x3+x2;
--  C  ~>  F   x4:=x3;
-- + Loop: 1
--      B  ~>  C   x2:=x3;
--      C  ~>  B   x3:=x3+x2;
-- >>> putStrLn $ render $ convert rex ex1
--  I  ~>  F   skip;x1:=x3;[1 x2:=x3;(x3:=x3+x2;x2:=x3;)*]x4:=x3;
-- + <B  ~>  C>  [1 x2:=x3;(x3:=x3+x2;x2:=x3;)*]
---
ex1 :: Program Char (RE String)
ex1 = toProgram $
  Top
    [a,b,c,d,e]
    [ Tree
      SimpleLoop
      { program' = [c,d]
      , loopid'  = Sym "1" }
      []
    ]
  where
    a = edge 'I' (Sym "skip;")      'A'
    b = edge 'A' (Sym "x1:=x3;")    'B'
    c = edge 'B' (Sym "x2:=x3;")    'C'
    d = edge 'C' (Sym "x3:=x3+x2;") 'B'
    e = edge 'C' (Sym "x4:=x3;")    'F'


-- |  An example using the flow (`Flow`) domain.
--
-- >>> putStrLn $ render ex2
--  I  ~>  A   []
--  A  ~>  B   [3 ~=> 1]
--  B  ~>  C   [3 ~=> 2]
--  C  ~>  B   [1 ~+> 3,2 ~+> 3]
--  C  ~>  F   [3 ~=> 4]
-- + Loop: []
--      B  ~>  C   [3 ~=> 2]
--      C  ~>  B   [1 ~+> 3,2 ~+> 3]
-- >>> putStrLn $ render $ convert (flow [1..5]) ex2
--  I  ~>  F   [3 ~=> 1,3 ~=> 2,3 ~=> 4,3 ~+> 2,3 ~+> 3,3 ~+> 4,3 ~*> 2,3 ~*> 3,3 ~*> 4,5 ~*> 2,5 ~*> 3,5 ~*> 4]
-- + <B  ~>  C>  [3 ~=> 2,1 ~+> 2,1 ~+> 3,3 ~+> 2,3 ~+> 3,1 ~*> 2,1 ~*> 3,5 ~*> 2,5 ~*> 3]
--
ex2 :: Program Char (F Int)
ex2 = toProgram $
  Top
    [a,b,c,d,e]
    [ Tree
      SimpleLoop
      { program' = [c,d]
      , loopid'  = skip vs `withAnnotation` 5 }
      []
    ]
  where
    a = edge 'I' (skip vs)       'A'
    b = edge 'A' (copy vs 1 3)   'B'
    c = edge 'B' (copy vs 2 3)   'C'
    d = edge 'C' (plus vs 3 1 2) 'B'
    e = edge 'C' (copy vs 4 3)   'F'
    vs = [1..5] :: [Int]


-- | Variables for ex3.
ex3vs :: [Var Int]
ex3vs = [ Ann 616, Huge, Counter, K ] ++ [ Var v | v <- [1..5] ]

-- |  An example using the tick (`Tick`) domain.
--
-- >>> putStrLn $ render ex3
--  I  ~>  A   [1 <= 1, 2 <= 2, 3 <= 3, 4 <= 4, 5 <= 5, 616 <= 616, tick <= tick, K <= K, huge <= huge]
--  A  ~>  B   [1 <= 3, 2 <= 2, 3 <= 3, 4 <= 4, 5 <= 5, 616 <= 616, tick <= tick, K <= K, huge <= huge]
--  B  ~>  C   [1 <= 1, 2 <= 3, 3 <= 3, 4 <= 4, 5 <= 5, 616 <= 616, tick <= tick, K <= K, huge <= huge]
--  C  ~>  B   [1 <= 1, 2 <= 2, 3 <= 1 + 2, 4 <= 4, 5 <= 5, 616 <= 616, tick <= tick, K <= K, huge <= huge]
--  C  ~>  F   [1 <= 1, 2 <= 2, 3 <= 3, 4 <= 3, 5 <= 5, 616 <= 616, tick <= tick, K <= K, huge <= huge]
-- + Loop: [616 <= 5]
--      B  ~>  C   [1 <= 1, 2 <= 3, 3 <= 3, 4 <= 4, 5 <= 5, 616 <= 616, tick <= tick, K <= K, huge <= huge]
--      C  ~>  B   [1 <= 1, 2 <= 2, 3 <= 1 + 2, 4 <= 4, 5 <= 5, 616 <= 616, tick <= tick, K <= K, huge <= huge]
-- >>> putStrLn $ render $ convert (ticked $ flow ex3vs) (toFlow ex3vs ex3)
 -- I  ~>  F   [3 ~=> 1
 --            ,3 ~=> 2
 --            ,3 ~=> 4
 --            ,5 ~=> 616
 --            ,3 ~+> 2
 --            ,3 ~+> 3
 --            ,3 ~+> 4
 --            ,5 ~+> tick
 --            ,tick ~+> tick
 --            ,3 ~*> 2
 --            ,3 ~*> 3
 --            ,3 ~*> 4
 --            ,5 ~*> 2
 --            ,5 ~*> 3
 --            ,5 ~*> 4]
-- + <B  ~>  C>  [3 ~=> 2
 --              ,5 ~=> 616
 --              ,1 ~+> 2
 --              ,1 ~+> 3
 --              ,3 ~+> 2
 --              ,3 ~+> 3
 --              ,5 ~+> tick
 --              ,tick ~+> tick
 --              ,1 ~*> 2
 --              ,1 ~*> 3
 --              ,5 ~*> 2
 --              ,5 ~*> 3]
-- >>> boundOfProof $ convert (ticked $ flow ex3vs) (toFlow ex3vs ex3)
-- Linear
--
ex3 :: Program Char (Assignment (Var Int))
ex3 = toProgram $
  Top
    [a,b,c,d,e]
    [ Tree
      SimpleLoop
      { program' = [c,d]
      , loopid'  = Assignment $ [ (Ann 616, Sum [(1,Var 5)]) ] }
      []
    ]
  where
    a = edge 'I' skip'                           'A'
    b = edge 'A' (copy' (Var 1) (Var 3))         'B'
    c = edge 'B' (copy' (Var 2) (Var 3))         'C'
    d = edge 'C' (plus' (Var 3) (Var 1) (Var 2)) 'B'
    e = edge 'C' (copy' (Var 4) (Var 3))         'F'

    env   = M.fromList [ (v, Sum [(1,v)]) | v <- ex3vs ]

    skip'       = Assignment $ M.toList env
    copy' x y   = Assignment $ M.toList $ M.insert x (Sum [(1,y)]) env
    plus' x y z = Assignment $ M.toList $ M.insert x (Sum [(1,y),(1,z)]) env

