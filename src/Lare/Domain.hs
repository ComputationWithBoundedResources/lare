-- | This module provides the interface for our abstract domain.
module Lare.Domain where

-- | Domain has a state @st@ and operations over edge labelles @e@.
data Dom st e = Dom
  { ctx       :: st
  , unity     :: st -> e
  , rip       :: st -> [e] -> e -> e -> e
  , ripWith   :: st -> e -> [e] -> e -> e -> e
  , alternate :: st -> e -> e -> e
  , closeWith :: st -> e -> e -> e }

