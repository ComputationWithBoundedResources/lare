-- | This module provides the interface for our abstract flow domain.
module Lare.Domain where

-- | A domain has a internal state @st@ and operations over edge labels @e@.
data Dom st e = Dom
  { ctx       :: st
  , unity     :: st -> e
  , rip       :: st -> [e] -> e -> e -> e
  , ripWith   :: st -> e -> [e] -> e -> e -> e
  , alternate :: st -> e -> e -> e
  , closeWith :: st -> e -> e -> e }

