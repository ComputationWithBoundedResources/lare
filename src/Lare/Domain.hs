{-# LANGUAGE TypeFamilies #-}
module Lare.Domain where


data Dom st e = Dom
  { ctx       :: st
  , unity     :: st -> e
  , rip       :: st -> [e] -> e -> e -> e
  , ripWith   :: st -> e -> [e] -> e -> e -> e
  , alternate :: st -> e -> e -> e
  , closeWith :: st -> e -> e -> e }

