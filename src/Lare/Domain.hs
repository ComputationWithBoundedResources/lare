{-# LANGUAGE TypeFamilies #-}
module Lare.Domain where


type family Annot a :: *

data Dom st e = Dom
  { ctx         :: st
  , identity    :: st -> e
  , concatenate :: st -> e -> e -> e
  , concatenate1 :: st -> e -> e -> e
  , concatenate2 :: st -> Maybe e -> [e] -> e -> e -> e
  , alternate   :: st -> e -> e -> e
  , closure     :: st -> e -> e -> e
  , iterate     :: st -> e -> e -> e }

