{-# LANGUAGE TypeFamilies #-}
module Lare.Domain where


type family Annot a :: *

data Dom st e = Dom
  { ctx         :: st
  , identity    :: st -> e
  , concatenate :: st -> e -> e -> e
  , concatenate1 :: st -> e -> e -> e
  , concatenate2 :: st -> Maybe (Annot e) -> [e] -> e -> e -> e
  , alternate   :: st -> e -> e -> e
  , closure     :: st -> Maybe (Annot e) -> e -> e
  , iterate     :: st -> Maybe (Annot e) -> e -> e }

