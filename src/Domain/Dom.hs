{-# LANGUAGE TypeFamilies #-}
module Domain.Dom where


type family Annot a :: *

data Dom st e = Dom
  { ctx         :: st
  , identity    :: st -> e
  , concatenate :: st -> e -> e -> e
  , alternate   :: st -> e -> e -> e
  , closure     :: st -> Maybe (Annot e) -> e -> e
  , iterate     :: st -> Maybe (Annot e) -> e -> e }

