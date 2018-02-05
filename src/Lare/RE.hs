{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
module Lare.RE where

import           Data.Monoid                  ((<>))

import           Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Prelude                      hiding (iterate)

import           Lare.Domain


type instance Annot (RE a) = Int

data RE a
  = Sym a
  | Epsilon
  | Concatenate (RE a) (RE a)
  | Alternate (RE a) (RE a)
  | Star (RE a)
  | Iterate Int (RE a)
  deriving Show

rex :: Dom () (RE a)
rex = undefined 
  -- { ctx         = ()
  -- , identity    = const Epsilon
  -- , concatenate = const Concatenate
  -- , concatenate1 = undefined
  -- , concatenate2 = undefined
  -- , alternate   = const Alternate
  -- , closure     = const (\_ -> Star)
  -- , iterate     = (\_ x e -> case x of {Just i -> Iterate i e; Nothing -> error "err"})
  -- }

instance {-# Overlapping #-} Pretty (RE Char) where
  pretty (Sym c)                 = PP.char c
  pretty Epsilon                 = PP.char '_'
  pretty (Concatenate Epsilon a) = pretty a
  pretty (Concatenate a Epsilon) = pretty a
  pretty (Concatenate a b)       = pretty a <> pretty b
  pretty (Alternate a b)         = PP.parens $ pretty a <> PP.char '|' <> pretty b
  pretty (Star (Sym c))          = PP.char c <> PP.char '*'
  pretty (Star a)                = PP.parens (PP.pretty a) <> PP.char '*'
  pretty (Iterate i a)           = PP.brackets $ PP.int i <> PP.space <> PP.pretty a

instance Pretty c => Pretty (RE c) where
  pretty (Sym c)                 = pretty c
  pretty Epsilon                 = PP.char '_'
  pretty (Concatenate Epsilon a) = pretty a
  pretty (Concatenate a Epsilon) = pretty a
  pretty (Concatenate a b)       = pretty a <> pretty b
  pretty (Alternate a b)         = PP.parens $ pretty a <> PP.char '|' <> pretty b
  pretty (Star (Sym c))          = PP.pretty c <> PP.char '*'
  pretty (Star a)                = PP.parens (PP.pretty a) <> PP.char '*'
  pretty (Iterate i a)           = PP.brackets $ PP.int i <> PP.space <> PP.pretty a

