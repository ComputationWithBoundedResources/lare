-- | This module provides \bounded regular expression\ abstract domain.
{-# LANGUAGE FlexibleInstances #-}
module Lare.RE where

import           Data.Monoid                  ((<>))

import           Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Lare.Domain                  as D


-- * Bounded RegeEx Abstract Domain

rex :: D.Dom () (RE a)
rex = D.Dom
  { D.ctx       = ()
  , D.unity     = const unity
  , D.rip       = const rip
  , D.ripWith   = const (const ripWith)
  , D.alternate = const alternate
  , D.closeWith = const closeWith }

data RE a
  = Sym a
  | Epsilon
  | Concatenate (RE a) (RE a)
  | Alternate (RE a) (RE a)
  | Star (RE a)
  | Iterate (RE a) (RE a)
  deriving (Show, Eq, Ord)

unity :: RE a
unity = Epsilon

alternate :: RE a -> RE a -> RE a
alternate = Alternate

rip, ripWith :: [RE a] -> RE a -> RE a -> RE a
rip [] uv vw = Concatenate uv vw
rip vv uv vw = uv `Concatenate` vv' `Concatenate` vw
  where vv' = Star $ foldr1 Alternate vv
ripWith = rip

closeWith :: RE a -> RE a -> RE a
closeWith a@(Sym _) uv = Iterate a uv
closeWith _ _          = error "LARE.RE: closeWith: the unexpected happened"


-- * Pretty

instance Pretty c => Pretty (RE c) where
  pretty (Sym c)                 = pretty c
  pretty Epsilon                 = PP.char '_'
  pretty (Concatenate Epsilon a) = pretty a
  pretty (Concatenate a Epsilon) = pretty a
  pretty (Concatenate a b)       = pretty a <> pretty b
  pretty (Alternate a b)         = PP.parens $ pretty a <> PP.char '|' <> pretty b
  pretty (Star (Sym c))          = PP.pretty c <> PP.char '*'
  pretty (Star a)                = PP.parens (PP.pretty a) <> PP.char '*'
  pretty (Iterate a e)           = PP.brackets $ PP.pretty a <> PP.space <> PP.pretty e

