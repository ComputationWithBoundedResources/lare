module Lare.Util where

import Data.Monoid ((<>))

import           Text.PrettyPrint.ANSI.Leijen (Doc, Pretty, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Data.Set as S (empty, insert, member)

snub :: Ord a => [a] -> [a]
snub = go S.empty where
  go seen []            = []
  go seen (x:xs)
    | x `S.member` seen = go seen xs
    | otherwise         = x: go (x `S.insert` seen) xs

partition3 :: (a -> Bool) -> (a -> Bool) -> (a -> Bool) -> [a] -> ([a],[a],[a],[a])
partition3 p1 p2 p3 = foldr select ([],[],[],[]) where
  select x ~(xs1,xs2,xs3,xs4)
    | p1 x       = (x:xs1, xs2,   xs3,   xs4)
    | p2 x       = (xs1,   x:xs2, xs3,   xs4)
    | p3 x       = (xs1,   xs2,   x:xs3, xs4)
    | otherwise  = (xs1,   xs2,   xs3,   x:xs4)

render :: Pretty a => a -> String
render = flip PP.displayS "" . (PP.renderPretty 0.5 240) . pretty
-- render = flip PP.displayS "" . PP.renderCompact . pretty

ppList :: [Doc] -> Doc
ppList [] = PP.empty
ppList ds = PP.enclose PP.lbracket PP.rbracket $ foldr1 (\p acc -> (p <> PP.text ", " <> acc) ) ds

