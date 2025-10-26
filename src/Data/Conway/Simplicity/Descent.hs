module Data.Conway.Simplicity.Descent (descend, descent, descentSeq) where

import Data.Conway.Conway
import qualified Data.Conway.Seq.InfList as I
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Completion (parentSeq)
import Data.Conway.Simplicity.Seq (ToSeq (..))
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.List (unfoldr)

descend :: (OrdRing a, FiniteSignExpansion a) => Conway a -> Maybe (Conway a)
descend = (rangeElem id (I.head . toSeq) <$>) . parentSeq

descent :: (OrdRing a, FiniteSignExpansion a) => Conway a -> [Conway a]
descent = unfoldr (fmap (\x -> (x, x)) . descend)

descentSeq :: (OrdRing a, FiniteSignExpansion a) => Conway a -> [(Conway a, Bool, RangeElem a)]
descentSeq x =
  case parentSeq x of
    Nothing -> []
    Just s'@(EPoint x') -> (x, x > x', s') : descentSeq x'
    Just s'@(ELimit l) ->
      let x' = I.index (toSeq l) 0
       in (x, x > x', s') : descentSeq x'
