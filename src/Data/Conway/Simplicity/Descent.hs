module Data.Conway.Simplicity.Descent (descend, descent, descentSeq, limLR) where

import Data.Conway.Conway
import qualified Data.Conway.Seq.InfList as I
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Completion (HasParentSeq (..), ParentRepr (..), limParentSeqDir, parentSeq)
import Data.Conway.Simplicity.Seq (ToSeq (..))
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.Conway.Typeclasses.ConwayOps (Birthday (..))
import Data.List (unfoldr)

descend :: (OrdRing a, FiniteSignExpansion a) => Conway a -> Maybe (Conway a)
descend = fmap (either id (I.head . toSeq) . toEither) . parentSeq

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

limLR :: (Birthday o a, HasParentSeq a re, ParentRepr re a seq) => (Maybe re, Maybe re) -> a
limLR (l, r) =
  case (limL, limR) of
    (Nothing, Nothing) -> zero
    (Just x, Nothing) -> x
    (Nothing, Just x) -> x
    (Just x, Just y) -> if birthday x < birthday y then y else x
  where
    limL = limParentSeqDir True l
    limR = limParentSeqDir False r
