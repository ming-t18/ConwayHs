module Data.Conway.Simplicity.ConwaySeq
  ( ConwaySeq (..),
    fromMonoSeq,
    fromSignedMonoSeq,
    archiClassMonoSeq,
    fromSignedMonoSeqOffset,
    addOffset,
    negConwaySeq,
  )
where

import Data.Conway.Conway
import Data.Conway.Helpers (archiClass, cutOffArchiClass, cutOffArchiClassExclusive)
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Completion
import Data.Conway.Simplicity.HelperTypes
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.Maybe (fromJust)

fromMonoSeq :: MonoSeq a -> ConwaySeq a
fromMonoSeq = ConwaySeq zero True

fromSignedMonoSeq :: Signed (MonoSeq a) -> ConwaySeq a
fromSignedMonoSeq = uncurry (ConwaySeq zero) . getSigned

fromSignedMonoSeqOffset :: (OrdRing a, FiniteSignExpansion a) => Conway a -> Signed (MonoSeq a) -> ConwaySeq a
fromSignedMonoSeqOffset base s = addOffset base $ fromSignedMonoSeq s

archiClassMonoSeq :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> Conway a
archiClassMonoSeq = fromJust . archiClass . limMonoSeq

addOffset :: (OrdRing a, FiniteSignExpansion a) => Conway a -> ConwaySeq a -> ConwaySeq a
addOffset off cs@(ConwaySeq base _ seqTerm)
  | isZero off = cs
  | otherwise = cs {csBase = base''}
  where
    base' = off `add` base
    pTerm = archiClassMonoSeq seqTerm
    absorb = case seqTerm of
      MonoMultSeq _ True -> True
      _ -> False
    base'' = if absorb then cutOffArchiClassExclusive pTerm base' else cutOffArchiClass pTerm base'

negConwaySeq :: (OrdZero a, One a) => ConwaySeq a -> ConwaySeq a
negConwaySeq (ConwaySeq base s m) = ConwaySeq (neg base) (not s) m
