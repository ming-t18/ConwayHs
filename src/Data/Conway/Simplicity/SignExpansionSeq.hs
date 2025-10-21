{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Conway.Simplicity.SignExpansionSeq
  ( OrdMonoSeq,
    SignExpansionSeq,
    ParentSeqSignExpansion,
    parentSeqSignExpansion,
    signExpansionSeqToInfList,
    limSignExpansionSeq,
    psseEmpty,
    pssePoint,
    psseLim,
    seRangeElem,
    limParentSeqSE,
    limParentSeqSEDir,
    birthdaySeq,
  )
where

import Data.Conway.Conway
import Data.Conway.Seq.InfList (Infinite)
import qualified Data.Conway.Seq.InfList as I
import qualified Data.Conway.SignExpansion as SE
import Data.Conway.SignExpansion.Types (SignExpansion, (+++))
import Data.Conway.Simplicity.Completion (Limit (..), limMonoSeq, parentSeq)
import Data.Conway.Simplicity.ConwaySeq (addOffset)
import Data.Conway.Simplicity.Seq (monoSeq)
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses (One (..), zero)

data SignExpansionRangeElem = SEPoint SignExpansion | SELimit SignExpansionSeq
  deriving (Eq, Show)

type OrdMonoSeq = MonoSeq Natural

-- | A limit sequence of a @SignExpansion@.
--
-- @SignExpansionSeq base sign term@ represents a sequence
-- @generate (\i -> base <> single (sign, monoSeq term `index` i))@
data SignExpansionSeq = SignExpansionSeq
  { sesBase :: SignExpansion,
    sesSign :: Bool,
    sesTerm :: OrdMonoSeq
  }
  deriving (Eq, Show)

type ParentSeqSignExpansion = Maybe SignExpansionRangeElem

-- * Helpers

psseEmpty :: ParentSeqSignExpansion
psseEmpty = Nothing

pssePoint :: SignExpansion -> ParentSeqSignExpansion
pssePoint = Just . SEPoint

psseLim :: SignExpansionSeq -> ParentSeqSignExpansion
psseLim = Just . SELimit

seRangeElem :: (SignExpansion -> b) -> (SignExpansionSeq -> b) -> SignExpansionRangeElem -> b
seRangeElem f _ (SEPoint p) = f p
seRangeElem _ g (SELimit l) = g l

-- * TYpes

parentSeqSignExpansion :: SignExpansion -> ParentSeqSignExpansion
parentSeqSignExpansion s =
  case fromSE s of
    [] -> Nothing
    ((sign, n) : xs) ->
      case parentSeq n of
        Nothing -> parentSeqSignExpansion $ toSE xs
        Just (EPoint n') -> Just $ SEPoint $ toSE ((sign, n') : xs)
        Just (ELimit (ConwaySeq nBase _ mSeq)) ->
          let base = toSE ((sign, nBase) : xs)
           in Just $ SELimit $ SignExpansionSeq base sign mSeq
  where
    toSE = SE.fromList . reverse
    fromSE = reverse . SE.toList

signExpansionSeqToInfList :: SignExpansionSeq -> Infinite SignExpansion
signExpansionSeqToInfList (SignExpansionSeq base sign term) =
  I.generate $ \i -> base +++ SE.single (sign, I.index s i)
  where
    s = monoSeq term

limSignExpansionSeq :: SignExpansionSeq -> SignExpansion
limSignExpansionSeq (SignExpansionSeq base sign term) =
  base +++ SE.single (sign, limMonoSeq term)

limParentSeqSE :: ParentSeqSignExpansion -> Maybe SignExpansion
limParentSeqSE = (seRangeElem id limSignExpansionSeq <$>)

limParentSeqSEDir :: Bool -> ParentSeqSignExpansion -> Maybe SignExpansion
limParentSeqSEDir sign = (seRangeElem (+++ SE.single (sign, one)) limSignExpansionSeq <$>)

birthdaySeq :: ParentSeqSignExpansion -> ParentSeq Natural
birthdaySeq pse =
  case pse of
    Nothing -> Nothing
    Just (SEPoint p) -> Just $ EPoint $ SE.length p
    Just (SELimit (SignExpansionSeq base _ term)) -> Just $ ELimit (SE.length base `addOffset` ConwaySeq zero True term)

instance Limit SignExpansionSeq SignExpansion where
  limit = limSignExpansionSeq
