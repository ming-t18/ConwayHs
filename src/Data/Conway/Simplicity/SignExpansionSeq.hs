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

    -- * Common prefix
    constructToSE,
    construct,
    commonPrefix,
  )
where

import Data.Conway.Conway
import Data.Conway.Seq.InfList (Infinite)
import qualified Data.Conway.Seq.InfList as I
import qualified Data.Conway.SignExpansion as SE
import Data.Conway.SignExpansion.Types (SignExpansion, (+++))
import Data.Conway.Simplicity.Completion (Limit (..), limMonoSeq, parentSeq)
import Data.Conway.Simplicity.ConwaySeq (addOffset)
import Data.Conway.Simplicity.OrdinalSeq
import Data.Conway.Simplicity.Seq (monoSeq)
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.Function (on)

data SignExpansionRangeElem = SEPoint SignExpansion | SELimit SignExpansionSeq
  deriving (Eq, Show)

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

instance Ord SignExpansionRangeElem where
  compare = compare `on` toOrdInv

toOrdInv :: SignExpansionRangeElem -> (SignExpansion, Ordering)
toOrdInv (SEPoint p) = (p, EQ)
toOrdInv (SELimit l@SignExpansionSeq {sesSign = True}) = (limSignExpansionSeq l, LT)
toOrdInv (SELimit l@SignExpansionSeq {sesSign = False}) = (limSignExpansionSeq l, GT)

instance Zero SignExpansionRangeElem where
  zero = SEPoint zero
  isZero (SEPoint p) = isZero p
  isZero _ = False

instance OrdZero SignExpansionRangeElem where
  neg = seRangeElem (SEPoint . neg) (SELimit . flipSeq)

-- | Flip the sign of the varying part of the @SignExpansionSeq@
flipSeq :: SignExpansionSeq -> SignExpansionSeq
flipSeq s@(SignExpansionSeq {sesSign = sign}) = s {sesSign = not sign}

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
  limitSign = sesSign

-- * Common prefix and construct operations

commonPrefix :: SignExpansionRangeElem -> SignExpansionRangeElem -> SignExpansionRangeElem
commonPrefix s1 s2
  | l1 == l2 =
      case (o1, o2) of
        (EQ, EQ) -> s1
        (_, EQ) -> s1
        (EQ, _) -> s2
        (_, _) -> error "commonPrefix: not possible"
  | cpl == l1 = s1
  | otherwise = s2
  where
    (l1, o1) = toOrdInv s1
    (l2, o2) = toOrdInv s2
    cpl = SE.commonPrefix l1 l2

constructToSE :: SignExpansionRangeElem -> SignExpansionRangeElem -> SignExpansion
constructToSE s1 s2
  | l1 > l2 =
      error "constructSERE: invalid"
  | l1 == l2 =
      case (o1, o2) of
        (EQ, EQ) -> error "ConstructSERE: invalid"
        -- { [S +^n'] | [S +^n] } = [S +^n -]
        (LT, EQ) -> l2 SE.+++ SE.single (False, one)
        -- { [S -^n'] | [S -^n'] } = [S -^n +]
        (EQ, GT) -> l1 SE.+++ SE.single (True, one)
        (_, _) -> error "constructSERE: not possible"
  | otherwise =
      case (o1, o2) of
        (EQ, GT) ->
          case SE.toList r2 of
            [(True, 1), (False, _)] -> l2
            _ -> l3
        (LT, EQ) ->
          case SE.toList r1 of
            [(False, 1), (True, _)] -> l2
            _ -> l3
        (EQ, EQ) -> l3
        (_, _) -> error "constructSERE: not possible"
  where
    (l1, o1) = toOrdInv s1
    (l2, o2) = toOrdInv s2
    l3 = SE.construct l1 l2
    (_, (r1, r2)) = SE.takeCommonPrefix l1 l2

construct :: SignExpansionRangeElem -> SignExpansionRangeElem -> SignExpansionRangeElem
construct s1 s2 = SEPoint $ constructToSE s1 s2

-- TODO implement
-- instance CO.Veb Ordinal (SignExpansionSeq a) where
--   veb1 = veb1SESeq
--   mono1 = mono1SESeq
