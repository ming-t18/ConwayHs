{-# LANGUAGE LambdaCase #-}

module Data.Conway.Simplicity.Range
  ( Range,
    point,
    rangeEmpty,
    rangeFromPoint,
    rangeFromSet,
    rangeToSet,
    rangeToList,
    rangeCombine,
    rangeMap,
    rangeFlatMap,
    rangeProd,
    rangeSimplify,
  )
where

import Data.Conway.Conway
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.ConwaySeq
import Data.Conway.Simplicity.HelperTypes
import Data.Conway.Simplicity.Instances ()
import Data.Conway.Simplicity.SeqArith
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.Maybe (maybeToList)
import Data.Set (Set)
import qualified Data.Set as S

newtype Range a = Range (Set (RangeElem a))
  deriving (Show)

rangeEmpty :: Range a
rangeEmpty = Range S.empty

point, rangeFromPoint :: Conway a -> Range a
rangeFromPoint = Range . S.singleton . EPoint
point = rangeFromPoint

rangeFromSet :: Set (RangeElem a) -> Range a
rangeFromSet = Range

rangeToSet :: Range a -> Set (RangeElem a)
rangeToSet (Range xs) = xs

rangeToList :: Range a -> [RangeElem a]
rangeToList (Range xs) = S.toAscList xs

rangeCombine :: (OrdRing a, FiniteSignExpansion a) => Range a -> Range a -> Range a
rangeCombine (Range xs) (Range ys) = Range (S.union xs ys)

rangeSimplify :: (OrdZero a, One a) => Range a -> Range a
rangeSimplify r@(Range xs) =
  case S.minView xs of
    Nothing -> r
    Just (rMin, rest) ->
      case S.maxView rest of
        Nothing -> r
        Just (rMax, _) -> Range $ S.fromAscList [rMin, rMax]

rangeMap :: (OrdRing b, FiniteSignExpansion b) => (RangeElem a -> RangeElem b) -> Range a -> Range b
rangeMap f = Range . S.map f . rangeToSet

rangeFlatMap :: (OrdRing b, FiniteSignExpansion b) => (RangeElem a -> Set (RangeElem b)) -> Range a -> Range b
rangeFlatMap f = Range . S.unions . fmap f . rangeToList

rangeProd :: (OrdRing b, FiniteSignExpansion b) => (RangeElem a -> RangeElem a -> RangeElem b) -> Range a -> Range a -> Range b
rangeProd f xr yr = Range $ S.fromList [f x y | x <- rangeToList xr, y <- rangeToList yr]

rangeFlatProd :: (Foldable f, OrdRing b, FiniteSignExpansion b) => (RangeElem a -> RangeElem a -> f (RangeElem b)) -> Range a -> Range a -> Range b
rangeFlatProd f xr yr = Range $ S.unions [foldMap S.singleton $ f x y | x <- rangeToList xr, y <- rangeToList yr]

rangeUnop ::
  (OrdRing b, FiniteSignExpansion b) =>
  (Conway a -> Conway b) ->
  (ConwaySeq a -> ConwaySeq b) ->
  Range a ->
  Range b
rangeUnop p l = rangeMap $ \case
  EPoint x -> EPoint $ p x
  ELimit x -> ELimit $ l x

rangeBinop ::
  (Functor f, Foldable f, OrdRing b, FiniteSignExpansion b) =>
  (RangeElem b -> f (RangeElem b)) ->
  (Conway a -> Conway a -> Conway b) ->
  (ConwaySeq a -> Conway a -> ConwaySeq b) ->
  (Conway a -> ConwaySeq a -> ConwaySeq b) ->
  (ConwaySeq a -> ConwaySeq a -> f (ConwaySeq b)) ->
  Range a ->
  Range a ->
  Range b
rangeBinop single p lp pl ll =
  rangeFlatProd $ curry $ \case
    (EPoint x, EPoint y) -> single $ EPoint $ x `p` y
    (ELimit x, EPoint y) -> single $ ELimit $ x `lp` y
    (EPoint x, ELimit y) -> single $ ELimit $ x `pl` y
    (ELimit x, ELimit y) -> ELimit <$> (x `ll` y)

rangeBinopM ::
  (Functor f, Foldable f, OrdRing b, FiniteSignExpansion b) =>
  (RangeElem b -> f (RangeElem b)) ->
  (Maybe (RangeElem b) -> f (RangeElem b)) ->
  (Conway a -> Conway a -> Conway b) ->
  (ConwaySeq a -> Conway a -> Maybe (ConwaySeq b)) ->
  (Conway a -> ConwaySeq a -> Maybe (ConwaySeq b)) ->
  (ConwaySeq a -> ConwaySeq a -> f (ConwaySeq b)) ->
  Range a ->
  Range a ->
  Range b
rangeBinopM single fromM p lp pl ll =
  rangeFlatProd $ curry $ \case
    (EPoint x, EPoint y) -> single $ EPoint $ x `p` y
    (ELimit x, EPoint y) -> fromM $ ELimit <$> x `lp` y
    (EPoint x, ELimit y) -> fromM $ ELimit <$> x `pl` y
    (ELimit x, ELimit y) -> ELimit <$> (x `ll` y)

instance (OrdRing a, FiniteSignExpansion a) => Semigroup (Range a) where
  (<>) = rangeCombine

instance (OrdRing a, FiniteSignExpansion a) => Monoid (Range a) where
  mempty = rangeEmpty

instance (Num a, OrdRing a, FiniteSignExpansion a) => Num (Range a) where
  (+) = rangeBinop One (+) (flip addOffset) addOffset addSeq
  (*) = rangeBinopM (: []) maybeToList (*) (flip multSeqByConst) multSeqByConst multSeq
  abs _ = error "Range.abs: not implemented"
  signum _ = error "Range.singnum: not implemented"
  fromInteger = rangeFromPoint . fromInteger
  (-) = rangeBinop One (-) subSeqPoint subPointSeq subSeq
  negate = rangeUnop negate negConwaySeq
