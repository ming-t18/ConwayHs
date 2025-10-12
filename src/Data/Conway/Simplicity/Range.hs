{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

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
    rangeFromLimit,
    rangeDv,
    rangeCv,
    rangeNeg,
    rangeMono1,
    rangeVeb1,

    -- * Ordering and interval
    rangeLimit,
    rangeExtreme,
    rangeMin,
    rangeMax,
    rangeExtreme',
    rangeMin',
    rangeMax',
    rangeLt,
    rangeNull,
    rangeContains,
  )
where

import Data.Conway.Conway
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Completion
import Data.Conway.Simplicity.ConwaySeq
import Data.Conway.Simplicity.HelperTypes
import Data.Conway.Simplicity.Instances ()
import Data.Conway.Simplicity.SeqArith
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses as T
import Data.List (intercalate)
import Data.Maybe (maybeToList)
import Data.Set (Set)
import qualified Data.Set as S

-- | A range of surreal numbers, which is a set of @RangeElem@s.
--
-- Represents a list of point or limit expressions.
-- Can also can be treated as an interval where the openness/closeness
-- of each side depends on if the ends are point or limit.
newtype Range a = Range {rangeToSet :: Set (RangeElem a)}

rangeNull :: Range a -> Bool
rangeNull (Range xs) = S.null xs

rangeEmpty :: Range a
rangeEmpty = Range S.empty

point, rangeFromPoint :: Conway a -> Range a
rangeFromPoint = Range . S.singleton . EPoint
point = rangeFromPoint

rangeFromSet :: Set (RangeElem a) -> Range a
rangeFromSet = Range

rangeToList :: Range a -> [RangeElem a]
rangeToList (Range xs) = S.toAscList xs

rangeCombine :: (OrdRing a, FiniteSignExpansion a) => Range a -> Range a -> Range a
rangeCombine (Range xs) (Range ys) = Range $ S.union xs ys

rangeSimplify :: (OrdZero a, One a) => Range a -> Range a
rangeSimplify r@(Range xs) =
  case S.minView xs of
    Nothing -> r
    Just (rMin, rest) ->
      case S.maxView rest of
        Nothing -> r
        Just (rMax, _) -> Range $ S.fromAscList [rMin, rMax]

rangeFromLimit :: ConwaySeq a -> Range a
rangeFromLimit = Range . S.singleton . ELimit

rangeMap :: (OrdRing b, FiniteSignExpansion b) => (RangeElem a -> RangeElem b) -> Range a -> Range b
rangeMap f = Range . S.map f . rangeToSet

rangeFlatMap :: (OrdRing b, FiniteSignExpansion b) => (RangeElem a -> Set (RangeElem b)) -> Range a -> Range b
rangeFlatMap f = Range . S.unions . fmap f . rangeToList

rangeProd :: (OrdRing b, FiniteSignExpansion b) => (RangeElem a -> RangeElem a -> RangeElem b) -> Range a -> Range a -> Range b
rangeProd f xr yr = Range $ S.fromList [f x y | x <- rangeToList xr, y <- rangeToList yr]

rangeFlatProd :: (Foldable f, OrdRing b, FiniteSignExpansion b) => (RangeElem a -> RangeElem a -> f (RangeElem b)) -> Range a -> Range a -> Range b
rangeFlatProd f xr yr = Range $ S.unions [foldMap S.singleton $ f x y | x <- rangeToList xr, y <- rangeToList yr]

-- * Ordering and interval

takeLimit :: (OrdRing a, FiniteSignExpansion a) => RangeElem a -> Conway a
takeLimit = rangeElem id limConwaySeq

-- | Take the limit of all range elements.
rangeLimit :: (OrdRing a, FiniteSignExpansion a) => Range a -> Range a
rangeLimit = Range . S.map (EPoint . takeLimit) . rangeToSet

rangeExtreme :: (OrdRing a, FiniteSignExpansion a) => Bool -> Range a -> Maybe (Conway a)
rangeExtreme d = ((takeLimit . fst) <$>) . view . rangeToSet . rangeSimplify
  where
    view = if d then S.maxView else S.minView

rangeMin, rangeMax :: (OrdRing a, FiniteSignExpansion a) => Range a -> Maybe (Conway a)
rangeMin = rangeExtreme False
rangeMax = rangeExtreme True

takeLimit' :: (OrdRing a, FiniteSignExpansion a) => Ordering -> RangeElem a -> (Conway a, Ordering)
takeLimit' o = rangeElem (,EQ) ((,o) . limConwaySeq)

rangeExtreme' :: (OrdRing a, FiniteSignExpansion a) => Bool -> Range a -> Maybe (Conway a, Ordering)
rangeExtreme' d = ((takeLimit' o . fst) <$>) . view . rangeToSet . rangeSimplify
  where
    o = if d then GT else LT
    view = if d then S.maxView else S.minView

rangeMin', rangeMax' :: (OrdRing a, FiniteSignExpansion a) => Range a -> Maybe (Conway a, Ordering)

-- | Gets the minimum interval point of a @Range@.
rangeMin' = rangeExtreme' False

-- | Gets the maximum interval point of a @Range@.
rangeMax' = rangeExtreme' True

rangeContains :: (OrdRing a, FiniteSignExpansion a) => Range a -> Conway a -> Bool
rangeContains r x = maybe True (<= x') (rangeMin' r) && maybe True (x' <=) (rangeMax' r) where x' = (x, EQ)

-- | @rx rangeLt ry@ if and only if pairwise @x < y@ for all @x in rx@ and @y in ry@
rangeLt :: (OrdRing a, FiniteSignExpansion a) => Range a -> Range a -> Bool
rangeLt x y = rangeMax x < rangeMin y

-- * Primitive

rangeDv, rangeCv :: Range a
rangeDv = rangeFromLimit $ fromMonoSeq $ MonoMultSeq zero True
rangeCv = rangeFromLimit $ fromMonoSeq $ MonoMultSeq zero False

-- * Range arithmetic operations

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

instance (Num a, OrdRing a, FiniteSignExpansion a) => Num (Range a) where
  (+) = rangeBinop One (+) (flip addOffset) addOffset addSeq
  (*) = rangeBinopM (: []) maybeToList (*) (flip multSeqByConst) multSeqByConst multSeq
  abs _ = error "Range.abs: not implemented"
  signum _ = error "Range.singnum: not implemented"
  fromInteger = rangeFromPoint . fromInteger
  (-) = rangeBinop One (-) subSeqPoint subPointSeq subSeq
  negate = rangeNeg

rangeNeg :: (OrdRing a, FiniteSignExpansion a) => Range a -> Range a
rangeNeg = rangeUnop neg negConwaySeq

rangeMono1 :: (OrdRing a, FiniteSignExpansion a) => Range a -> Range a
rangeMono1 = rangeUnop mono1 mono1Seq

rangeVeb1 :: (OrdRing a, FiniteSignExpansion a) => Ordinal -> Range a -> Range a
rangeVeb1 o = rangeUnop (veb1 o) (veb1Seq o)

-- * Range Instances

instance (OrdRing a, FiniteSignExpansion a) => Semigroup (Range a) where
  (<>) = rangeCombine

instance (OrdRing a, FiniteSignExpansion a) => Monoid (Range a) where
  mempty = rangeEmpty

instance (Show a, OrdRing a) => Show (Range a) where
  show (Range xs) = "{" ++ intercalate ", " (map show' $ S.toAscList xs) ++ "}"
    where
      show' (EPoint p) = show p
      show' (ELimit l) = show l
