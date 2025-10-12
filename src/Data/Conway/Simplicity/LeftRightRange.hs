{-# LANGUAGE ViewPatterns #-}

-- | Module handling the @{ left | right }@ representation of surreal numbers
-- where @left@ and @right@ are @Range@s.
module Data.Conway.Simplicity.LeftRightRange
  ( LRRange (..),
    left,
    right,
    star,
    toLR,
    isValid,
    lrNeg,
    lrLe,
    existsLe,
    empty,
    lrAdd,
    lrMono1,
  )
where

import Data.Conway.Conway
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Instances ()
import Data.Conway.Simplicity.Parent
import Data.Conway.Simplicity.Range
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses

infix 0 :|:

-- | Represents the @{left | right}@ form of a surreal number
-- where @left@ and @right@ are @Range@s.
--
-- It is possible to represent an invalid range where the sides overlap.
data LRRange a = Range a :|: Range a
  deriving (Show)

-- | @(l :|: r)@ is zero if and only if all @l@ are negative and all @r@ are positive
instance (OrdRing a, FiniteSignExpansion a) => Zero (LRRange a) where
  zero = lrZero
  isZero ((rangeMax -> ml) :|: (rangeMin -> mr)) = maybe True isNegative ml && maybe True isPositive mr

-- | Negation of a range. Flips the range and negates both sides.
lrNeg :: (OrdRing a, FiniteSignExpansion a) => LRRange a -> LRRange a
lrNeg (l :|: r) = rangeNeg r :|: rangeNeg l

left, right :: LRRange a -> Range a
left (l :|: _) = l
right (_ :|: r) = r

-- * Pre-defined values

lrZero :: LRRange a
lrZero = rangeEmpty :|: rangeEmpty

-- | The invalid range @{ 0 | 0 }@
star :: LRRange a
star = rangeFromPoint zero :|: rangeFromPoint zero

-- * Conversion

toLR :: (OrdRing a, FiniteSignExpansion a) => Conway a -> LRRange a
toLR x = toRange l :|: toRange r
  where
    (l, r) = toPair $ lrConway x

-- * Ordering

-- | Determines if a range represents a valid surreal number.
isValid :: (OrdRing a, FiniteSignExpansion a) => LRRange a -> Bool
isValid (l :|: r) = rangeExtreme True l < rangeExtreme False r

existsLeLimit :: (OrdRing a, FiniteSignExpansion a) => LRRange a -> ConwaySeq a -> Bool
existsLeLimit _ _ = error "TODO"

existsLeRangeElem :: (OrdRing a, FiniteSignExpansion a) => LRRange a -> RangeElem a -> Bool
existsLeRangeElem x = rangeElem ((x `lrLe`) . toLR) (existsLeLimit x)

-- | @x `existsLe` range@ determines if there exists @r@ in @range@ such that @x <= r@
existsLe :: (OrdRing a, FiniteSignExpansion a) => LRRange a -> Range a -> Bool
existsLe x = any (x `existsLeRangeElem`) . rangeToList

--
--
--         x
-- ------o |   o---------
--
--    o      o   o    o      o     o

-- | @range `existsLe'` (yl :|: yr)@ determines if there exists @r@ in @range@ such that @y <= (yl :|: yr)@
existsLe' :: (OrdRing a, FiniteSignExpansion a) => Range a -> LRRange a -> Bool
existsLe' r x = lrNeg x `existsLe` rangeNeg r

lrLe :: (OrdRing a, FiniteSignExpansion a) => LRRange a -> LRRange a -> Bool
lrLe
  x@(xl :|: _)
  y@(_ :|: yr) = not (y `existsLe` xl) && not (yr `existsLe'` x)

empty :: LRRange a
empty = rangeEmpty :|: rangeEmpty

-- instance Zero (LRRange a) where
--   zero = empty
--   isZero (LRRange (l, r)) = isZero l && isZero r

toRange :: ParentSeq a -> Range a
toRange Nothing = rangeEmpty
toRange (Just (EPoint p)) = rangeFromPoint p
toRange (Just (ELimit l)) = rangeFromLimit l

-- rangeFromConway :: (OrdRing a, FiniteSignExpansion a) => Bool -> Conway a -> Range a
-- rangeFromConway sign = toRange . parentConway sign

-- * Arithmetic

lrAdd :: (OrdRing a, FiniteSignExpansion a) => Conway a -> Conway a -> LRRange a
lrAdd x0 y0 = (x' `add` y) <> (x `add` y') :|: (x'' `add` y) <> (x `add` y'')
  where
    x = point x0
    y = point y0
    (x' :|: x'') = toLR x0
    (y' :|: y'') = toLR y0

lrMono1 :: (OrdRing a, FiniteSignExpansion a) => Conway a -> LRRange a
lrMono1 x0 = zero <> (rangeMono1 x' `mult` rangeDv) :|: rangeMono1 x'' `mult` rangeCv
  where
    (x' :|: x'') = toLR x0

-- lrVeb1 :: (OrdRing a, FiniteSignExpansion a) => Ordinal -> Conway a -> LRRange a
-- lrVeb1 o x0 = left (lrMono1 x0) <> _ :|: right (lrMono1 x0) <> _
--   where
--     (x' :|: x'') = toLR x0
