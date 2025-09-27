{-# LANGUAGE ViewPatterns #-}

module Data.Conway.Helpers (isInteger, archiClass, trailingArchiClass, toExponent) where

import Data.Conway.Conway
import Data.Conway.SignExpansion.Conway (isAllMinusesFinite, isAllPlusesFinite)
import Data.Conway.SignExpansion.Dyadic
import Data.Conway.Typeclasses

toExponent :: (OrdZero a, One a) => VebMono a -> Conway a
toExponent (VebMono 0 p) = p
toExponent (VebMono o p) = veb1 o p

-- | Determines if a @Conway@ is an integer according to [Gonshor] Theorem 8.1.
--
-- @isInteger x@ if and only if @x = { x - 1 | x + 1 }@
isInteger :: (FiniteSignExpansion a, OrdRing a) => Conway a -> Bool
isInteger x = case trailingView x of
  Nothing -> True
  Just (_, ((isZero -> True), c)) -> isIntegerFinite c
  Just (_, (VebMono (isZero -> True) p, _)) -> isPositive p
  Just _ -> True

isIntegerFinite :: (Zero a, FiniteSignExpansion a) => a -> Bool
isIntegerFinite x = isZero x || isAllPlusesFinite x || isAllMinusesFinite x

-- | Gets the Archimedean class of a @Conway@.
archiClass :: (OrdZero a, One a) => Conway a -> Maybe (Conway a)
archiClass x = (\((vm, _), _) -> toExponent vm) <$> leadingView x

-- | Gets the Archimedean class of the last term of a @Conway@.
trailingArchiClass :: (OrdZero a, One a) => Conway a -> Maybe (Conway a)
trailingArchiClass x = (\(_, (vm, _)) -> toExponent vm) <$> trailingView x
