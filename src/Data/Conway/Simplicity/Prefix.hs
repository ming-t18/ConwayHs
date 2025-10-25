module Data.Conway.Simplicity.Prefix (isOrdinal, isNegOrdinal, leadingPlusesOnly, leadingMinusesOnly) where

import Data.Conway.Conway
import Data.Conway.SignExpansion.Conway (isAllMinuses, isAllPluses, isAllPlusesFinite, isAllPlusesVebMono)
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion (..))
import qualified Data.Conway.SignExpansion.Dyadic as SED
import Data.Conway.Typeclasses

isOrdinal :: (FiniteSignExpansion a) => Conway a -> Bool
isOrdinal = isAllPluses

isNegOrdinal :: (FiniteSignExpansion a, OrdZero a, One a) => Conway a -> Bool
isNegOrdinal = isAllMinuses

-- | Givean a @Conway@, truncate it with the leading pluses (based on sign expansion) only.
--
-- This implementation does not go through sign expansion conversion.
leadingPlusesOnly :: (FiniteSignExpansion a, One a, AddSub a) => Conway a -> Conway a
leadingPlusesOnly = fromTermsList . loop . termsList
  where
    loop [] = []
    loop (x0@(vm@(VebMono o p), c) : xs)
      | isNegative c = []
      | pvm && pc =
          case loop xs of
            ((vm', c') : xs') | vm == vm' -> (vm, c `add` c') : xs'
            xs' -> x0 : xs'
      | pvm && not pc = [(vm, leadingPlusesOnlyFinite c)]
      | otherwise = [(VebMono o $ leadingPlusesOnly p, one)]
      where
        pvm = isAllPlusesVebMono vm
        pc = isAllPlusesFinite c

leadingMinusesOnly :: (FiniteSignExpansion a, One a, AddSub a) => Conway a -> Conway a
leadingMinusesOnly = neg . leadingPlusesOnly . neg

leadingPlusesOnlyFinite :: (FiniteSignExpansion a) => a -> a
leadingPlusesOnlyFinite = parseFiniteSE' . SED.fromList . takeLeading . SED.toList . finiteSE
  where
    takeLeading [] = []
    takeLeading ((True, n) : _) = [(True, n)]
    takeLeading _ = []
