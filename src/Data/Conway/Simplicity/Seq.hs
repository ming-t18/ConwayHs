{-# LANGUAGE ViewPatterns #-}

-- | Module for enumerating the fundamental sequences of surreal numbers.
--
-- Modifications from the "standard" fundamental sequences:
--
-- * The FS of monomials must be monomial
--
-- * The FS of monomials must start with zero
--
-- * The FS of the sum of multiple monomials must remove the last term at index zero
module Data.Conway.Simplicity.Seq (toPointOrSeq, conwaySeq, monoSeq, veb1Seq) where

import Data.Conway.Conway
import Data.Conway.Helpers
import Data.Conway.Seq.InfList (Infinite)
import qualified Data.Conway.Seq.InfList as I
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion (parseFiniteSE), fromList)
import Data.Conway.Simplicity.Completion
import Data.Conway.Simplicity.Parent
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.Maybe (fromJust)

toPointOrSeq :: (OrdRing a, FiniteSignExpansion a) => ParentSeq a -> Maybe (Either (Conway a) (Infinite (Conway a)))
toPointOrSeq = (rangeElem Left (Right . conwaySeq) <$>)

conwaySeq :: (OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> Infinite (Conway a)
monoSeq :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> Infinite (Conway a)
veb1Seq :: (OrdRing a, FiniteSignExpansion a) => Veb1Seq a -> Infinite (Conway a)
conwaySeq ConwaySeq {csBase = base, csSign = isAdd, csTerm = tSeq} =
  addBase <$> doSkip (ensureLeadingZero $ monoSeq tSeq)
  where
    addBase = if isAdd then (base `add`) else (base `sub`)
    pLast = trailingArchiClass base
    doSkip =
      case (tSeq, pLast) of
        (Mono1Seq s, Just pL) ->
          -- Skip lower exponents
          -- TODO skip [0, 0, ...] for eps (-1/2)
          if pLim < pL then I.skipWhile (maybe True (> pL) . archiClass) else id
          where
            pLim = toExponent $ limVeb1SeqVebMono s
        (_, _) -> id
    ensureLeadingZero xs@(I.consView -> (isZero -> True, _)) = xs
    ensureLeadingZero xs = I.cons zero xs

-- Added a zero in the beginning to allow the mono1 to be removed at index zero
monoSeq (Mono1Seq vSeq) = veb1Seq vSeq
monoSeq (MonoMultSeq p True) = I.generate (\n -> fromVebMono (p, fromJust $ parseFiniteSE $ fromList [(True, n)]))
monoSeq (MonoMultSeq p False) = I.generate (\n -> fromVebMono (p, fromJust $ parseFiniteSE $ fromList [(True, 1), (False, n)]))

veb1Seq (Veb1ArgSeq o p') = I.generate (veb1 o . I.index pSeq)
  where
    pSeq = conwaySeq p'
veb1Seq (Veb1OrderSeq o' (fromFixBase -> p)) = I.generate ((`veb1` p) . I.index oSeq)
  where
    oSeq = conwaySeq o'
veb1Seq (Veb1IterSeq o (fromFixBase -> base)) = I.iterate (veb1 o) $ veb1 o base
