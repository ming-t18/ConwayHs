{-# LANGUAGE ViewPatterns #-}

module Data.Conway.Simplicity.Seq (toPointOrSeq, conwaySeq, monoSeq, veb1Seq) where

import Data.Conway.Conway
import Data.Conway.Seq.InfList (Infinite)
import qualified Data.Conway.Seq.InfList as I
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion (parseFiniteSE), fromList)
import Data.Conway.Simplicity.Parent
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.Maybe (fromJust)

toPointOrSeq :: (OrdRing a, FiniteSignExpansion a) => ParentSeq a -> Maybe (Either (Conway a) (Infinite (Conway a)))
toPointOrSeq = (rangeElem Left (Right . conwaySeq) <$>)

conwaySeq :: (OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> Infinite (Conway a)
monoSeq :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> Infinite (Conway a)
veb1Seq :: (OrdRing a, FiniteSignExpansion a) => Veb1Seq a -> Infinite (Conway a)
conwaySeq ConwaySeq {csBase = base, csSign = isAdd, csTerm = tSeq}
  | isAdd = (base `add`) <$> monoSeq tSeq
  | otherwise = (base `sub`) <$> monoSeq tSeq

-- TODO minimum exponent constraint on the sequence: w^(-3.5) + [w^-w][i] starts at w^(-3.5) + [w^-4] by skipping terms

-- Added a zero in the beginning to allow the mono1 to be removed at index zero
monoSeq (Mono1Seq vSeq) = I.cons zero $ veb1Seq vSeq
monoSeq (MonoMultSeq p True) = I.generate (\n -> fromVebMono (p, fromJust $ parseFiniteSE $ fromList [(True, n)]))
monoSeq (MonoMultSeq p False) = I.generate (\n -> fromVebMono (p, fromJust $ parseFiniteSE $ fromList [(True, 1), (False, n)]))

veb1Seq (Veb1ArgSeq o p') = I.generate (veb1 o . I.index pSeq)
  where
    pSeq = conwaySeq p'
veb1Seq (Veb1OrderSeq o' (fromFixBase -> p)) = I.generate ((`veb1` p) . I.index oSeq)
  where
    oSeq = conwaySeq o'
veb1Seq (Veb1IterSeq o (fromFixBase -> base)) = zero `I.cons` I.iterate (veb1 o) base
