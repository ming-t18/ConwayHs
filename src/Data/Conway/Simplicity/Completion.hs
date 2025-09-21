{-# LANGUAGE ViewPatterns #-}

module Data.Conway.Simplicity.Completion
  ( limConwaySeq,
    limMonoSeq,
    limVeb1Seq,
    limParentSeq,
    limLR,
  )
where

import Data.Conway.Conway
import Data.Conway.SignExpansion (parseToConway)
import Data.Conway.SignExpansion.Conway (birthday, conwaySE)
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion (..))
import qualified Data.Conway.SignExpansion.Dyadic as SED
import qualified Data.Conway.SignExpansion.Types as SE
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.Maybe (fromJust)

appendSign :: (OrdRing a, FiniteSignExpansion a) => Bool -> Conway a -> Conway a
limConwaySeq :: (Show a, OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> Conway a
limMonoSeq :: (Show a, OrdRing a, FiniteSignExpansion a) => MonoSeq a -> Conway a
limVeb1Seq :: (Show a, OrdRing a, FiniteSignExpansion a) => Veb1Seq a -> Conway a
limParentSeq :: (Show a, OrdRing a, FiniteSignExpansion a) => ParentSeq a -> Maybe (Conway a)
limLR :: (Show a, OrdRing a, FiniteSignExpansion a) => LeftRight a -> Conway a
appendSignDyadic :: (FiniteSignExpansion a) => Bool -> a -> a
appendSignDyadic s c = fromJust $ parseFiniteSE (finiteSE c <> SED.single (s, 1 :: Natural))
appendSign s x = parseToConway (conwaySE x <> SE.single (s, 1))

limConwaySeq cs0@ConwaySeq {csBase = base, csSign = s, csTerm = tSeq} =
  case trailingView base of
    Nothing -> addBase $ limMonoSeq tSeq
    Just (base', (v@(fromVebMono1 -> p), c)) ->
      let pLim = limMonoSeq tSeq
       in case p `compare` pLim of
            LT -> limConwaySeq cs0 {csBase = base'}
            EQ ->
              let c' = appendSignDyadic (if s then isPositive pLim else isNegative pLim) c
               in base' `add` fromVebMono (v, c')
            GT -> addBase pLim
  where
    addBase = if s then (base `add`) else (base `sub`)

--  | s = base `add` limMonoSeq tSeq
--  | otherwise = base `sub` limMonoSeq tSeq

-- break up base, check if adding a minus is needed

limMonoSeq (Mono1Seq v1Seq) = limVeb1Seq v1Seq
limMonoSeq (MonoMultSeq (VebMono (isZero -> True) p) sign) = mono1 $ appendSign sign p
limMonoSeq (MonoMultSeq vm@(VebMono _ _) sign) = mono1 $ appendSign sign p'
  where
    p' = mono1 $ appendSign sign $ fromVebMono1 vm

limVeb1Seq (Veb1ArgSeq o pSeq) = fromVebMono1 $ VebMono o $ limConwaySeq pSeq
limVeb1Seq (Veb1OrderSeq oSeq Nothing) = fromVebMono1 $ VebMono (limConwaySeq oSeq) zero
-- TODO doesn't verify if the inner order makes sense
limVeb1Seq (Veb1OrderSeq oSeq (Just (VebMono _o' p, s))) = fromVebMono1 $ VebMono (limConwaySeq oSeq) $ appendSign s p
-- {0, veb1 o 0, veb1 o (veb1 o 0), ...} -> veb1 (o + 1) 0
limVeb1Seq (Veb1IterSeq o Nothing) = fromVebMono1 $ VebMono (o + 1) zero
-- TODO doesn't verify if the outer order makes sense
limVeb1Seq (Veb1IterSeq _o' (Just (VebMono o p, s))) =
  fromVebMono1 $ VebMono o $ appendSign s p

limParentSeq = (either id limConwaySeq <$>)

limLR (LR l r) =
  case (limL, limR) of
    (Nothing, Nothing) -> zero
    (Just x, Nothing) -> x
    (Nothing, Just x) -> x
    (Just x, Just y) -> if birthday x < birthday y then y else x
  where
    limL = limParentSeq l
    limR = limParentSeq r
