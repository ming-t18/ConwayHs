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
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import qualified Data.Conway.SignExpansion.Types as SE
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses

appendSign :: (OrdRing a, FiniteSignExpansion a) => Bool -> Conway a -> Conway a
limConwaySeq :: (Show a, OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> Conway a
limMonoSeq :: (Show a, OrdRing a, FiniteSignExpansion a) => MonoSeq a -> Conway a
limVeb1Seq :: (Show a, OrdRing a, FiniteSignExpansion a) => Veb1Seq a -> Conway a
limParentSeq :: (Show a, OrdRing a, FiniteSignExpansion a) => ParentSeq a -> Maybe (Conway a)
limLR :: (Show a, OrdRing a, FiniteSignExpansion a) => LeftRight a -> Conway a
appendSign True x = parseToConway (conwaySE x <> SE.plus 1)
appendSign False x = parseToConway (conwaySE x <> SE.minus 1)

limConwaySeq ConwaySeq {csBase = base, csSign = s, csTerm = tSeq}
  | s = base `add` limMonoSeq tSeq
  | otherwise = base `sub` limMonoSeq tSeq

limMonoSeq (Mono1Seq v1Seq) = limVeb1Seq v1Seq
limMonoSeq (MonoMultSeq (VebMono (isZero -> True) p) sign) = mono1 $ appendSign sign p
limMonoSeq (MonoMultSeq vm@(VebMono _ _) sign) = mono1 $ appendSign sign p'
  where
    p' = mono1 $ appendSign sign $ fromVebMono1 vm

limVeb1Seq (Veb1ArgSeq o pSeq) = fromVebMono1 $ VebMono o $ limConwaySeq pSeq
-- TODO containing plus 1/minus 1?
limVeb1Seq (Veb1OrderSeq oSeq p) = fromVebMono1 $ VebMono (limConwaySeq oSeq) p
-- TODO doesn't work: need to extract the order first
limVeb1Seq (Veb1IterSeq o p s) =
  case leadingView p of
    Nothing -> fromVebMono1 $ VebMono o $ appendSign s zero
    Just ((VebMono o' p', isOne -> True), isZero -> True)
      | o < o' ->
          -- TODO check requirements on o'
          fromVebMono1 $ VebMono o' $ appendSign s p'
    v -> error $ "limVeb1Seq: unable to extract completion: " ++ show v

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
