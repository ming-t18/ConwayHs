{-# LANGUAGE ViewPatterns #-}

module Data.Conway.Simplicity.Parent
  ( ParentSeq,
    ConwaySeq (..),
    MonoSeq (..),
    Veb1Seq (..),
    LeftRight,
    lrConway,
    parentDyadic,
    parentConway,
    parentMono,
    parentVeb1,
  )
where

import Data.Conway.Conway
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion (..))
import qualified Data.Conway.SignExpansion.Dyadic as SED
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses

negateParentSeq :: (OrdZero a, One a) => ParentSeq a -> ParentSeq a
negateParentSeq Nothing = Nothing
negateParentSeq (Just (Left x)) = Just $ Left $ neg x
negateParentSeq (Just (Right x)) = Just $ Right $ negateConwaySeq x

negateConwaySeq :: (OrdZero a, One a) => ConwaySeq a -> ConwaySeq a
negateConwaySeq ConwaySeq {csBase = b, csSign = s, csTerm = t} = ConwaySeq {csBase = neg b, csSign = not s, csTerm = t}

type Direction = Bool

parentDyadic :: (FiniteSignExpansion a) => Direction -> a -> Maybe a
parentDyadic isLeft x = SED.parent isLeft (finiteSE x) >>= parseFiniteSE

lrConway :: (OrdRing a, FiniteSignExpansion a) => Conway a -> LeftRight a
lrConway x = LR (parentConway True x) (parentConway False x)

parentConway :: (OrdRing a, FiniteSignExpansion a) => Direction -> Conway a -> ParentSeq a
parentConway isLeft x =
  do
    (base, (p, c)) <- trailingView x
    let res = parentMono isLeft (p, c)
    case res of
      Nothing -> parentConway isLeft base
      Just (Left s) -> psPoint $ base `add` s
      Just (Right l) -> psLim $ addSeq base l

parentMono :: (OrdRing a, FiniteSignExpansion a) => Direction -> (VebMono a, a) -> ParentSeq a
parentMono isLeft (p, c)
  | isZero c = psEmpty
  | isNegative c = negateParentSeq $ parentMono (not isLeft) (p, neg c)
  | isOne c = do
      p' <- parentVeb1 isLeft p
      case p' of
        Left p'Succ -> psPoint p'Succ
        Right p'Lim -> psLim $ ConwaySeq {csBase = zero, csSign = True, csTerm = p'Lim}
  | otherwise = do
      -- L: V(o, p).c = { V(o, p).c' + V(o, p)'.n | ... }
      -- R: V(o, p).c = { ... | V(o, p).c'' - V(o, p)'.n }
      c' <- parentDyadic isLeft c
      -- let op = if isLeft then add else sub
      let base = fromVebMono (p, c')
      let cs0 = ConwaySeq {csBase = base, csSign = isLeft, csTerm = undefined}
      let p0'Lower = parentVeb1 True p
      case p0'Lower of
        Nothing -> if isLeft then psPoint base else Nothing
        Just (Left p'Succ) -> psPoint $ base `add` p'Succ
        Just (Right p'Lim) -> psLim $ cs0 {csTerm = p'Lim}

fixBaseZero :: FixBase a
fixBaseZero = Nothing

parentVeb1 :: (OrdRing a, FiniteSignExpansion a) => Direction -> VebMono a -> ParentSeq0 a
parentVeb1 isLeft (VebMono (isZero -> True) p) =
  case parentConway isLeft p of
    Nothing -> if isLeft then Just $ Left zero else Nothing
    -- L: V(0, p) = w^{|...} = { 0 | ... } (handled by caller)
    -- R: V(0, p) = w^{...|} = { ... | }
    -- L: V(0, p) = w^{p'|...} = { w^p . n | ... }
    -- R: V(0, p) = w^{...|p''} = { ... | w^p'' . (1 `shr` n)}
    Just (Left p'Succ) -> Just $ Right $ MonoMultSeq (VebMono zero p'Succ) isLeft
    -- L: V(0, p) = w^{p'[n]|...} = { w^p'[n] | ... }
    -- R: V(0, p) = w^{...|p''[n]} = { ... | w^p''[n] }
    Just (Right p'Lim) -> Just $ Right $ Mono1Seq $ Veb1ArgSeq zero p'Lim
parentVeb1 isLeft (VebMono o (isZero -> True))
  | isLeft = do
      co <- parentConway True o
      case co of
        -- Veb1LSuccZero
        Left o'Succ -> Just $ Right $ Mono1Seq $ Veb1IterSeq o'Succ fixBaseZero
        -- Veb1LLimitZero
        Right o'Lim -> Just $ Right $ Mono1Seq $ Veb1OrderSeq o'Lim fixBaseZero
  -- Veb1RSuccZero, Veb1RLimitZero
  | otherwise = Nothing
parentVeb1 isLeft (VebMono o p) = do
  let cp = parentConway isLeft p
  case cp of
    Nothing | isLeft -> do
      -- Veb1LSuccEmpty, Veb1LLimitEmpty
      parentVeb1 True (VebMono o zero)
    -- Veb1RSuccEmpty, Veb1RLimitEmpty
    Nothing -> Nothing
    Just (Left p'Succ) -> do
      co <- parentConway True o
      case co of
        -- Veb1LSuccSucc, Veb1RSuccSucc
        Left o'Succ ->
          let base = Just (VebMono o p'Succ, isLeft)
           in Just $ Right $ Mono1Seq $ Veb1IterSeq o'Succ base
        -- Veb1LLimitSucc, Veb1LRimitSucc
        Right o'Lim ->
          let base = Just (VebMono o p'Succ, isLeft)
           in Just $ Right $ Mono1Seq $ Veb1OrderSeq o'Lim base
    Just (Right p'Lim) -> Just $ Right $ Mono1Seq $ Veb1ArgSeq o p'Lim

addSeq :: (OrdRing a) => Conway a -> ConwaySeq a -> ConwaySeq a
addSeq base0 c@ConwaySeq {csBase = b0} = c {csBase = base0 `add` b0}

-- TODO skip based on reduced SE
