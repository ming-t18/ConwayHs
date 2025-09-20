{-# LANGUAGE ViewPatterns #-}

-- | Let @S + veb o p c@ be a @Conway@ with a trailing term.
--
-- Let @'@ be the left parent of a surreal number, and @''@ be the right parent.
--
-- The range can be empty (zero), singleton (successor) or range (limit).
--
-- @n = 0, 1, 2, ...@ is the index of a limit range.
--
-- Sum of terms rules:
--
--   * SumL: @(S + veb o p c)' = S + (veb1 o p c)'@
--
--   * SumR: @(S + veb o p c)'' = S + (veb1 o p c)''@
--
-- If the last monomial has an empty range, remove the last term and try again with the second last term.
-- This process repeats from the rightmost term to the first term until the first term with non-empty
-- range has been found or if all terms have been exhausted.
--
-- Monomial with non-trivial coefficient rules:
--
--   * CoeffLSucc: @(mono p c)' = mono p c' + mono p' n@
--
--   * CoeffRSucc: @(mono p c)'' = mono p c'' - mono p' n@
--
--   * CoeffLLimit: @(mono p c)' = {0, mono p' c}@
--
--   * CoeffRLimit: @(mono p c)'' = mono p''@
--
-- Monomial with coefficient of 1 rules:
--
--   * Mono1LEmpty: @(mono1 p)' = 0@ where @p'@ is empty
--
--   * Mono1REmpty: @(mono1 p)'' = {}@ where @p''@ is empty
--
--   * Mono1LSucc: @(mono1 p)' = veb 0 p' n@
--
--   * Mono1RSucc: @(mono1 p)'' = veb 0 p'' (1 `shr` n)@
--
--   * Mono1LLimit: @(mono1 p)' = {0, mono1 p'}@
--
--   * Mono1RLimit: @(mono1 p)'' = mono1 p''@
--
-- * Veb1 rules
--
-- The @Veb1@ rules are based on the "CGV Googology part 1: veblen function" definition of the surreal single-argument Veblen function:
--
-- @veb1 o p = { iterate (veb1 o') {0, p' * n} | iterate (veb1 o') (p'' * (1 `shr` n)) }@
--
-- where @n@ is the range @{0, 1, 2, 3, 4, ...}@ and @1 `shr` n@ is the range @{1, 1/2, 1/4, 1/8, 1/16, ...}@
--
-- Zero argument:
--
--   * Veb1LSuccZero: @(veb1 o 0)' = iterate (veb1 o') 0@
--
--   * Veb1RSuccZero: @(veb1 o 0)'' = {}@
--
--   * Veb1LLimitZero: @(veb1 o 0)' = veb1 o' 0@
--
--   * Veb1RLimitZero: @(veb1 o 0)'' = {}@
--
-- Empty argument:
--
--   * Veb1LSuccEmpty: @(veb1 o p)' = veb1 o' 0@ where @p'@ is empty
--
--   * Veb1RSuccEmpty: @(veb1 o p)'' = {}@ where @p''@ is empty
--
-- Successor argument:
--
--   * Veb1LSuccSucc: @(veb1 o p)' = iterate (veb1 o') (veb1 o p' + 1)@
--
--   * Veb1RSuccSucc: @(veb1 o p)'' = iterate (veb1 o') (veb1 o p'' - 1)@
--
--   * Veb1LLimitSucc: @(veb1 o p)' = veb1 o' (veb1 o p' + 1)@
--
--   * Veb1RLimitSucc: @(veb1 o p)'' = veb1 o' (veb1 o p'' - 1)@
--
-- Limit argument:
--
--   * Veb1LSuccLimit: @(veb1 o p)' = veb1 o p'@
--
--   * Veb1RSuccLimit: @(veb1 o p)'' = veb1 o p''@
--
--   * Veb1LLimitLimit: @(veb1 o p)' = veb1 o p'@
--
--   * Veb1RLimitLimit: @(veb1 o p)'' = veb1 o p''@
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
        Left o'Succ -> Just $ Right $ Mono1Seq $ Veb1IterSeq o'Succ zero isLeft
        -- Veb1LLimitZero
        Right o'Lim -> Just $ Right $ Mono1Seq $ Veb1OrderSeq o'Lim zero
  -- Veb1RSuccZero, Veb1RLimitZero
  | otherwise = Nothing
parentVeb1 isLeft (VebMono o p) = do
  let cp = parentConway isLeft p
  case cp of
    -- Veb1RSuccEmpty, Veb1RLimitEmpty
    Nothing | not isLeft -> Nothing
    Nothing -> do
      co <- parentConway True o
      case co of
        -- Veb1LSuccEmpty
        Left o'Succ -> parentVeb1 True (VebMono o'Succ zero)
        -- Veb1LLimitEmpty
        Right o'Lim -> Just $ Right $ Mono1Seq $ Veb1OrderSeq o'Lim zero
    Just (Left p'Succ) -> do
      co <- parentConway True o
      case co of
        -- Veb1LSuccSucc, Veb1RSuccSucc
        Left o'Succ -> Just $ Right $ Mono1Seq $ Veb1IterSeq o'Succ (veb1 o p'Succ) isLeft
        -- Veb1LLimitSucc, Veb1LRimitSucc
        Right o'Lim ->
          let off = getIterOffset isLeft
           in Just $ Right $ Mono1Seq $ Veb1OrderSeq o'Lim (off $ veb1 o p'Succ)
    Just (Right p'Lim) -> Just $ Right $ Mono1Seq $ Veb1ArgSeq o p'Lim

getIterOffset :: (AddSub a, One a) => Bool -> a -> a
getIterOffset isLeft = if isLeft then (`add` one) else (`sub` one)

addSeq :: (OrdRing a) => Conway a -> ConwaySeq a -> ConwaySeq a
addSeq base0 c@ConwaySeq {csBase = b0} = c {csBase = base0 `add` b0}
