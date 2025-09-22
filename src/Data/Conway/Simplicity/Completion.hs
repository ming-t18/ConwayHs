{-# LANGUAGE ViewPatterns #-}

module Data.Conway.Simplicity.Completion
  ( limConwaySeq,
    limMonoSeq,
    limVeb1Seq,
    limParentSeq,
    limLR,
    parentSeq,
  )
where

import Data.Conway.Conway
import Data.Conway.SignExpansion (parseToConway)
import Data.Conway.SignExpansion.Conway (birthday, conwaySE)
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion (..))
import qualified Data.Conway.SignExpansion.Dyadic as SED
import qualified Data.Conway.SignExpansion.Types as SE
import Data.Conway.Simplicity.Parent (parentConway)
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.Maybe (fromJust, fromMaybe)

appendSign :: (OrdRing a, FiniteSignExpansion a) => Bool -> Conway a -> Conway a
limConwaySeq :: (OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> Conway a
limMonoSeq :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> Conway a
limVeb1Seq :: (OrdRing a, FiniteSignExpansion a) => Veb1Seq a -> Conway a
limParentSeq :: (OrdRing a, FiniteSignExpansion a) => ParentSeq a -> Maybe (Conway a)
limLR :: (OrdRing a, FiniteSignExpansion a) => LeftRight a -> Conway a
appendSignDyadic :: (FiniteSignExpansion a) => Bool -> a -> a
appendSignDyadic s c = fromJust $ parseFiniteSE (finiteSE c <> SED.single (s, 1 :: Natural))
appendSign s x = parseToConway (conwaySE x <> SE.single (s, 1))

-- | Complete the limit @base + w^{pLim}@ where @pLim is a limit sequence@.
--
-- Let @w^p.c@ be the trailing term of @base@.
--
-- The cases of @base' + w^p.c +/- w^pLim = ?@:
--
-- * @p > pLim@: @= base' + w^p.c + w^pLim@
--
-- * @p = pLim@: @= base' + w^p.(c & +/-)@
--
-- * @p < pLim && unreduceCheck@: @= base' + w^p.(c & +/-)@
--     where @unreduceCheck@ is true if and only if @p = pLim & [-^k]@ for some ordinal @k@
--
-- * otherwise: @= base'@
limConwaySeq cs0@ConwaySeq {csBase = base, csSign = s, csTerm = tSeq} =
  case trailingView base of
    Nothing -> addBase $ limMonoSeq tSeq
    Just (base', (v@(fromVebMono1 -> p), c)) ->
      case p `compare` pLim of
        GT -> addBase pLim
        cmp
          | cmp == EQ || unreduceCheck -> base' `add` fromVebMono (v, c')
          where
            c' = appendSignDyadic (if s then isPositive pLim else isNegative pLim) c
            unreduceCheck = onlyMinusesBetween p pLim
        -- "absorbed" case
        _ -> limConwaySeq cs0 {csBase = base'}
  where
    addBase = if s then (base `add`) else (base `sub`)
    pLim = limMonoSeq tSeq

-- | True if and only if @p@ equals @pLim@ with a non-zero number of minuses after it.
onlyMinusesBetween :: (OrdZero a, One a, FiniteSignExpansion a) => Conway a -> Conway a -> Bool
onlyMinusesBetween p pLim = pCond && pLimCond
  where
    pSE = conwaySE p
    pLimSE = conwaySE pLim
    (_, (pPart, pLimPart)) = SE.takeCommonPrefix pSE pLimSE
    pLimCond = isZero pLimPart
    pCond =
      case SE.toList pPart of
        [(False, _)] -> True
        _ -> False

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

limParentSeqDir :: (OrdRing a, FiniteSignExpansion a) => Bool -> Maybe (Either (Conway a) (ConwaySeq a)) -> Maybe (Conway a)
limParentSeqDir sign = (either (appendSign sign) limConwaySeq <$>)

limLR (LR l r) =
  case (limL, limR) of
    (Nothing, Nothing) -> zero
    (Just x, Nothing) -> x
    (Nothing, Just x) -> x
    (Just x, Just y) -> if birthday x < birthday y then y else x
  where
    limL = limParentSeqDir True l
    limR = limParentSeqDir False r

-- | Given a @Conway@, find its immediate parent sequence.
parentSeq :: (OrdRing a, FiniteSignExpansion a) => Conway a -> ParentSeq a
parentSeq x0 =
  case (limL, limR) of
    (Nothing, Nothing) -> psEmpty
    (Just _, Nothing) -> seqL
    (Nothing, Just _) -> seqR
    (Just x, Just y) -> if birthday x < birthday y then seqR else seqL
  where
    seqL = parentConway True x0
    seqR = parentConway False x0
    limL = limParentSeqDir True seqL
    limR = limParentSeqDir False seqR

tryGetPoint :: ParentSeq a -> Maybe (Conway a)
tryGetPoint (Just (Left x)) = Just x
tryGetPoint _ = Nothing
