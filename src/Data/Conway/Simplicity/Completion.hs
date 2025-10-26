{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Conway.Simplicity.Completion
  ( Limit (..),
    ParentRepr (..),
    HasParentSeq (..),
    parentSeqSign,
    limParentSeq,
    limParentSeqDir,
    birthdayLimParentSeq,
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
import Data.Either (fromLeft, fromRight)
import Data.Maybe (fromJust, fromMaybe)

-- | Typeclass for type @a@ that represents a sequence that completes to a @limit@ of type @b@
class Limit seq a | seq -> a where
  {-# MINIMAL limit, limitSign #-}

  -- | Completion of the limit.
  limit :: seq -> a

  -- | The sign of the limit, which is either from below (@True@) or from above (@False@)
  limitSign :: seq -> Bool

  limitOrdering :: seq -> Ordering
  limitOrdering s = if limitSign s then LT else GT

-- | Typeclass for the parent sequence (of type @p@) of value of @a@.
--
-- The are two possible parents:
--
-- * Point: @toEither@ returns @Left@
--
-- * Limit: @toEither@ returns @Right@
class (Ord a, Limit seq a) => ParentRepr p a seq | p -> a, p -> seq where
  {-# MINIMAL toEither, fromEither #-}
  toEither :: p -> Either a seq
  fromEither :: Either a seq -> p

  -- parentSeqSign :: Maybe p -> Maybe Bool

  -- | Partial function
  unwrapSeq :: Maybe p -> seq
  unwrapSeq = fromRight undefined . toEither . fromJust

  -- | Partial function
  unwrapPoint :: Maybe p -> a
  unwrapPoint = fromLeft undefined . toEither . fromJust

  ordKey :: p -> (a, Ordering)
  ordKey pr = case toEither pr of
    Left p -> (p, EQ)
    Right s -> (limit s, limitOrdering s)

-- | Typeclass for a type with a "parent sequence" of type @Maybe re@.
class (OrdZero a) => HasParentSeq a re | a -> re where
  {-# MINIMAL parentSeq, parentSeqWithSign, appendSign #-}
  parentSeq :: a -> Maybe re
  parentSeqWithSign :: a -> Maybe (Bool, Maybe re)
  appendSign :: Bool -> a -> a

instance (OrdRing a, FiniteSignExpansion a) => Limit (ConwaySeq a) (Conway a) where
  limit = limConwaySeq
  limitSign = conwaySeqSign

instance (OrdRing a, FiniteSignExpansion a) => Limit (MonoSeq a) (Conway a) where
  limit = limMonoSeq
  limitSign = monoSeqSign

instance (OrdRing a, FiniteSignExpansion a) => Limit (Veb1Seq a) (VebMono a) where
  limit = limVeb1SeqVebMono
  limitSign = veb1SeqSign

instance (OrdRing a, FiniteSignExpansion a) => ParentRepr (RangeElem a) (Conway a) (ConwaySeq a) where
  toEither = rangeElem Left Right
  fromEither = either EPoint ELimit

-- TODO fix
-- instance (OrdRing a, FiniteSignExpansion a) => ParentRepr (RangeElemMono a) (VebMono a) (MonoSeq a) where
--   toEither = rangeElem0 Left Right
--   fromEither = either MPoint MLimit

limParentSeq :: (ParentRepr re a seq) => Maybe re -> Maybe a

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
    (_, (pPart, pLimPart)) = SE.takeCommonPrefix (conwaySE p) (conwaySE pLim)
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

limVeb1Seq = fromVebMono1 . limVeb1SeqVebMono

limVeb1SeqVebMono (Veb1ArgSeq o pSeq) = VebMono o $ limConwaySeq pSeq
limVeb1SeqVebMono (Veb1OrderSeq oSeq Nothing) = VebMono (limConwaySeq oSeq) zero
limVeb1SeqVebMono (Veb1OrderSeq oSeq (Just (vm@(VebMono o p), s))) =
  case compare oLim o of
    LT -> VebMono oLim $ fromVebMono1 vm `add` one
    EQ -> VebMono o $ appendSign s p
    GT -> VebMono oLim zero
  where
    oLim = limConwaySeq oSeq

-- {0, veb1 o 0, veb1 o (veb1 o 0), ...} -> veb1 (o + 1) 0
limVeb1SeqVebMono (Veb1IterSeq o Nothing) = VebMono (o + 1) zero
limVeb1SeqVebMono (Veb1IterSeq o' (Just (vm@(VebMono o p), s))) =
  case compare oSucc o of
    LT -> VebMono oSucc $ fromVebMono1 vm `add` one
    EQ -> VebMono o $ appendSign s p
    GT -> VebMono oSucc zero
  where
    oSucc = appendSign True o'

limParentSeq = (either id limit . toEither <$>)

limParentSeqDir :: (HasParentSeq a re, ParentRepr re a seq) => Bool -> Maybe re -> Maybe a
limParentSeqDir sign = (either (appendSign sign) limit . toEither <$>)

-- | Given a @ParentSeq@, find its birthday limit.
birthdayLimParentSeq :: (OrdRing a, FiniteSignExpansion a) => ParentSeq a -> Ordinal
birthdayLimParentSeq x = maybe zero birthday (limParentSeq x)

instance (OrdRing a, FiniteSignExpansion a) => HasParentSeq (Conway a) (RangeElem a) where
  parentSeq = maybe psEmpty snd . parentSeqWithSign

  parentSeqWithSign x0 =
    case (limL, limR) of
      (Nothing, Nothing) -> Nothing
      (Just _, Nothing) -> Just (True, seqL)
      (Nothing, Just _) -> Just (False, seqR)
      (Just x, Just y) -> if birthday x < birthday y then Just (False, seqR) else Just (True, seqL)
    where
      seqL = parentConway True x0
      seqR = parentConway False x0
      limL = limParentSeqDir True seqL
      limR = limParentSeqDir False seqR

  appendSign s x = parseToConway (conwaySE x SE.+++ SE.single (s, 1))

-- * @Conway@-specific helpers

limConwaySeq :: (OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> Conway a
limMonoSeq :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> Conway a
limVeb1Seq :: (OrdRing a, FiniteSignExpansion a) => Veb1Seq a -> Conway a
limVeb1SeqVebMono :: (OrdRing a, FiniteSignExpansion a) => Veb1Seq a -> VebMono a
appendSignDyadic :: (FiniteSignExpansion a) => Bool -> a -> a

-- | Given a @ConwaySeq@, determine if it is increase or decreasing
conwaySeqSign :: (OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> Bool
conwaySeqSign (ConwaySeq {csSign = sign, csTerm = mSeq}) = (== sign) $ monoSeqSign mSeq

monoSeqSign :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> Bool
monoSeqSign (MonoMultSeq _ b) = b
monoSeqSign (Mono1Seq p) = veb1SeqSign p

veb1SeqSign :: (OrdRing a, FiniteSignExpansion a) => Veb1Seq a -> Bool
veb1SeqSign v = case v of
  (Veb1ArgSeq _ c) -> fromMaybe True $ parentSeqSign $ psLim c
  (Veb1OrderSeq _ b) -> maybe True fixBaseSign b
  (Veb1IterSeq _ b) -> maybe True fixBaseSign b
  where
    fixBaseSign = snd

parentSeqSign :: (ParentRepr p a seq) => Maybe p -> Maybe Bool
parentSeqSign = (>>= (either (const Nothing) (Just . limitSign) . toEither))

appendSignDyadic s c = fromJust $ parseFiniteSE (finiteSE c <> SED.single (s, 1 :: Natural))
