{-# LANGUAGE ViewPatterns #-}

-- | Range arithmetic
--
-- This module handles the arithmetic operations on surreal sequences of type @ConwaySeq@, @MonoSeq@ and @Veb1Seq@.
--
-- * Basic operations
--
-- Power: @mono1@ @veb1@
--
-- Natural: @add@ @mult@
--
-- Ordinal: @ordAdd@ @ordMult@ @ordPow@
--
-- * Addition
module Data.Conway.Simplicity.RangeElemArith
  ( -- * Addition and Subtraction
    addOffset,
    addSeq,
    subSeq,
    negConwaySeq,
    addMono,

    -- * Multiplication
    multSeqByConst,
    multSeq,
    multMonoSeq,
    multMonoSeqByConst,
    -- mono1,
    -- veb1,
  )
where

import Data.Conway.Conway (Conway, VebMono, VebMonoI (..), fromVebMono1, leadingView)
import Data.Conway.Helpers (archiClass)
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Completion
import Data.Conway.Simplicity.ConwaySeq
import Data.Conway.Simplicity.HelperTypes
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses (AddSub (..), One, OrdRing, OrdZero (..), Zero (..))
import qualified Data.Conway.Typeclasses as T
import Data.Maybe (fromJust, maybeToList)

-- sub :: MonoSeq a -> MonoSeq a -> [MonoSeq a]
-- subCancel :: MonoSeq a -> MonoSeq a -> Maybe (Either (MonoSeq a) (MonoSeq a))
-- mult :: (AddSub a, One a, OrdRing a, FiniteSignExpansion a) => MonoSeq a -> MonoSeq a -> [MonoSeq a]
-- mono1 :: MonoSeq a -> MonoSeq a
-- veb1 :: Ordinal -> MonoSeq a -> MonoSeq a

-- * Addition and Subtraction

addSeq, subSeq :: (OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> ConwaySeq a -> OneOrTwo (ConwaySeq a)
addSeq ConwaySeq {csBase = base1, csSign = s1, csTerm = t1} ConwaySeq {csBase = base2, csSign = s2, csTerm = t2} =
  fmap (\(Signed (s'', t'')) -> normalize $ ConwaySeq {csBase = base1 `add` base2, csSign = s'', csTerm = t''}) t'
  where
    normalize cs3@ConwaySeq {csBase = base3} = addOffset base3 $ cs3 {csBase = zero}
    t' = case (s1, s2) of
      (False, False) -> One $ signedNeg (t1 `addMono` t2)
      (True, True) -> One $ signedPos (t1 `addMono` t2)
      (True, False) -> t1 `subMono` t2
      (False, True) -> t2 `subMono` t1
subSeq s1 s2 = s1 `addSeq` negConwaySeq s2

addMono :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> MonoSeq a -> MonoSeq a
addMono s1 s2 =
  -- w^[-> a] + w^[-> b] = w^[-> a] if a > b
  -- w^[-> a] + w^[-> b].k = w^[-> a]
  -- w^[-> a] + w^[-> b].2^-k = w^[-> a]
  case archiClassMonoSeq s1 `compare` archiClassMonoSeq s2 of
    LT -> s2
    GT -> s1
    EQ ->
      case (s1, s2) of
        (Mono1Seq _, Mono1Seq _) -> s1
        (MonoMultSeq _ d1, MonoMultSeq _ d2) ->
          case (d1, d2) of
            (True, True) -> s1
            (True, False) -> s1
            (False, True) -> s2
            (False, False) -> s1
        -- w^p.k + w^[-> p] = w^p(-> k + 1) = w^p
        -- w^p.2^(-k) + w^[-> p] = w^p.(-> 0) + w^[-> p] = w^[-> p]
        (MonoMultSeq _ d1, Mono1Seq _) -> if d1 then s1 else s2
        (Mono1Seq _, MonoMultSeq _ d2) -> if d2 then s2 else s1

subMono :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> MonoSeq a -> OneOrTwo (Signed (MonoSeq a))
subMono s1 s2 =
  case archiClassMonoSeq s1 `compare` archiClassMonoSeq s2 of
    LT -> rhs
    GT -> lhs
    EQ ->
      case (s1, s2) of
        (Mono1Seq _, Mono1Seq _) -> diverge
        (MonoMultSeq _ d1, MonoMultSeq _ d2) ->
          case (d1, d2) of
            (True, True) -> diverge
            (False, False) -> diverge
            (True, False) -> lhs
            (False, True) -> rhs
        (MonoMultSeq _ d1, Mono1Seq _) -> if d1 then lhs else rhs
        (Mono1Seq _, MonoMultSeq _ d2) -> if d2 then rhs else lhs
  where
    lhs = One $ signedPos s1
    rhs = One $ signedNeg s2
    diverge = Two (signedNeg s1) (signedPos s1)

addMonoSigned :: (OrdRing a, FiniteSignExpansion a) => Signed (MonoSeq a) -> Signed (MonoSeq a) -> OneOrTwo (Signed (MonoSeq a))
addMonoSigned (Signed (sx, x)) (Signed (sy, y)) =
  case (sx, sy) of
    (True, True) -> One $ signedPos $ x `addMono` y
    (False, False) -> One $ signedNeg $ x `addMono` y
    (True, False) -> x `subMono` y
    (False, True) -> y `subMono` x

-- * Multiplication

addExponents :: (AddSub a, One a) => VebMono a -> VebMono a -> VebMono a
addExponents va@(VebMono pa a) vb@(VebMono pb b) =
  case (isZero pa, isZero pb) of
    (True, True) -> VebMono zero (a `add` b)
    (True, False) -> VebMono zero (a `add` fromVebMono1 vb)
    (False, True) -> VebMono zero (fromVebMono1 va `add` b)
    (False, False) -> VebMono zero (fromVebMono1 va `add` fromVebMono1 vb)

offsetExponents :: (OrdRing a, FiniteSignExpansion a) => VebMono a -> Veb1Seq a -> Veb1Seq a
offsetExponents vOff b = Veb1ArgSeq zero $ addOffset (fromVebMono1 vOff) $ fromMonoSeq $ Mono1Seq b

multMonoSeq :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> MonoSeq a -> OneOrTwo (MonoSeq a)
multMonoSeq s1@(Mono1Seq p1) s2@(Mono1Seq p2) = if limVeb1Seq p1 > limVeb1Seq p2 then One s1 else One s2
multMonoSeq (MonoMultSeq p1 d1) (MonoMultSeq p2 d2) =
  case (d1, d2) of
    -- w^a.j * w^b.k = w^(a + b).k
    (True, True) -> One $ MonoMultSeq s' d1
    -- w^a.(-> 0) * w^b.(-> 0) = w^(a + b).(-> 0)
    (False, False) -> One $ MonoMultSeq s' d1
    -- w^a.(-> 0) * w^b.k = two possibilities
    -- (False, True) and (True, False)
    _ -> MonoMultSeq s' <$> ft
  where
    s' = addExponents p1 p2
    ft = Two False True
multMonoSeq (MonoMultSeq p1 _) (Mono1Seq p2) = One $ Mono1Seq $ offsetExponents p1 p2
multMonoSeq (Mono1Seq p1) (MonoMultSeq p2 _) = One $ Mono1Seq $ offsetExponents p2 p1

multMonoSeqByPositive :: (OrdRing a, FiniteSignExpansion a) => Conway a -> MonoSeq a -> MonoSeq a
-- a ~ 1, a S = S
multMonoSeqByPositive ((isZero <$>) . archiClass -> Just True) ms = ms
multMonoSeqByPositive a@(leadingView -> Just ((vm, _), _)) ms = case ms of
  -- a ~ w^c, a w^P = w^(c + p)
  Mono1Seq (Veb1ArgSeq (isZero -> True) pSeq) -> Mono1Seq $ Veb1ArgSeq zero $ addOffset (fromJust $ archiClass a) pSeq
  -- a ~ w^(veb1 o p), a w^(veb1 ...) = w^(c + veb1 ...)
  Mono1Seq vs -> Mono1Seq $ Veb1ArgSeq zero $ addOffset c (ConwaySeq zero True $ Mono1Seq vs)
  -- a ~ w^c, a (w^p.R) = w^(a + p).R
  MonoMultSeq b s -> MonoMultSeq (vm `addExponents` b) s
  where
    c = fromVebMono1 vm
multMonoSeqByPositive _ _ = error "multMonoSeqByConst: multiplier is zero"

multMonoSeqByConst :: (OrdRing a, FiniteSignExpansion a) => Conway a -> MonoSeq a -> Maybe (Signed (MonoSeq a))
multMonoSeqByConst c m
  | isZero c = Nothing
  | isNegative c = Just $ signedNeg $ multMonoSeqByPositive (neg c) m
  | otherwise = Just $ signedPos $ multMonoSeqByPositive c m

multSeq :: (OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> ConwaySeq a -> [ConwaySeq a]
multSeq ConwaySeq {csBase = a, csSign = s1, csTerm = x} ConwaySeq {csBase = b, csSign = s2, csTerm = y} =
  (\(Signed (sign, z)) -> addOffset ab ConwaySeq {csBase = zero, csSign = sign, csTerm = z})
    <$> res
  where
    ab = a `T.mult` b
    xy' = x `multMonoSeq` y
    bx' = b `multMonoSeqByConst` x
    ay' = a `multMonoSeqByConst` y
    s1s2 = s1 /= s2
    res = do
      xy <- listFrom12 $ withSign s1s2 <$> xy'
      bx <- maybeToList bx'
      ay <- maybeToList ay'
      bxay <- listFrom12 $ addMonoSigned (s1 `flipSigned` bx) (s2 `flipSigned` ay)
      listFrom12 $ addMonoSigned bxay xy

-- (a + s1 X)(b + s2 Y) = a b + ((s1 b X + s2 a Y) + s1 s2 X Y)
--                      = a b + (sbxay BXAY + s1s2 X Y)

multSeqByConst :: (OrdRing a, FiniteSignExpansion a) => Conway a -> ConwaySeq a -> Maybe (ConwaySeq a)
multSeqByConst a ConwaySeq {csBase = b, csSign = s2, csTerm = y} =
  fromSignedMonoSeqOffset ab <$> ay'
  where
    ab = a `T.mult` b
    ay' = (s2 `flipSigned`) <$> (a `multMonoSeqByConst` y)

-- a(b + s2 Y) = a b + s2 a Y
