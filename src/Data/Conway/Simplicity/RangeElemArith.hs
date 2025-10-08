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
  ( addOffset,
    addSeq,
    addMono,
    mult',
    -- subCancel,
    -- sub,
    -- mult,
    -- mono1,
    -- veb1,
  )
where

import Data.Conway.Conway (Conway, Ordinal, VebMono, VebMonoI (..), fromVebMono1)
import Data.Conway.Helpers (archiClass, cutOffArchiClass, cutOffArchiClassExclusive)
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Completion
import Data.Conway.Simplicity.HelperTypes
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses (AddSub, One, OrdRing, OrdZero (..), Zero (..))
import qualified Data.Conway.Typeclasses as T
import Data.Maybe (fromJust)

archiClassMonoSeq :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> Conway a

-- * Addition

addOffset :: (OrdRing a, FiniteSignExpansion a) => Conway a -> ConwaySeq a -> ConwaySeq a
addMono :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> MonoSeq a -> MonoSeq a

-- * Multiplication

-- * Others

-- sub :: MonoSeq a -> MonoSeq a -> [MonoSeq a]
-- subCancel :: MonoSeq a -> MonoSeq a -> Maybe (Either (MonoSeq a) (MonoSeq a))
-- mult :: (AddSub a, One a, OrdRing a, FiniteSignExpansion a) => MonoSeq a -> MonoSeq a -> [MonoSeq a]
-- mono1 :: MonoSeq a -> MonoSeq a
-- veb1 :: Ordinal -> MonoSeq a -> MonoSeq a

archiClassMonoSeq = fromJust . archiClass . limMonoSeq

addOffset off cs@ConwaySeq {csBase = base, csSign = _, csTerm = seqTerm}
  | isZero off = cs
  | otherwise = cs {csBase = base''}
  where
    base' = off `T.add` base
    pTerm = archiClassMonoSeq seqTerm
    absorb = case seqTerm of
      MonoMultSeq _ True -> True
      _ -> False
    base'' = if absorb then cutOffArchiClassExclusive pTerm base' else cutOffArchiClass pTerm base'

addSeq :: (OrdRing a, FiniteSignExpansion a) => ConwaySeq a -> ConwaySeq a -> OneOrTwo (ConwaySeq a)
addSeq ConwaySeq {csBase = base1, csSign = s1, csTerm = t1} ConwaySeq {csBase = base2, csSign = s2, csTerm = t2} =
  fmap (\(Signed (s'', t'')) -> normalize $ ConwaySeq {csBase = base1 `T.add` base2, csSign = s'', csTerm = t''}) t'
  where
    normalize cs3@ConwaySeq {csBase = base3} = addOffset base3 $ cs3 {csBase = zero}
    t' = case (s1, s2) of
      (False, False) -> One $ signedNeg (t1 `addMono` t2)
      (True, True) -> One $ signedPos (t1 `addMono` t2)
      (True, False) -> t1 `subMono` t2
      (False, True) -> t2 `subMono` t1

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

addExponents :: (AddSub a, One a) => VebMono a -> VebMono a -> VebMono a
addExponents a b = VebMono zero (fromVebMono1 a `T.add` fromVebMono1 b)

mult' :: (OrdRing a, FiniteSignExpansion a) => MonoSeq a -> MonoSeq a -> [MonoSeq a]
mult' s1@(Mono1Seq p1) s2@(Mono1Seq p2) = if limVeb1Seq p1 > limVeb1Seq p2 then [s1] else [s2]
mult' (MonoMultSeq p1 d1) (MonoMultSeq p2 d2) =
  case (d1, d2) of
    -- w^a.j * w^b.k = w^(a + b).k
    (True, True) -> [MonoMultSeq s' d1]
    -- w^a.(-> 0) * w^b.(-> 0) = w^(a + b).(-> 0)
    (False, False) -> [MonoMultSeq s' d1]
    -- w^a.(-> 0) * w^b.k = two possibilities above
    (True, False) -> MonoMultSeq s' <$> ft
    (False, True) -> MonoMultSeq s' <$> ft
  where
    s' = addExponents p1 p2
    ft = [False, True]
mult' (MonoMultSeq p1 d1) (Mono1Seq p2) = error "TODO"
  where
    l2 = limVeb1Seq p2
mult' (Mono1Seq p1) (MonoMultSeq p2 d2) = error "TODO"
  where
    l1 = limVeb1Seq p1
