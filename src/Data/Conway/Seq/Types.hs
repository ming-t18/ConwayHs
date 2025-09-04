{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.Conway.Seq.Types (OrdZero (..), Seq (..), ParsableSeq (..), RunLengthSeq (..)) where

import Data.Conway.Typeclasses
import Prelude hiding (length, null, replicate)

-- | A transfinite sequence of type @s@, indexed by index type @o@,
-- and value type @a@. The length of the sequence is also @o@.
class (OrdZero o) => Seq s o a | s -> o, s -> a where
  -- | Length (order type) of the sequence.
  length :: s -> o

  -- | Indexing function. Errors if the index is out of bounds.
  (!) :: s -> o -> a

  null :: s -> Bool
  null = isZero . length

  head :: s -> a
  head = (! zero)

  -- | Alias of @length@
  seqLength :: s -> o
  seqLength = length

  -- | Alias of @(!)@
  seqIndex :: s -> o -> a
  seqIndex = (!)

-- errorAbsorbedConsume :: Show o => (o, o) -> a
-- errorAbsorbedConsume (lo, hi) = error $ "ParsableSeq: consumed amount is too small to reduce a transfinite amount. (consumed, remain) = " ++ show (lo, hi)

-- | Typeclass for parsing transfinite sequences by prefix run-lengths.
class (OrdZero o, Eq a, Seq s o a) => ParsableSeq s o a where
  lookahead :: s -> Maybe (a, o)
  tryConsume :: s -> (a, o) -> Maybe s
  consume :: s -> (a, o) -> Maybe s

  tryConsume _ (_, z) | isZero z = Nothing
  tryConsume xs t@(v, n) =
    case lookahead xs of
      Nothing -> Nothing
      Just (v', len) | v == v' && n <= len ->
        case consume xs t of
          Just s' -> Just s'
          Nothing -> error "tryConsume: failed"
      Just _ -> Nothing

-- | Typeclass for constructing transfinite sequences by prefix run-lengths.
-- Aside from monoid operations for sequence conat, the @replicate@
-- function creates a run-length sequence.
class (Monoid s, OrdZero o, Eq a, Seq s o a) => RunLengthSeq s o a where
  replicate :: o -> a -> s

  -- | Alias of replicate
  rep :: o -> a -> s
  rep = replicate
