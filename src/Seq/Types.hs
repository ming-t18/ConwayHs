{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Seq.Types (OrdZero (..), Seq (..), ParsableSeq (..)) where

import Conway
import SignExpansion (SignExpansion)
import qualified SignExpansion as SE
import Typeclasses
import Prelude hiding (length, null)

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

instance Seq SignExpansion Ordinal Bool where
  length = SE.length
  (!) = SE.index

-- errorAbsorbedConsume :: Show o => (o, o) -> a
-- errorAbsorbedConsume (lo, hi) = error $ "ParsableSeq: consumed amount is too small to reduce a transfinite amount. (consumed, remain) = " ++ show (lo, hi)

class (OrdZero o, Eq a, Seq s o a) => ParsableSeq s o a where
  lookahead :: s -> Maybe (o, a)
  tryConsume :: s -> (o, a) -> Maybe s
  consume :: s -> (o, a) -> Maybe s

  tryConsume _ (z, _) | isZero z = Nothing
  tryConsume xs p@(n, v) =
    case lookahead xs of
      Nothing -> Nothing
      Just (len, v') | v == v' && n <= len ->
        case consume xs (n, v) of
          Just s' -> Just s'
          Nothing -> error "tryConsume: failed"
      Just _ -> Nothing
