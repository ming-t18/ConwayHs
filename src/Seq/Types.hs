{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Seq.Types (OrdZero (..)) where

import Conway
import SignExpansion (SignExpansion)
import qualified SignExpansion as SE
import Typeclasses
import Prelude hiding (length, null)

-- | A transfinite sequence of type @s@,
-- indexed by index type @o@,
-- and value type @a@.
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
