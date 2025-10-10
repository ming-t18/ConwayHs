{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Typeclass instances for sequences/ranges.
--
-- For external API consumers only.
module Data.Conway.Simplicity.Instances
  (
  )
where

import Data.Conway.Conway
import Data.Conway.Seq
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Completion
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import Data.Function (on)

instance (OrdZero a, One a, OrdRing a, FiniteSignExpansion a) => Ord (RangeElem a) where
  compare = compare `on` ordKey

-- TODO
-- instance Seq (Veb1Seq a) Natural (VebMono a)
--
-- instance Seq (MonoSeq a) Natural (Conway a)
--
-- instance Seq (ConwaySeq a) Natural (Conway a)
