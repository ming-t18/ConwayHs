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
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Completion (ordKey)
import Data.Conway.Simplicity.SeqArith (mono1Seq, veb1Seq)
import Data.Conway.Simplicity.Types
import Data.Conway.Typeclasses
import qualified Data.Conway.Typeclasses.ConwayOps as CO
import Data.Function (on)

instance (OrdZero a, One a, OrdRing a, FiniteSignExpansion a) => Ord (RangeElem a) where
  compare = compare `on` ordKey

-- TODO
-- instance Seq (Veb1Seq a) Natural (VebMono a)
--
-- instance Seq (MonoSeq a) Natural (Conway a)
--
-- instance Seq (ConwaySeq a) Natural (Conway a)

instance CO.Veb Ordinal (ConwaySeq a) where
  veb1 = veb1Seq
  mono1 = mono1Seq

instance (OrdRing a) => CO.Veb Ordinal (RangeElem a) where
  veb1 o = rangeElem (EPoint . veb1 o) (ELimit . veb1Seq o)
  mono1 = rangeElem (EPoint . mono1) (ELimit . mono1Seq)
