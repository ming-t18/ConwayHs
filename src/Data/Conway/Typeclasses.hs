module Data.Conway.Typeclasses
  ( -- | Typeclasses for algebraic properties related to ordinal and surreal numbers.
    -- Custom numeric types should implement these typeclasses so they can be used in @Conway@.
    Zero (..),
    One (..),
    OrdZero (..),
    AddSub (..),
    Mult (..),
    OrdRing,

    -- * Zero-only type
    ZeroOnly (..),
  )
where

import Data.Conway.Typeclasses.Algebra
import Data.Conway.Typeclasses.ConwayOps ()
