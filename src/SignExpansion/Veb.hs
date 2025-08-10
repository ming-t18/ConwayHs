module SignExpansion.Veb (mono1SE, mono1SE', veb1SE, veb1SE', veb1SELead, mono1SELead) where

import Control.Arrow (second)
import Conway
import Data.Foldable (foldl')
import OrdinalArith
import SignExpansion.Types

m1 :: Ordinal -> Ordinal
m1 = mono1

-- | Given a sign expansion, generate an output sign expansion while keeping track of a state.
transform :: (a -> (Bool, Ordinal) -> (a, SignExpansion)) -> a -> SignExpansion -> (a, SignExpansion)
transform f a0 = foldl' (\(a, s) -> second (s +++) . f a) (a0, empty) . toList

-- | Given the sign expansion of @x@, return the sign expansion of @mono1 x@.
mono1SE :: SignExpansion -> SignExpansion

-- | Like @mono1SE@, except takes the accumulator as the first argument
-- and returns the accumulator after generating the sign expansion.
-- The accumulator is the number of pluses in the input so far.
mono1SE' :: Ordinal -> SignExpansion -> (Ordinal, SignExpansion)

mono1SE = (mono1SELead `consSE`) . snd . mono1SE' 0

mono1SE' = transform f
  where
    f a (True, n) = (a', plus $ m1 a') where a' = a `ordAdd` n
    f a (False, n) = (a, minus $ m1 (a `ordAdd` 1) `ordMult` n)

-- | Given Veblen order @o@ and the sign expansion of @x@, return the sign expansion of @veb1 o x@.
veb1SE :: Ordinal -> SignExpansion -> SignExpansion

-- | Like @veb1SE@, except takes the accumulator as the second argument
-- and returns the accumulator after generating the sign expansion.
-- The accumulator is the number of pluses in the input so far.
veb1SE' :: Ordinal -> Ordinal -> SignExpansion -> (Ordinal, SignExpansion)

veb1SE 0 = mono1SE
veb1SE o = (veb1SELead o `consSE`) . snd . veb1SE' o 0

veb1SE' 0 = mono1SE'
veb1SE' o = transform f
  where
    v1 = veb1 o
    p = m1 o
    f a (True, n) = (a', plus $ v1 a') where a' = a `ordAdd` n
    f a (False, n) = (a, minus $ (v1 a `ordPow` p) `ordMult` n)

mono1SELead :: (Bool, Ordinal)
mono1SELead = (True, 1)

veb1SELead :: Ordinal -> (Bool, Ordinal)
veb1SELead 0 = (True, 1)
veb1SELead o = (True, veb1 o 0)
