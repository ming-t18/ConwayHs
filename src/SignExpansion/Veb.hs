module SignExpansion.Veb (mono1SE, mono1SE', veb1SE, veb1SE') where

import Conway
import Data.Foldable (foldl')
import OrdinalArith
import SignExpansion.Types

m1 :: Ordinal -> Ordinal
m1 = mono1

-- | Given a sign expansion, generate an output sign expansion while keeping track of a state.
transform :: (a -> (Bool, Ordinal) -> (a, SignExpansion)) -> a -> SignExpansion -> (a, SignExpansion)
transform f a0 = foldl' (\(a, s) e -> let (a', ds) = f a e in (a', s +++ ds)) (a0, empty) . toList

-- | Given the sign expansion of @x@, return the sign expansion of @mono1 x@.
mono1SE :: SignExpansion -> SignExpansion

-- | Like @mono1SE@, except takes the accumulator as the first argument
-- and returns the accumulator after generating the sign expansion.
-- The accumulator is the number of pluses in the input so far.
mono1SE' :: Ordinal -> SignExpansion -> (Ordinal, SignExpansion)

mono1SE = ((True, 1) `consSE`) . snd . mono1SE' 0
mono1SE' = transform f
  where
    f a (True, n) = (a', single (True, m1 a')) where a' = a `ordAdd` n
    f a (False, n) = (a, single (False, m1 (a `ordAdd` 1) `ordMult` n))

-- | Given Veblen order @o@ and the sign expansion of @x@, return the sign expansion of @veb1 o x@.
veb1SE :: Ordinal -> SignExpansion -> SignExpansion

-- | Like @veb1SE@, except takes the accumulator as the second argument
-- and returns the accumulator after generating the sign expansion.
-- The accumulator is the number of pluses in the input so far.
veb1SE' :: Ordinal -> Ordinal -> SignExpansion -> (Ordinal, SignExpansion)

veb1SE 0 = mono1SE
veb1SE o = ((True, veb1 o 0) `consSE`) . snd . veb1SE' o 0

veb1SE' 0 = mono1SE'
veb1SE' o = transform f
  where
    v1 = veb1 o
    f a (True, n) = (a', single (True, v1 a')) where a' = a `ordAdd` n
    f a (False, n) = (a, single (False, (v1 a `ordPow` m1 o) `ordMult` n))
