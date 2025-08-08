module SignExpansion.Veb (mono1SE, mono1SE', veb1SE, veb1SE') where

import Conway
import OrdinalArith
import SignExpansion.Types

m1 :: Ordinal -> Ordinal
m1 = Conway.mono1

-- | Given the sign expansion of @x@,
-- return the sign expansion of @mono1 x@.
mono1SE :: SignExpansion -> SignExpansion
mono1SE' :: Ordinal -> SignExpansion -> SignExpansion
mono1SE = ((True, 1) `consSE`) . mono1SE' 0

mono1SE' a xs = case toConsSE xs of
  Nothing -> empty
  Just ((True, n), xs') ->
    let a' = (a `ordAdd` n)
     in (True, m1 a') `consSE` mono1SE' a' xs'
  Just ((False, n), xs') ->
    (False, m1 (a `ordAdd` 1) `ordMult` n) `consSE` mono1SE' a xs'

-- | Given Veblen order @o@ and the sign expansion of @x@,
-- return the sign expansion of @veb1 o x@.
veb1SE :: Ordinal -> SignExpansion -> SignExpansion
veb1SE' :: Ordinal -> Ordinal -> SignExpansion -> SignExpansion
veb1SE o = ((True, veb1 o 0) `consSE`) . veb1SE' o 0

veb1SE' o = recurse
  where
    v1 :: Ordinal -> Ordinal
    v1 = veb1 o
    recurse :: Ordinal -> SignExpansion -> SignExpansion
    recurse a xs = case toConsSE xs of
      Nothing -> empty
      Just ((True, n), xs') ->
        let a' = (a `ordAdd` n)
         in (True, v1 a') `consSE` recurse a' xs'
      Just ((False, n), xs') ->
        (False, (v1 a `ordPow` m1 o) `ordMult` n) `consSE` recurse a xs'
