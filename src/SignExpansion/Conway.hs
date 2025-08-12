module SignExpansion.Conway
  ( isAllPluses,
    conwaySE,
  )
where

import Control.Arrow (second)
import Conway
import Data.Foldable (foldl')
import SignExpansion.Dyadic
import SignExpansion.Reduce
import SignExpansion.Types
import SignExpansion.Veb
import Typeclasses

-- * Is all pluses

isAllPluses :: (FiniteSignExpansion a) => Conway a -> Bool
isAllPlusesTerm :: (FiniteSignExpansion a) => (VebMono a, a) -> Bool
isAllPlusesVebMono :: (FiniteSignExpansion a) => VebMono a -> Bool
isAllPlusesFinite :: (FiniteSignExpansion a) => a -> Bool
isAllPluses = all isAllPlusesTerm . termsList

isAllPlusesTerm (v, c) = isAllPlusesVebMono v && isAllPlusesFinite c

isAllPlusesVebMono (VebMono _ p) = isAllPluses p

isAllPlusesFinite = all fst . toList . fromFSE . finiteSE

-- * Conway

conwaySE :: (One a, FiniteSignExpansion a, OrdZero a) => Conway a -> SignExpansion
conwaySE = termsListSE . termsList

termsListSE :: (One a, FiniteSignExpansion a, OrdZero a) => [(VebMono a, a)] -> SignExpansion
termsListSE [] = empty
termsListSE xs = foldl' (\s (VebMono o _, po, c) -> s +++ monoSE o po c) empty xs'
  where
    (ps, cs) = unzip xs
    -- \| The reduced sign expansions of the exponents
    pos = reduce $ map toExponent ps
    -- TODO count nPlus in ps
    xs' = zip3 ps pos cs

-- | Given a @VebMono@ @v@, returns the sign expansion of @p@ where @v = mono1 p@.
toExponent :: (One a, FiniteSignExpansion a, OrdZero a) => VebMono a -> SignExpansion
toExponent (VebMono 0 p) = conwaySE p
toExponent (VebMono o p) = veb1SE o (conwaySE p)

-- | Given the Veblen order @o@, the sign expansion of @p@ (where @p = veb1 o p'@ for some @p'@)
-- and the coefficient @c@, returns the sign expansion of @p * finite c@.
monoSE :: (One a, FiniteSignExpansion a, OrdZero a) => Ordinal -> SignExpansion -> a -> SignExpansion
monoSE o p c
  | c == one = mono1SE'' p
  | isNegative c = neg $ monoSE o p $ neg c
  | otherwise = mono1SE'' p +++ realPart
  where
    -- \| The sign expansion contribution of the coefficient.
    -- Based on [Gonshor] Theorem 5.12(a)
    realPart :: SignExpansion
    realPart = fromList $ map (second multiply) $ omitLead $ finiteSE c

    -- \| Converts a FSE run length to number-of-pluses run length.
    multiply :: Natural -> Ordinal
    multiply n = v1 `mult` finite n

    -- \| Given the sign expansion of @p@, returns the sign expansion of @mono1 p@,
    -- taking into account the value of @o@ where @p = veb1 o ...@.
    mono1SE'' :: SignExpansion -> SignExpansion
    mono1SE'' = if o == 0 then mono1SE else id

    v1 = if o == 0 then mono1 nPlus else nPlus
    nPlus = countSigns True p
