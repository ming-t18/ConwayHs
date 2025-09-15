module Data.Conway.SignExpansion.Conway
  ( isAllPluses,
    isAllMinuses,
    birthday,
    conwaySE,

    -- * Helpers

    -- ** Term list and reduced sign expansions
    termsListSE,
    mergeReducedTermList,
    reduceTermsList,

    -- ** Helper
    monoSE,
    vebSE,
    toExponent,
  )
where

import Control.Arrow (second)
import Data.Conway.Conway
import Data.Conway.SignExpansion.Dyadic hiding (empty, toList)
import qualified Data.Conway.SignExpansion.Dyadic as SED
import Data.Conway.SignExpansion.Reduce
import Data.Conway.SignExpansion.Types as SE
import Data.Conway.SignExpansion.Veb
import Data.Conway.Typeclasses
import Data.Foldable (foldl')

-- * Is all pluses

isAllPluses :: (FiniteSignExpansion a) => Conway a -> Bool
isAllPlusesTerm :: (FiniteSignExpansion a) => (VebMono a, a) -> Bool
isAllPlusesVebMono :: (FiniteSignExpansion a) => VebMono a -> Bool
isAllPlusesFinite :: (FiniteSignExpansion a) => a -> Bool
isAllPluses = all isAllPlusesTerm . termsList

isAllMinuses :: (FiniteSignExpansion a, OrdZero a, One a) => Conway a -> Bool
isAllMinuses = isAllPluses . neg

isAllPlusesTerm (v, c) = isAllPlusesVebMono v && isAllPlusesFinite c

isAllPlusesVebMono (VebMono _ p) = isAllPluses p

isAllPlusesFinite = all fst . toList . fromFSE . finiteSE

-- * Conway

birthday :: (One a, FiniteSignExpansion a, OrdZero a) => Conway a -> Ordinal
birthday = SE.length . conwaySE

conwaySE :: (One a, FiniteSignExpansion a, OrdZero a) => Conway a -> SignExpansion
conwaySE = termsListSE . termsList

termsListSE :: (One a, FiniteSignExpansion a, OrdZero a) => [(VebMono a, a)] -> SignExpansion
termsListSE = mergeReducedTermList . reduceTermsList

mergeReducedTermList :: (OrdZero a, FiniteSignExpansion a, One a) => [(Reduced SignExpansion, a)] -> SignExpansion
mergeReducedTermList = foldl' (\s (Reduced po, c) -> s +++ monoSE po c) empty

reduceTermsList :: (One a, FiniteSignExpansion a, OrdZero a) => [(VebMono a, c)] -> [(Reduced SignExpansion, c)]
reduceTermsList xs = zip pos cs
  where
    (ps, cs) = unzip xs
    -- The reduced sign expansions of the exponents
    pos = reduce $ map toExponent ps

-- | Given a @VebMono@ @v@, returns the sign expansion of @p@ where @v = mono1 p@.
toExponent :: (One a, FiniteSignExpansion a, OrdZero a) => VebMono a -> SignExpansion
toExponent (VebMono 0 p) = conwaySE p
toExponent (VebMono o p) = veb1SE o (conwaySE p)

-- | Given the sign expansion of @p@ and the coefficient @c@,
-- return the sign expansion of @mono1 p * finite c@.
monoSE :: (One a, FiniteSignExpansion a, OrdZero a) => SignExpansion -> a -> SignExpansion
monoSE p c
  | isZero c = empty
  | c == one = mono1SE p
  | isNegative c = neg $ monoSE p $ neg c
  | otherwise = SE.plus 1 +++ mono1Part +++ coeffPart
  where
    -- @mono1Part@ is the sign expansion contribution of the mono1 part, excluding the first plus.
    -- @nPlus@ is the number of pluses in @p@
    (nPlus, mono1Part) = mono1SE' 0 p

    -- The sign expansion contribution of the coefficient.
    -- Based on [Gonshor] Theorem 5.12(a)
    coeffPart :: SignExpansion
    coeffPart = SE.fromList $ map (second multiply) $ SED.toList $ omitLead $ finiteSE c

    -- Converts an @FSE@ run length to number-of-pluses run length.
    multiply :: Natural -> Ordinal
    multiply n = mono1 nPlus `mult` finite n

vebSE :: (One a, FiniteSignExpansion a, OrdZero a) => Ordinal -> SignExpansion -> a -> SignExpansion
vebSE 0 p c = monoSE p c
vebSE o p c = monoSE (veb1SE o p) c
