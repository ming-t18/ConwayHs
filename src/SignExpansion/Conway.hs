module SignExpansion.Conway
  ( isAllPluses,
    conwaySE,
  )
where

import Control.Arrow (second)
import Conway
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
termsListSE xs = foldl (\s (VebMono o _, po, c) -> s +++ multMonoSE o po c) empty xs'
  where
    (ps, cs) = unzip xs
    toExponent (VebMono 0 p) = conwaySE p
    toExponent (VebMono o p) = veb1SE o (conwaySE p)
    pos = reduce $ map toExponent ps
    xs' = zip3 ps pos cs

multMonoSE :: (One a, FiniteSignExpansion a, OrdZero a) => Ordinal -> SignExpansion -> a -> SignExpansion
multMonoSE o p c
  | c == one = fromMono1SE p
  | isNegative c = neg $ multMonoSE o p $ neg c
  | otherwise = fromMono1SE p +++ suffix
  where
    suffix :: SignExpansion
    suffix = fromList $ map (second multiply) $ omitLead $ finiteSE c

    fromMono1SE :: SignExpansion -> SignExpansion
    fromMono1SE = if o == 0 then mono1SE else id

    multiply :: Natural -> Ordinal
    multiply n = v1 `mult` finite n

    v1 = if o == 0 then mono1 nPlus else nPlus
    nPlus = countSigns True p
