module SignExpansion.Conway where

import Control.Arrow (second)
import Conway
import SignExpansion
import SignExpansion.Dyadic
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
termsListSE [(v, c)] = vebMonoSE v c
termsListSE _ = error "TODO implement this"

realSuffixSE :: (FiniteSignExpansion a) => Ordinal -> Ordinal -> a -> SignExpansion
realSuffixSE o a c = fromList $ map (second f) $ omitLead $ finiteSE c
  where
    f n = v1 `mult` finite n
    v1 = veb1 o a

-- * Monomial

vebMonoSE :: (FiniteSignExpansion a, One a, OrdZero a) => VebMono a -> a -> SignExpansion
vebMonoSE v@(VebMono o p) c
  | c == one = veb1SE o (conwaySE p)
  | isNegative c = neg $ vebMonoSE v $ neg c
  | otherwise =
      mono1Part +++ realSuffixSE o np c
  where
    (np, p') = veb1SE' o 0 (conwaySE p)
    p0 = single $ veb1SELead o
    mono1Part = p0 +++ p'
