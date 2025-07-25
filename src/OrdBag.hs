
module OrdBag (
    OrdBag,
    fromMap,
    fromList,
    toMap,
    toDescList,
    sumWith,
    negate,
) where
import qualified Data.Map.Strict as M
import Data.Map.Strict(Map)
import Typeclasses (Zero(..), Zero, OrdZero (..))
import Prelude hiding (negate)

-- | Represents a multiset of elements of type @k@ and
-- multiplicity of each element of type @v@.
--
-- Represented as a @Data.Map.Strict.Map@ with keys having
-- zero values eliminated.
newtype OrdBag k v = OrdBag (Map k v)
    deriving (Eq)

zeroNormalize :: (Zero v) => Map k v -> Map k v
zeroNormalize = M.filter (not . isZero)

fromMap :: (Zero v) => Map k v -> OrdBag k v
fromMap = OrdBag . zeroNormalize

fromList :: (Ord k, Zero v) => [(k, v)] -> OrdBag k v
fromList = OrdBag . zeroNormalize . M.fromList

toMap :: OrdBag k v -> Map k v
toMap (OrdBag m) = m

toDescList :: OrdBag k v -> [(k, v)]
toDescList (OrdBag m) = M.toDescList m

sumWith :: (Ord k, Zero v) => (k -> v -> v -> v) -> OrdBag k v -> OrdBag k v -> OrdBag k v
sumWith f (OrdBag m1) (OrdBag m2) = fromMap $ M.unionWithKey f m1 m2

negate :: (OrdZero v) => OrdBag k v -> OrdBag k v
negate (OrdBag m) = OrdBag $ M.map neg m

-- | Ordered lexicographically from the largest key to the smallest.
-- If either side has no matching key, its value is considered as zero.
-- Negative values are considered to be below zero.
instance (OrdZero k, OrdZero v) => Ord (OrdBag k v) where
    compare a b = comp ta tb where
        ta = toDescList a
        tb = toDescList b
        compPair :: (Ord k, OrdZero v) => (k, v) -> (k, v) -> Ordering
        compPair (p, c) (q, d)
            | s1 /= s2 = compare s1 s2
            | s1 == LT = compare q p <> compare c d
            | otherwise = compare p q <> compare c d
            where s1 = compareZero c
                  s2 = compareZero d

        z :: (Zero k, Zero v) => (k, v)
        z = (zero, zero)
        comp :: (OrdZero k, OrdZero v) => [(k, v)] -> [(k, v)] -> Ordering
        comp [] [] = EQ
        comp (x:_) [] = compPair x z
        comp [] (y:_) = compPair z y
        comp (x:xs) (y:ys) =
            case compPair x y of
                EQ -> comp xs ys
                other -> other
