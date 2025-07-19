{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
import Test.QuickCheck
import Lib
import qualified Data.Map.Strict as M
import Typeclasses
import Numeric.Natural (Natural)
import Dyadic
import Control.Monad
import FundamentalSeq

import qualified Data.List.NonEmpty as NE

maxDepth :: Int
maxDepth = 4

maxLengthByDepth :: Int -> Gen Int
maxLengthByDepth d
    = case d of
        0 -> chooseInt (0, 1)
        1 -> chooseInt (0, 2)
        2 -> chooseInt (0, 3)
        3 -> chooseInt (0, 4)
        _ -> chooseInt (0, 5)

arbConway :: (Arbitrary order, Arbitrary gen, OrdRing a) => (order -> Ordinal) -> (gen -> a) -> Int -> Gen (Conway a)
arbConway fromOrder fromCoeff = recurse where
    -- recurse :: (OrdRing a) => Int -> Gen (Conway a)
    recurse d | d <= 0 = return zero
    recurse d = do
        l <- listOf (genMono d)
        n <- maxLengthByDepth d
        return $ foldr add zero $ take n l
    -- genMono :: (OrdRing a) => Int -> Gen (Conway a)
    genMono d = do
        a <- fromOrder <$> arbitrary
        p <- recurse (d - 1)
        veb a p . fromCoeff <$> arbitrary

shrinkFinite :: OrdRing a => a -> [a]
shrinkFinite c
    | isZero c = []
    | zero < c && c <= one = [zero]
    | one < c = [zero, one]
    | neg one <= c && c < zero = [zero]
    | otherwise = [zero, neg one]

shrinkTriple :: OrdRing a => (Ordinal, Conway a, a) -> [(Ordinal, Conway a, a)]
shrinkTriple (a, p, c) =
    [(a', p, c) | a' <- shrinkConway a]
    ++ [(a, p', c) | p' <- shrinkConway p]
    ++ [(a, p, c') | c' <- shrinkFinite c]


monosList :: (OrdZero a, One a) => Conway a -> [(Ordinal, Conway a, a)]
monosList x = map (\(VebMono a p, c) -> (a, p, c)) $ termsList x

shrinkConway :: OrdRing a => Conway a -> [Conway a]
shrinkConway x =
    [
        foldl (\s (a, p, c) -> add s (veb a p c)) zero list'
        |  list' <- shrinkList shrinkTriple $ monosList x
    ]

newtype DyadicGen = DyadicGen { getDyadic :: Dyadic }
    deriving (Eq, Ord, Show)

newtype NaturalGen = NatGen { getNatural :: Natural }
    deriving (Eq, Ord, Show)

newtype FiniteOrdGen = FinOrd { getFiniteOrd :: Ordinal }
    deriving (Eq, Ord, Show)

newtype OrdV0Gen = OrdV0 { getOrdV0 :: Ordinal }
    deriving (Eq, Ord, Show)

newtype ConwayV0Gen a = ConwayV0 { getConwayV0 :: Conway a }
    deriving (Eq, Ord, Show)

newtype ConwayGen a = ConwayGen { getConway :: Conway a }
    deriving (Eq, Ord, Show)

instance Arbitrary DyadicGen where
    arbitrary = DyadicGen <$> (makeDyadic <$> arbitrary <*> arbitrary)
    shrink (DyadicGen d) =
        map DyadicGen (
            [ makeDyadic a' p | a' <- shrink a ] ++ [ makeDyadic a p' | p' <- shrink p ]
        ) where
            (a, p) = unmakeDyadic d

instance Arbitrary Dyadic where
    arbitrary = getDyadic <$> arbitrary
instance Arbitrary NaturalGen where
    arbitrary = (\(x :: Integer) -> NatGen $ fromIntegral $ abs x) <$> (arbitrary :: Gen Integer)
    -- shrink (NatGen 0) = []
    -- shrink (NatGen 1) = [NatGen 0]
    -- shrink (NatGen x) = map NatGen [0..x - 1]

instance Arbitrary FiniteOrdGen where
    arbitrary = FinOrd . finite . getNatural <$> arbitrary

instance Arbitrary OrdV0Gen where
    arbitrary = OrdV0 <$> arbConway (\() -> zero :: Ordinal) getNatural maxDepth
    shrink (OrdV0 x) = OrdV0 <$> shrinkConway x

instance (Arbitrary a, OrdRing a) => Arbitrary (ConwayV0Gen a) where
    arbitrary = ConwayV0 <$> arbConway (\() -> zero :: Ordinal) (id :: a -> a) maxDepth
    shrink (ConwayV0 x) = ConwayV0 <$> shrinkConway x

instance (Arbitrary a, OrdRing a) => Arbitrary (ConwayGen a) where
    arbitrary = ConwayGen <$> arbConway getOrdV0 (id :: a -> a) maxDepth
    shrink (ConwayGen x) = ConwayGen <$> shrinkConway x

test1, test2 :: Conway Integer
-- test1 = veb1 2 (veb1 3 0 + 1)
-- test2 = veb1 3 (veb1 2 0 + 1)
test1 = finite (-3)
test2 = finite (-2)

prop_makeDyadic :: Integer -> Integer -> Bool
prop_makeDyadic a b = makeDyadic a b == makeDyadic a b

prop_compareTransitive :: Ord a => a -> a -> a -> Property
prop_compareTransitive a b c
    | a <= b && a <= c = True ==> a <= c
    | a <= c && c <= b = True ==> a <= b
    | a >= b && b >= c = True ==> a >= c
    | a >= c && c >= b = True ==> a >= b
    | b <= a && a <= c = True ==> b <= c
    | b >= a && a >= c = True ==> b >= c
    | otherwise = False ==> False

prop_compareReverse :: Ord a => a -> a -> Bool
prop_compareReverse a b = compare a b == f (compare b a) where
    f EQ = EQ
    f LT = GT
    f GT = LT

prop_compareNegation :: OrdZero a => a -> a -> Bool
prop_compareNegation a b = compare a b == f (compare (neg a) (neg b)) where
    f EQ = EQ
    f LT = GT
    f GT = LT

prop_orderedAdd :: (AddSub a) => a -> a -> a -> Bool
prop_orderedAdd a b c
    | a <= b = add a c <= add b c
    | otherwise = add a c >= add b c

prop_addComm :: AddSub a => a -> a -> Bool
prop_addComm a b = add a b == add b a

prop_addAssoc :: AddSub a => a -> a -> a -> Bool
prop_addAssoc a b c = add a (add b c) == add (add a b) c

prop_multZero :: (Mult a) => a -> Bool
prop_multZero x = isZero (mult zero x) && isZero (mult x zero)

prop_multOne :: (Mult a) => a -> Bool
prop_multOne x = mult one x == x && mult x one == x

prop_multComm :: Mult a => a -> a -> Bool
prop_multComm a b = mult a b == mult b a

prop_multAssoc :: Mult a => a -> a -> a -> Bool
prop_multAssoc a b c = mult a (mult b c) == mult (mult a b) c

prop_multDistr :: (AddSub a, Mult a) => a -> a -> a -> Bool
prop_multDistr a b c = mult a (add b c) == add (mult a b) (mult a c)

propIncrMap, propDecrMap :: OrdV0Gen -> OrdV0Gen -> Property
-- | @a < b ==> V[a, V[b, 0] + 1] > V[b, 0]@
propIncrMap (OrdV0 a) (OrdV0 b)
    | a == b = False ==> True
    | a < b = True ==> veb1 a (veb1 b zero `add` one) > (veb1 b zero :: Conway Dyadic)
    | otherwise = True ==> veb1 b (veb1 a zero `add` one) > (veb1 a zero :: Conway Dyadic)

-- | @a < b ==> V[a, V[b, 0] - 1] < V[b, 0]@
propDecrMap (OrdV0 a) (OrdV0 b)
    | a == b = False ==> True
    | a < b = True ==> veb1 a (veb1 b zero `sub` one) < (veb1 b zero :: Conway Dyadic)
    | otherwise = True ==> veb1 b (veb1 a zero `sub` one) < (veb1 a zero :: Conway Dyadic)

-- | All elements of the fundamental sequence are smaller
-- @x[i] < x@
prop_fsOrd_smaller :: Int -> Ordinal -> Property
prop_fsOrd_smaller i 0 = False ==> True
prop_fsOrd_smaller i x =
    case fsOrd x of
        Left _ -> False ==> True
        Right f -> True ==> (f NE.!! i < x)

-- | Fundamental sequence is increasing:
-- @i < j ==> x[i] < x[j]@
prop_fsOrd_increasing :: Int -> Int -> Ordinal -> Property
prop_fsOrd_increasing i j x =
    case fsOrd x of
        Left _ -> False ==> True
        Right f -> True ==> (f NE.!! i < f NE.!! j)

type G = ConwayGen Dyadic
type GO = OrdV0Gen
type C = Conway Dyadic
type O = Ordinal
conway1 :: (C -> t) -> G -> t
conway2 :: (C -> C -> t) -> G -> G -> t
conway3 :: (C -> C -> C -> t) -> G -> G -> G -> t
conway1 p (ConwayGen x) = p (x :: C)
conway2 p (ConwayGen x) (ConwayGen y) = p (x :: C) y
conway3 p (ConwayGen x) (ConwayGen y) (ConwayGen z) = p (x :: C) y z

ord1 :: (O -> t) -> GO -> t
--ord2 :: (O -> O -> t) -> GO -> GO -> t
--ord3 :: (O -> O -> O -> t) -> GO -> GO -> GO -> t
ord1 p (OrdV0 x) = p (x :: O)
--ord2 p (OrdV0Gen x) (OrdV0Gen y) = p (x :: O) y
--ord3 p (OrdV0Gen x) (OrdV0Gen y) (OrdV0Gen z) = p (x :: O) y z

qc :: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs { maxSuccess = 1000, maxShrinks = 1000 }

type T = Dyadic
main :: IO ()
main = do
    when True $ do
        putStrLn "Dyadic"
        qc prop_makeDyadic
        qc (prop_compareTransitive :: T -> T -> T -> Property)
        qc (prop_compareReverse :: T -> T -> Bool)
        qc (prop_compareNegation :: T -> T -> Bool)
        qc (prop_addComm :: T -> T -> Bool)
        qc (prop_multComm :: T -> T -> Bool)
        qc (prop_addAssoc :: T -> T -> T -> Bool)
        qc (prop_multAssoc :: T -> T -> T -> Bool)
        qc (prop_multDistr :: T -> T -> T -> Bool)
        qc (prop_orderedAdd :: T -> T -> T -> Bool)
        putStrLn "---"

    when True $ do
        putStrLn "Conway Dyadic"
        qc (conway3 prop_compareTransitive)
        qc (conway2 prop_compareReverse)
        qc (conway2 prop_compareNegation)
        putStrLn "addComm"
        qc (conway2 prop_addComm)
        putStrLn "multComm"
        qc (conway2 prop_multComm)
        putStrLn "multZero"
        qc (conway1 prop_multZero)
        putStrLn "multOne"
        qc (conway1 prop_multOne)
        putStrLn "addAssoc"
        qc (conway3 prop_addAssoc)
        putStrLn "multAssoc"
        qc (conway3 prop_multAssoc)
        putStrLn "orderedAdd"
        qc (conway3 prop_orderedAdd)
        putStrLn "multDistr"
        qc (conway3 prop_multDistr)
        putStrLn "---"

    when True $ do
        putStrLn "veb increasing map"
        qc propIncrMap
        qc propDecrMap
        putStrLn "---"

    when True $ do
        putStrLn "Fundamental Sequences of Ordinals"
        qc (\(OrdV0 o) (NatGen i) ->
            prop_fsOrd_smaller (fromIntegral i) o)
        qc (\(OrdV0 o) (NatGen i) (NatGen j) ->
            j > i ==> prop_fsOrd_increasing (fromIntegral i) (fromIntegral j) o)
        putStrLn "---"

    -- quickCheck (\(ConwayGen x) (ConwayGen y) (ConwayGen z) -> prop_leTransitive (x :: Conway Dyadic) y z)
    -- quickCheck (\(ConwayGen x) (ConwayGen y) -> prop_compareReverse (x :: Conway Dyadic) y)
    -- quickCheck (\(ConwayGen x) (ConwayGen y) -> x == (y + (omega :: Conway Dyadic)))
    -- quickCheck (\(ConwayGen x) (ConwayGen y) -> prop_orderedAdd (x :: Conway Dyadic) y)
    -- print test1
    -- print test2
    -- print (test1 < test2)
    -- quickCheck (\(ConwayMono x) (ConwayMono y) (ConwayMono z) -> (x :: Conway Integer) < y && y < z ==> x < z)
    -- quickCheck (\(x :: Integer) (y :: Integer) -> compare x y == compare (finite x) (finite y))
    -- quickCheck (\(x :: Integer) (y :: Integer) -> finite (x + y) == finite x + finite y)
    -- quickCheck (\(ConwayMono x) -> (x :: Conway Integer) + 1 > x)
