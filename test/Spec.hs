{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
import Gen
import Test.QuickCheck
import Lib
import Typeclasses
    ( OrdRing,
      OrdZero(neg, isPositive),
      Zero(zero, isZero),
      AddSub(..),
      Mult(..),
      One(one) )
import Dyadic
import Control.Monad
import FundamentalSeq

import qualified Data.List.NonEmpty as NE
import Numeric.Natural (Natural)

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

prop_addComm :: (AddSub a, Show a) => a -> a -> Property
prop_addComm a b = add a b === add b a

prop_addAssoc :: (AddSub a, Show a) => a -> a -> a -> Property
prop_addAssoc a b c = add a (add b c) === add (add a b) c

prop_dneg :: (OrdZero a, Show a) => a -> Property
prop_dneg a = a === neg (neg a)

prop_addNegIsSub :: (Show a, AddSub a) => a -> a -> Property
prop_addNegIsSub a b = a `add` neg b === a `sub` b

prop_multZero :: Mult a => a -> Bool
prop_multZero x = isZero (mult zero x) && isZero (mult x zero)

prop_multOne :: Mult a => a -> Bool
prop_multOne x = mult one x == x && mult x one == x

prop_multComm :: (Mult a, Show a) => a -> a -> Property
prop_multComm a b = mult a b === mult b a

prop_multAssoc :: (Mult a, Show a) => a -> a -> a -> Property
prop_multAssoc a b c = mult a (mult b c) === mult (mult a b) c

prop_multDistr :: (AddSub a, Mult a, Show a) => a -> a -> a -> Property
prop_multDistr a b c = mult a (add b c) === add (mult a b) (mult a c)

prop_multNeg :: (AddSub a, Mult a, Show a) => a -> a -> Property
prop_multNeg a b = neg (mult a b) === mult (neg a) b

prop_sqPos :: Mult a => a -> Bool
prop_sqPos a = if a == zero then mult a a == zero else mult a a > zero

prop_multPreserveOrder :: Mult a => a -> a -> a -> Property
prop_multPreserveOrder m a b
    | isZero m = False ==> True === True
    | isPositive m = True ==> (a <= b) === (mult m a <= mult m b)
    | otherwise = True ==> (b <= a) === (mult m a <= mult m b)

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
prop_fsOrd_smaller _ 0 = False ==> True
prop_fsOrd_smaller i x =
    case fsOrd x of
        Left _ -> False ==> True
        Right f -> True ==> f NE.!! i < x

-- | Fundamental sequence is increasing:
-- @i < j ==> x[i] < x[j]@
prop_fsOrd_increasing :: Int -> Int -> Ordinal -> Property
prop_fsOrd_increasing i j x =
    case fsOrd x of
        Left _ -> False ==> True
        Right f -> True ==> f NE.!! i < f NE.!! j

qc :: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs { maxSuccess = 20000, maxShrinks = 1000 }

testPropsOrdRing :: (Show a, Show t, Arbitrary a, OrdRing t) => (a -> t) -> IO ()
testPropsOrdRing i = do
    let i1 f a = f (i a)
    let i2 f a b = f (i a) (i b)
    let i3 f a b c = f (i a) (i b) (i c)
    putStrLn "[ordering]"
    qc (i3 prop_compareTransitive)
    qc (i2 prop_compareReverse)
    putStrLn "[negation]"
    qc (i2 prop_compareNegation)
    qc (i1 prop_dneg)
    putStrLn "[add]"
    qc (i2 prop_addComm)
    qc (i3 prop_addAssoc)
    qc (i2 prop_addNegIsSub)
    qc (i3 prop_orderedAdd)
    putStrLn "[mult]"
    qc (i1 prop_multZero)
    qc (i1 prop_multOne)
    qc (i2 prop_multNeg)
    qc (i2 prop_multComm)
    putStrLn "  sqPos"
    qc (i1 prop_sqPos)
    putStrLn "  multPreserveOrder"
    qc (i3 prop_multPreserveOrder)
    putStrLn "  multAssoc"
    qc (i3 prop_multAssoc)
    putStrLn "  multDistr"
    qc (i3 prop_multDistr)

main :: IO ()
main = do
    when True $ do
        putStrLn "Dyadic"
        testPropsOrdRing (id :: Dyadic -> Dyadic)
        putStrLn "---"

    when True $ do
        putStrLn "Conway Integer"
        testPropsOrdRing ((\(ConwayGen x) -> x) :: ConwayGen Integer -> Conway Integer)
        putStrLn "---"

    when True $ do
        putStrLn "Conway Dyadic"
        testPropsOrdRing ((\(ConwayGen x) -> x) :: ConwayGen Dyadic -> Conway Dyadic)
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

--
--  TODO multiAssoc failed for Conway Dyadic and Conway Integer
--  *** Failed! Falsified (after 3604 tests and 7 shrinks):
--  ConwayGen {getConway = w^{-1}}
--  ConwayGen {getConway = φ[3, 0].-1}
--  ConwayGen {getConway = φ[3, 0]}
--  ConwayGen {getConway = w^{-1}}
--  ConwayGen {getConway = ε_0}
--  ConwayGen {getConway = w^{-1}.-1}
--
