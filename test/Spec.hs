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
import OrdinalArith
import Numeric.Natural

-- * Ordering

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

-- * Natural sum and product

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

-- * Ordinal Arithmetic

prop_ordAddZero :: Ordinal -> Property
prop_ordAddZero x = x `ordAdd` 0 === x

prop_ordAddFinite :: Natural -> Natural -> Property
prop_ordAddFinite x y = finite x `ordAdd` finite y === finite (x + y)

prop_ordAddSucc :: Ordinal -> Ordinal -> Property
prop_ordAddSucc x y = x `ordAdd` (y + 1) === (x `ordAdd` y) + 1

prop_ordAddOrderPreservingLeft :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordAddOrderPreservingLeft x y z = x `compare` y === (z `ordAdd` x) `compare` (z `ordAdd` y)

prop_ordAddAssoc :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordAddAssoc x y z = (x `ordAdd` y) `ordAdd` z === x `ordAdd` (y `ordAdd` z)

prop_ordAddAssocSelf :: Ordinal -> Property
prop_ordAddAssocSelf x = (x `ordAdd` x) `ordAdd` x === x `ordAdd` (x `ordAdd` x)

prop_ordMultZero :: Ordinal -> Property
prop_ordMultZero x = x `ordMult` 0 === 0

prop_ordMultOne :: Ordinal -> Property
prop_ordMultOne x = x `ordMult` 1 === x

prop_ordMultFinite :: Natural -> Natural -> Property
prop_ordMultFinite x y = finite x `ordMult` finite y === finite (x * y)

prop_ordMultSucc :: Ordinal -> Ordinal -> Property
prop_ordMultSucc x y = x `ordMult` (y + 1) === (x `ordMult` y) `ordAdd` x

prop_ordMultAssoc :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordMultAssoc x y z = (x `ordMult` y) `ordMult` z === x `ordMult` (y `ordMult` z)

prop_ordMultAssocSelf :: Ordinal -> Property
prop_ordMultAssocSelf x = (x `ordMult` x) `ordMult` x === x `ordMult` (x `ordMult` x)

prop_ordMultLeftDistr :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordMultLeftDistr x y z = x `ordMult` (y `ordAdd` z) === (x `ordMult` y) `ordAdd` (x `ordMult` z)

prop_ordMultMono1 :: Ordinal -> Ordinal -> Property
prop_ordMultMono1 x y = mono1 x `ordMult` mono1 y === mono1 (x `ordAdd` y)

-- * Power

prop_ordZeroPow :: Ordinal -> Property
prop_ordZeroPow x = not (isZero x) ==> 0 `ordPow` x === 0

prop_ordPowZero :: Ordinal -> Property
prop_ordPowZero x = x `ordPow` 0 === 1

prop_ordPowOne :: Ordinal -> Property
prop_ordPowOne x = x `ordPow` 1 === x

-- | For finite @b, c@, @b^(w.c) = (b^w)^c = w^c@
prop_ordPowFiniteMultW :: Natural -> Natural -> Property
prop_ordPowFiniteMultW b c = b > 1 && c > 1 ==> finite b `ordPow` mono 1 c === mono1 (finite c)

-- | For finite @b, c@, @b^(w^c) = b^(w.w^(c-1)) = (b^w)^(w^(c-1)) = w^(w^(c-1))@
prop_ordPowFiniteWPFinite :: Natural -> Natural -> Property
prop_ordPowFiniteWPFinite b c = b > 1 && c > 1 ==> finite b `ordPow` mono1 (finite c) === mono1 (mono1 $ finite (c - 1))

prop_ordPowSucc :: Ordinal -> Ordinal -> Property
prop_ordPowSucc x y = x `ordPow` (y + 1) === (x `ordPow` y) `ordMult` x

prop_ordPowFinite :: Natural -> Natural -> Property
prop_ordPowFinite x y = finite x `ordPow` finite y === finite (x ^ y)

prop_ordPowExponentSum :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordPowExponentSum x y z = (x `ordPow` (y `ordAdd` z)) === (x `ordPow` y) `ordMult` (x `ordPow` z)

-- TODO large exponents can cause hangs
prop_ordPowExponentProduct :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordPowExponentProduct x y z =
    isPositive y && isPositive z ==> (x `ordPow` (y `ordMult` z)) === (x `ordPow` y) `ordPow` z

prop_ordPowOrderPreserving :: Ordinal -> Ordinal -> Ordinal -> Property
prop_ordPowOrderPreserving x y z
    | x == y = False ==> True
    | x < y = True ==> (x `ordPow` z) <= (y `ordPow` z)
    | otherwise = True ==> (x `ordPow` z) >= (y `ordPow` z)

-- | @x^(w^y) = x^(p0 . w^y)@ where @x = w^p0 . c0 + ...@
-- ProofWiki: https://proofwiki.org/wiki/Ordinal_Exponentiation_via_Cantor_Normal_Form/Corollary
-- with @w@ being the base.
prop_ordPowLeadingTerm :: Ordinal -> Ordinal -> Property
prop_ordPowLeadingTerm x y = not (isFinite x) && isPositive y ==> x `ordPow` mono1 y === mono1 (p0 `ordMult` mono1 y) where
    (v, _) = leadingTerm x
    p0 = unMono1 v

prop_ordPowMono1 :: Ordinal -> Property
prop_ordPowMono1 x = mono1 x === omega `ordPow` x

-- * Veblen Function

prop_vebIncrMap, prop_vebDecrMap :: OrdV0Gen -> OrdV0Gen -> Property
-- | @a < b ==> V[a, V[b, 0] + 1] > V[b, 0]@
prop_vebIncrMap (OrdV0 a) (OrdV0 b)
    | a == b = False ==> True
    | a < b = True ==> veb1 a (veb1 b zero `add` one) > (veb1 b zero :: Conway Dyadic)
    | otherwise = True ==> veb1 b (veb1 a zero `add` one) > (veb1 a zero :: Conway Dyadic)

-- | @a < b ==> V[a, V[b, 0] - 1] < V[b, 0]@
prop_vebDecrMap (OrdV0 a) (OrdV0 b)
    | a == b = False ==> True
    | a < b = True ==> veb1 a (veb1 b zero `sub` one) < (veb1 b zero :: Conway Dyadic)
    | otherwise = True ==> veb1 b (veb1 a zero `sub` one) < (veb1 a zero :: Conway Dyadic)

-- * Fundamental Sequences

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

-- * Testing

qc :: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs { maxSuccess = 1000, maxShrinks = 1000 }

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

testPropsOrdArith :: IO ()
testPropsOrdArith = do
    putStrLn "[ordinal addition]"
    qc prop_ordAddZero
    qc prop_ordAddFinite
    qc prop_ordAddSucc
    qc prop_ordAddOrderPreservingLeft
    qc prop_ordAddAssoc
    qc prop_ordAddAssocSelf

    putStrLn "[ordinal multiplication]"
    qc prop_ordMultZero
    qc prop_ordMultOne
    qc prop_ordMultFinite
    putStrLn "  multSucc"
    qc prop_ordMultSucc
    putStrLn "  multAssoc"
    qc prop_ordMultAssoc
    putStrLn "  multAssocSelf"
    qc prop_ordMultAssocSelf
    putStrLn "  multLeftDistr"
    qc prop_ordMultLeftDistr
    putStrLn "  multMono1"
    qc prop_ordMultMono1

    putStrLn "[ordinal power]"
    putStrLn "  zeroPow"
    qc prop_ordZeroPow
    putStrLn "  powZero"
    qc prop_ordPowZero
    putStrLn "  powOne"
    qc prop_ordPowOne
    putStrLn "  pow finite^(w.finite)"
    qc prop_ordPowFiniteMultW
    putStrLn "  pow finite^(w^finite)"
    qc prop_ordPowFiniteWPFinite
    putStrLn "  powSucc"
    qc prop_ordPowSucc
    putStrLn "  powFinite"
    qc prop_ordPowFinite
    putStrLn "  powExponentSum"
    qc prop_ordPowExponentSum
    putStrLn "  powExponentProduct"
    qc prop_ordPowExponentProduct
    putStrLn "  powOrderPresering"
    qc prop_ordPowOrderPreserving
    putStrLn "  powLeadingTerm"
    qc prop_ordPowLeadingTerm
    putStrLn "  powMono1"
    qc prop_ordPowMono1


main :: IO ()
main = do
    when True $ do
        putStrLn "Dyadic"
        testPropsOrdRing (id :: Dyadic -> Dyadic)
        putStrLn "---"

    when True $ do
        putStrLn "ConwayV0 Integer"
        testPropsOrdRing ((\(ConwayV0 x) -> x) :: ConwayV0Gen Integer -> Conway Integer)
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
        putStrLn "Ordinal arithmetic"
        testPropsOrdArith
        putStrLn "---"

    when True $ do
        putStrLn "Veb increasing map"
        qc prop_vebIncrMap
        putStrLn "Veb decreasing map"
        qc prop_vebDecrMap
        putStrLn "---"

    when True $ do
        putStrLn "Ordinal fundamental sequences"
        qc (\(OrdV0 o) (NatGen i) ->
            prop_fsOrd_smaller (fromIntegral i) o)
        qc (\(OrdV0 o) (NatGen i) (NatGen j) ->
            j > i ==> prop_fsOrd_increasing (fromIntegral i) (fromIntegral j) o)
        putStrLn "---"
