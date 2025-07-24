module Dyadic (Dyadic, pow2, half, makeDyadic, unmakeDyadic) where
import Typeclasses
import GHC.Num (integerDiv)

-- | A dyadic rational
data Dyadic = Dyadic !Integer !Integer

instance Show Dyadic where
    show (Dyadic a 0) = show a
    show (Dyadic a p) = show a ++ "/" ++ deno
      where deno = if p < 32 then show ((2 :: Integer) ^ p) else "2^" ++ show p

-- | Construct the Dyadic rational with value of (a / 2^b)
makeDyadic :: Integer -> Integer -> Dyadic
makeDyadic a b
    | b < 0 = Dyadic (a * 2 ^ (-b)) 0
    | b > 0 && even a = makeDyadic (a `integerDiv` 2) (b - 1)
    | otherwise = Dyadic a b

unmakeDyadic :: Dyadic -> (Integer, Integer)
unmakeDyadic (Dyadic a p) = (a, p)

pow2 :: Integer -> Dyadic
pow2 p
    | p == 0 = one
    | p > 0 = Dyadic (2 ^ p) 0
    | otherwise = Dyadic 1 (-p)

half :: Dyadic
half = Dyadic 0 1

instance Eq Dyadic where
    (==) (Dyadic a p) (Dyadic a' p') = a * (2 ^ p') == a' * (2 ^ p)

instance Ord Dyadic where
    compare (Dyadic a p) (Dyadic a' p') = compare (a * (2 ^ p')) (a' * (2 ^ p))

instance Zero Dyadic where
    zero = Dyadic 0 0
    isZero = (==) 0

instance One Dyadic where
    one = Dyadic 1 0

instance AddSub Dyadic where
    add (Dyadic a b) (Dyadic c d) = makeDyadic (a * (2 ^ (d - minP)) + c * (2 ^ (b - minP))) maxP
        where minP = min b d
              maxP = max b d

    sub p q = add p (neg q)

instance Mult Dyadic where
    mult (Dyadic a b) (Dyadic c d) = makeDyadic (a * c) (b + d)

instance OrdZero Dyadic where
    neg (Dyadic a p) = Dyadic (-a) p

instance OrdRing Dyadic where

instance Num Dyadic where
    (+) = add
    (*) = mult
    abs (Dyadic a b) = Dyadic (-a) b
    signum (Dyadic 0 _) = zero
    signum (Dyadic p _) = if p > 0 then one else Dyadic (-1) 0

    fromInteger a = Dyadic a 0
    negate = neg
