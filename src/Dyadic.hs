module Dyadic (Dyadic, pow2, half, shl, shr, makeDyadic, unmakeDyadic, parts) where

import GHC.Num (integerDiv)
import Typeclasses
import Control.Arrow ((***))

-- | A dyadic rational
data Dyadic = Dyadic !Integer !Integer

instance Show Dyadic where
  show (Dyadic a 0) = show a
  show (Dyadic a p) = show a ++ "/" ++ deno
    where
      deno = if p < 32 then show ((2 :: Integer) ^ p) else "2^" ++ show p

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

-- | @1/2@
half :: Dyadic
half = makeDyadic 1 1

-- | "Shift left": Multiply by @2^p@ where @p@ is the second argument
shl :: Dyadic -> Integer -> Dyadic
shl (Dyadic x p) d = makeDyadic x (p - d)

-- | "Shift right": Multiply by @2^-p@ where @p@ is the second argument
shr :: Dyadic -> Integer -> Dyadic
shr (Dyadic x p) d = makeDyadic x (p + d)

-- | Decomposes a @Dyadic@ into the integer and fractional part.
-- The fractional parts is in @[0, 1)@ for positive value
-- and @(-1, 0]@ for negative.
parts :: Dyadic -> (Integer, Dyadic)
parts 0 = (0, 0)
parts x@(Dyadic n q)
  | x < 0 = (negate *** negate) $ parts $ -x
  | otherwise = (n `div` d, makeDyadic p' q) where
    d = 2 ^ q
    p' = n - (n `div` d) * d

instance Eq Dyadic where
  (==) (Dyadic a p) (Dyadic a' p') = a * (2 ^ p') == a' * (2 ^ p)

instance Ord Dyadic where
  compare (Dyadic a p) (Dyadic a' p') = compare (a * (2 ^ p')) (a' * (2 ^ p))

instance Zero Dyadic where
  zero = Dyadic 0 0
  isZero = (==) 0

instance One Dyadic where
  one = Dyadic 1 0
  isOne = (==) one

instance AddSub Dyadic where
  add (Dyadic a b) (Dyadic c d) = makeDyadic (a * (2 ^ (d - minP)) + c * (2 ^ (b - minP))) maxP
    where
      minP = min b d
      maxP = max b d

  sub p q = add p (neg q)

instance Mult Dyadic where
  mult (Dyadic a b) (Dyadic c d) = makeDyadic (a * c) (b + d)

instance OrdZero Dyadic where
  neg (Dyadic a p) = Dyadic (-a) p

instance OrdRing Dyadic

instance Num Dyadic where
  (+) = add
  (*) = mult
  abs (Dyadic a b) = Dyadic (-a) b
  signum (Dyadic 0 _) = zero
  signum (Dyadic p _) = if p > 0 then one else Dyadic (-1) 0

  fromInteger a = Dyadic a 0
  negate = neg
