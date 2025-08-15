module Dyadic
  ( Dyadic,

    -- * Creation and decomposition
    (%/),
    makeDyadic,
    unmakeDyadic,
    fromFloat,

    -- * Conversion to @Ratio@
    numerator,
    denominator,

    -- * Operations
    pow2,
    half,
    shl,
    shr,
    parts,
  )
where

import Control.Arrow ((***))
import Data.Bits
import Data.Ratio ((%))
import qualified Data.Ratio as R
import GHC.Num (integerDiv)
import Typeclasses

-- | Arbitrary-precision dyadic rational number.
--
-- A dyadic rational is a rational number with the denominator
-- constrainted to be a power of 2, @2^-p@.
--
-- It is represented as a pair @(n, p)@ where
-- @n@ is an @Integer@ and @p@ is non-negative integer.
-- @(n, p)@ are automatically simplified to minimize the @p@
-- required to represent the value.
--
-- Strictness: Strict over @n@ and @p@.
data Dyadic = Dyadic !Integer !Integer

instance Show Dyadic where
  show (Dyadic a 0) = show a
  show (Dyadic a p) = show a ++ "/" ++ deno
    where
      deno = if p < 32 then show ((2 :: Integer) ^ p) else "2^" ++ show p

-- | WARNING: Partial function since dyadic denominators must be powers of 2.
instance Fractional Dyadic where
  fromRational r = p %/ l2 q
    where
      (p, q) = (R.numerator r, R.denominator r)
      l2 :: Integer -> Integer
      l2 n
        | n .&. (n - 1) == 0 = floor $ logBase (2 :: Double) $ fromIntegral n
        | otherwise = error $ "Dyadic.fromRational: denominator is not a power of 2: " ++ show r
  recip (Dyadic p d) = fromRational $ (2 ^ d) % p

instance Real Dyadic where
  toRational (Dyadic n p) = n % (2 ^ p)


infixl 7 %/

-- | Constructs the Dyadic rational with the value of @(n / 2^p)@
makeDyadic :: Integer -> Integer -> Dyadic
makeDyadic n p
  | p < 0 = Dyadic (n * 2 ^ (-p)) 0
  | p > 0 && even n = (n `integerDiv` 2) `makeDyadic` (p - 1)
  | otherwise = Dyadic n p

-- | Constructs the Dyadic rational with the value of @(n / 2^p)@.
--
-- Both parameters must be same or different instances of @Integral@.
(%/) :: (Integral a, Integral b) => a -> b -> Dyadic
(%/) n p = makeDyadic (fromIntegral n) (fromIntegral p)

-- | Given an instance of @RealFloat@, converts it to a @Dyadic@.
--
-- WARNING: Its @floatRadix@ must be @2@ and it is not checked.
fromFloat :: (RealFloat a) => a -> Dyadic
fromFloat f = a `makeDyadic` fromIntegral (-b) where (a, b) = decodeFloat f

-- | Returns the pair representation of the @Dyadic@.
unmakeDyadic :: Dyadic -> (Integer, Integer)
unmakeDyadic (Dyadic n p) = (n, p)

-- | Extracts the simplified numerator of the @Dyadic@.
numerator :: Dyadic -> Integer
numerator (Dyadic n _) = n

-- | Extracts the simplified denominator of the @Dyadic@.
denominator :: Dyadic -> Integer
denominator (Dyadic _ p) = 2 ^ p

-- | Creates a @Dyadic@ that equals to a power of 2.
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
shl (Dyadic n p) d = n %/ (p - d)

-- | "Shift right": Multiply by @2^-p@ where @p@ is the second argument
shr :: Dyadic -> Integer -> Dyadic
shr (Dyadic n p) d = n %/ (p + d)

-- | Decomposes a @Dyadic@ into the integer and fractional part.
-- The fractional parts is in @[0, 1)@ for positive value
-- and @(-1, 0]@ for negative.
parts :: Dyadic -> (Integer, Dyadic)
parts 0 = (0, 0)
parts x@(Dyadic n q)
  | x < 0 = (negate *** negate) $ parts $ -x
  | otherwise = (n `div` d, p' %/ q)
  where
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
  add (Dyadic a b) (Dyadic c d) = (a * (2 ^ (d - minP)) + c * (2 ^ (b - minP))) %/ maxP
    where
      minP = min b d
      maxP = max b d

  sub p q = add p (neg q)

instance Mult Dyadic where
  mult (Dyadic a b) (Dyadic c d) = (a * c) %/ (b + d)

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
