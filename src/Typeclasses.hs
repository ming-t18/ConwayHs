{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Typeclasses (
    -- | Typeclasses for algebraic properties related to ordinal and surreal numbers.
    -- Custom numeric types should implement these typeclasses so they can be used in @Conway@.
    Zero(..), One(..), OrdZero(..), AddSub(..), Mult(..), OrdRing
) where
import Data.Ratio (Ratio, (%))
import Numeric.Natural

class Zero a where
    zero :: a
    isZero :: a -> Bool

class One a where
    one :: a

-- | Typeclass for a total order with a zero element and negation around the zero element.
--
-- Properties:
--
-- 1. @neg zero == zero@
--
-- 2. @neg (neg x) == x@
--
-- 3. @x >= y ==> neg y >= neg x@
class (Zero a, Ord a) => OrdZero a where
    neg :: a -> a
    isPositive, isNegative :: a -> Bool
    isPositive = (> zero)
    isNegative = (< zero)
    compareZero :: a -> Ordering
    compareZero x = compare x zero

class OrdZero a => AddSub a where
    add :: a -> a -> a
    sub :: a -> a -> a
    sub a b = add a (neg b)

class (OrdZero a, One a) => Mult a where
    mult :: a -> a -> a

class (OrdZero a, AddSub a, Mult a) => OrdRing a where
    --

instance Zero Integer where
    zero = 0
    isZero = (==) 0

instance One Integer where
    one = 1

instance OrdZero Integer where
  neg = negate

instance AddSub Integer where
    add = (+)
    sub = (-)

instance Mult Integer where
    mult = (*)

instance OrdRing Integer where

instance Zero Natural where
    zero = 0
    isZero = (==) 0

instance One Natural where
    one = 1

-- | Negating a non-zero natural number causes the arithmetic underflow error.
instance OrdZero Natural where
  neg = negate

instance AddSub Natural where
    add = (+)
    sub = (-)

instance Mult Natural where
    mult = (*)

instance OrdRing Natural where


instance (Integral a, Zero a, One a) => Zero (Ratio a) where
    zero = zero % one
    isZero = (==) zero

instance (Integral a, One a) => One (Ratio a) where
    one = one % one

instance (Integral a, OrdZero a, One a, Num a) => OrdZero (Ratio a) where
  neg a = -a

instance (Integral a, Num a, OrdZero a, One a) => AddSub (Ratio a) where
    add = (+)
    sub = (-)

instance (Integral a, Num a, OrdZero a, One a) => Mult (Ratio a) where
    mult = (*)

instance (Integral a, Num a, OrdRing a) => OrdRing (Ratio a) where

newtype Sum a = Sum a deriving (Eq, Ord, Show, Read, Functor)
newtype Product a = Product a deriving (Eq, Ord, Show, Read, Functor)

instance AddSub a => Semigroup (Sum a) where
    (<>) (Sum a) (Sum b) = Sum (add a b)

instance AddSub a => Monoid (Sum a) where
    mempty = Sum zero

instance Mult a => Semigroup (Product a) where
    (<>) (Product a) (Product b) = Product (mult a b)

instance Mult a => Monoid (Product a) where
    mempty = Product zero
