{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
module Typeclasses (
  -- | Typeclasses for algebraic properties related to ordinal and surreal numbers.
  -- Custom numeric types should implement these typeclasses so they can be used in @Conway@.
  Zero(..), One(..), OrdZero(..), AddSub(..), Mult(..), OrdRing, Veblen(..)
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

-- | A generic typeclass for a type @a@ that contains
-- a Veblen hierarchy functio @veblen@ with order type @o@.
--
-- @o@ can be a representation of ordinal numbers, or a
-- representation of an array of ordinals such as Klammersymbolen.
--
-- Laws of the @Veblen@ typeclass:
--
-- * If @a < b@, then @veblen a x < veblen b x@
--
-- * If @a < b@, then @veblen a (veblen b x) === veblen b x@
--
-- * If @unVeblen x === Just (b, y)@, then @veblen a x === x@ for all @a < b@.
--
class (OrdZero o, Ord a) => Veblen a o | a -> o where
  veblen :: o -> a -> a
  unVeblen :: a -> Maybe (o, a)

-- * Integer

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

-- * Int

instance Zero Int where
  zero = 0
  isZero = (==) 0

instance One Int where
  one = 1

instance OrdZero Int where
  neg = negate

instance AddSub Int where
  add = (+)
  sub = (-)

instance Mult Int where
  mult = (*)

instance OrdRing Int where

-- * Natural

instance Zero Natural where
  zero = 0
  isZero = (==) 0

instance One Natural where
  one = 1

-- | Negating a non-zero natural number causes the arithmetic underflow error.
instance OrdZero Natural where
  neg = negate
  isNegative _ = False

-- | @sub@ is subject to arithmetic underflow errors.
instance AddSub Natural where
  add = (+)
  sub = (-)

instance Mult Natural where
  mult = (*)

instance OrdRing Natural where

-- * Float

instance Zero Float where
  zero = 0
  isZero = (==) 0

instance One Float where
  one = 1

instance OrdZero Float where
  neg = negate

instance AddSub Float where
  add = (+)
  sub = (-)

instance Mult Float where
  mult = (*)

instance OrdRing Float where

-- * Ratio

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
