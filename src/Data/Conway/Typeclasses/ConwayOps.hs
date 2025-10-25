{-# LANGUAGE FunctionalDependencies #-}

module Data.Conway.Typeclasses.ConwayOps (Veb (..), UnVeb (..), eps) where

import Data.Conway.Typeclasses.Algebra

class (OrdZero o, Ord o) => Veb o a | a -> o where
  {-# MINIMAL veb1 #-}

  -- | Evaluates the Veblen hierarchy function
  veb1 :: o -> a -> a

  mono1 :: a -> a
  mono1 = veb1 zero

-- | A generic typeclass for a type @a@ that contains
-- a Veblen hierarchy function @veblen@ indexed by an order
-- of type @o@.
--
-- Laws of the @Veblen@ typeclass:
--
-- * If @a < b@, then @veblen a x < veblen b x@
--
-- * If @a < b@, then @veblen a (veblen b x) === veblen b x@
--
-- * If @unVeblen x === Just (b, y)@, then @veblen a x === x@ for all @a < b@.
class (OrdZero o, Ord a) => UnVeb o a | a -> o where
  -- | Determines if the argument can be written in the form of @veblen o x@,
  -- for the largest possible @o@, and returns:
  --
  -- * @Just (o, x)@ if true
  --
  -- * @Nothing@ otherwise
  unVeb1 :: a -> Maybe (o, a)

eps :: (One o, Veb o a) => a -> a
eps = veb1 one
