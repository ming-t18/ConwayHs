{-# LANGUAGE FunctionalDependencies #-}

module Data.Conway.Typeclasses.ConwayOps (Veb (..), UnVeb (..), mono1, eps) where

import Data.Conway.Typeclasses.Algebra

class (OrdZero o, Ord o) => Veb o a | a -> o where
  -- | Evaluates the Veblen hierarchy function
  veb1 :: o -> a -> a

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

mono1 :: (Veb o a) => a -> a
mono1 = veb1 zero

eps :: (One o, Veb o a) => a -> a
eps = veb1 one
