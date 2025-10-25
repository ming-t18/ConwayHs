{-# LANGUAGE FunctionalDependencies #-}

module Data.Conway.Typeclasses.ConwayOps
  ( Veb (..),
    UnVeb (..),
    Birthday (..),
    CommonPrefix (..),
    BinaryConstruct (..),
    (/\),
    eps,
  )
where

import Data.Conway.Typeclasses.Algebra

infixr 6 /\

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

-- | Typeclass for a type @a@ that represents a subset of surreal numbers with
-- birthday of type @o@.
class (OrdZero o) => Birthday o a | a -> o where
  birthday :: a -> o

-- | Typeclass for a type @a@ with the "longest common prefix" operation.
--
-- Properties:
--
-- * @birthday (commonPrefix x y)@ is maximized.
--
-- * @commonPrefix@ forms a meet-semilattice with @commonPrefix x zero === zero@
--
-- * @isPrefixOf@ and @prefixPartialCompare@ form a partial order based on simplicity.
class (OrdZero a) => CommonPrefix a where
  {-# MINIMAL commonPrefix #-}
  commonPrefix :: a -> a -> a

  isPrefixOf :: a -> a -> Bool
  isPrefixOf a b = a == commonPrefix a b

  prefixPartialCompare :: a -> a -> Maybe Ordering
  prefixPartialCompare a b
    | a == b = Just EQ
    | c == a = Just LT
    | c == b = Just GT
    | otherwise = Nothing
    where
      c = commonPrefix a b

-- simpleLeq :: a -> a -> Bool

-- | Typeclass for a type @a@ with the @{ left | right }@ operation where
-- @left@ and @right@ are single values of type @a@.
--
-- Properties:
--
-- * @birthday (binaryConstruct x y)@ is maximized
--
-- * Let @z = binaryConstruct x y@, @x < y && y < z@
class (CommonPrefix a) => BinaryConstruct a where
  -- | Partial function requiring @x < y@ for @binaryConstruct x y@.
  binaryConstruct :: a -> a -> a

(/\) :: (CommonPrefix a) => a -> a -> a
(/\) = commonPrefix
