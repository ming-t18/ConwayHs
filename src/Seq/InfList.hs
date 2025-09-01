{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}

module Seq.InfList
  ( Infinite,
    consView,
    head,
    tail,
    cons,
    prepend,
    repeat,
    iterate,
    skip,
    take,
    map,
    skipWhile,
    toList,
    index,
  )
where

import Conway (Natural, Ordinal, finiteView, omega)
import Data.List (intercalate)
import qualified Seq.Types (Seq (..))
import Prelude hiding (head, iterate, length, map, repeat, tail, take)

-- | Represents an infinite list with element type @a@.
-- An infinite list is also a transfinite sequence with order type @omega@.
data Infinite a = Inf a (Infinite a)
  deriving (Foldable, Functor, Traversable)

instance (Show a) => Show (Infinite a) where
  show xs = "Inf [" ++ intercalate ", " (show <$> take 5 xs) ++ ", ...]"

instance Seq.Types.Seq (Infinite a) Ordinal a where
  length _ = omega
  (!) xs (finiteView -> Just i) = index xs i
  (!) _ _ = error "Infinite.!: index is finite"

consView :: Infinite a -> (a, Infinite a)
consView (Inf x xs) = (x, xs)

head :: Infinite a -> a
head (Inf x _) = x

tail :: Infinite a -> Infinite a
tail (Inf _ xs) = xs

cons :: a -> Infinite a -> Infinite a
cons = Inf

prepend :: (Foldable t) => t a -> Infinite a -> Infinite a
prepend = flip $ foldr cons

repeat :: a -> Infinite a
repeat x = Inf x $ repeat x

iterate :: (a -> a) -> a -> Infinite a
iterate f x = Inf x $ iterate f $ f x

skip :: Natural -> Infinite a -> Infinite a
skip 0 xs = xs
skip n (Inf _ xs) = skip (n - 1) xs

take :: Natural -> Infinite a -> [a]
take 0 _ = []
take n (Inf x xs) = x : take (n - 1) xs

map :: (a -> b) -> Infinite a -> Infinite b
map = fmap

skipWhile :: (a -> Bool) -> Infinite a -> Infinite a
skipWhile p xs0@(Inf x xs)
  | p x = skipWhile p xs
  | otherwise = xs0

toList :: Infinite a -> [a]
toList (Inf x xs) = x : toList xs

index :: Infinite a -> Natural -> a
index (Inf x _) 0 = x
index (Inf _ xs) n = index xs (n - 1)
