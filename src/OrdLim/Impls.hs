{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module OrdLim.Impls (NatPair (..), List' (..)) where

import Conway
import OrdLim.Types
import Typeclasses
import Prelude hiding (pred, succ)

-- | A pair of natural numbers. Has order type of @w^2@.
--
-- For demonstration only.
-- Use the @OrdLim@ implementation for @(Natural, Natural)@ instead.
newtype NatPair = NP (Natural, Natural)
  deriving (Eq, Ord, Show)

-- | Wrapper type for a list that is ordered lexicographically
-- starting from the leftmost element.
--
-- If two lists have different number of elements, the shorter
-- list is left-padded with zeroes (@Zero@ typeclass)
-- before checking equality or comparison.
newtype List' a = List' {toList :: [a]}
  deriving (Show)

mapRev :: ([a] -> [a]) -> List' a -> List' a
mapRev f = List' . reverse . f . reverse . toList

mapRevM :: (Functor m) => ([a] -> m [a]) -> List' a -> m (List' a)
mapRevM f (List' xs) = List' . reverse <$> f (reverse xs)

zeroPad :: (Zero a) => [a] -> [a] -> ([a], [a])
zeroPad xs ys
  | xl == yl = (xs, ys)
  | xl < yl = (rep (yl - xl) ++ xs, ys)
  | otherwise = (xs, rep (xl - yl) ++ ys)
  where
    xl = length xs
    yl = length ys
    rep = (`replicate` zero)

instance (OrdZero a) => Eq (List' a) where
  (==) (List' a) (List' b) = a' == b'
    where
      (a', b') = zeroPad a b

instance (OrdZero a) => Ord (List' a) where
  compare (List' a) (List' b) = a' `compare` b'
    where
      (a', b') = zeroPad a b

instance Zero NatPair where
  zero = NP (0, 0)
  isZero (NP (0, 0)) = True
  isZero _ = False

instance OrdZero NatPair where
  neg (NP (0, 0)) = zero
  neg _ = error "not defined"

instance OrdLim NatPair where
  limSeq = NP . (,0) <$> [0 ..]
  succ (NP (x, y)) = NP (x, y + 1)
  pred (NP (_, 0)) = Nothing
  pred (NP (x, y)) = Just (NP (x, y - 1))

  getOrdLim (NP (0, 0)) = Zero
  getOrdLim (NP (x, 0)) = Limit (map (NP . (x - 1,)) [0 ..])
  getOrdLim (NP (x, y)) = Succ (NP (x, y - 1))

instance Zero (List' a) where
  zero = List' []
  isZero (List' []) = True
  isZero _ = False

instance (OrdZero a) => OrdZero (List' a) where
  neg (List' []) = List' []
  neg _ = error "not defined"

instance (OrdLim a) => OrdLim (List' a) where
  limSeq = List' <$> iterate (++ [zero]) [one'] where one' = succ zero
  succ =
    mapRev
      ( \case
          [] -> []
          (x : xs) -> (succ x : xs)
      )

  pred =
    mapRevM
      ( \case
          [] -> Nothing
          (x : xs) -> (: xs) <$> pred x
      )

  getOrdLim (List' l) = case reverse l of
    [] -> Zero
    xs'@(z : _) | isZero z -> Limit $ map (List' . reverse) $ unLim xs'
    x : xs -> Succ $ List' $ reverse (pred' x : xs)
    where
      unLim [] = error "unLim: empty"
      unLim [_] = undefined
      unLim (z : xs'@(v : xs))
        | isZero z && isZero v = map (z :) $ unLim xs'
        | isZero z = let xs'' = pred' v : xs in map (: xs'') (iterate succ zero)
        | otherwise = undefined
