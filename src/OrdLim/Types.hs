{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module OrdLim.Types (OrdLim (..), OrdLimCases (..), OrdLimCases1 (..)) where

import Conway
import Data.List (intercalate)
import Typeclasses
import Prelude hiding (pred, succ)

infixr 5 :+.

newtype ShowTrunc a = ShowTrunc [a]
  deriving (Functor)

instance (Show a) => Show (ShowTrunc a) where
  show (ShowTrunc xs) = "[" ++ intercalate ", " (take 10 $ map show xs) ++ ", ...]"

data OrdLimCasesShow a = Zero' | a :+. Natural | Succ' a | Limit' (ShowTrunc a)
  deriving (Show, Functor)

data OrdLimCases a = Zero | Succ a | Limit [a]
  deriving (Eq, Functor)

data OrdLimCases1 a = Zero1 | PlusFin a Natural | Limit1 [a]
  deriving (Eq, Functor)

instance (Show a) => Show (OrdLimCases a) where
  show x = show (toRepr x)
    where
      toRepr Zero = Zero'
      toRepr (Succ x') = Succ' x'
      toRepr (Limit xs) = Limit' (ShowTrunc xs)

instance (Show a) => Show (OrdLimCases1 a) where
  show x = show (toRepr x)
    where
      toRepr Zero1 = Zero'
      toRepr (PlusFin x' n) = x' :+. n
      toRepr (Limit1 xs) = Limit' (ShowTrunc xs)

-- | Typeclass for a total order (@Ord@) that "behaves" like an ordinal number
-- under the transfinite induction definition of ordinal numbers.
--
-- Important: The order type must be a limit ordinal.
--
-- 1. Zero
--
-- 2. Successor
--
-- 3. Limit (has a fundamental sequence as an ascending infinite list)
class (OrdZero a) => OrdLim a where
  {-# MINIMAL succ, pred, getOrdLim, limSeq #-}

  -- | The fundamental sequence of the order type of this typeclass.
  limSeq :: [a]

  -- | Ordinal successor. Must always be defined.
  succ :: a -> a

  -- | Ordinal predecessor. Should return @Nothing@ on @Zero@ and @Limit@ cases.
  pred :: a -> Maybe a

  -- | Ordinal predecessor as a partial function.
  pred' :: a -> a
  pred' x =
    case pred x of
      Nothing -> error "OrdLim.pred': not a successor ordinal"
      Just x' -> x'

  -- | Repeated application of ordinal predecessor.
  -- | Returns @(x', n)@ where the number of times @pred@ can be applied @n@
  -- before it becomes @x'@ where @x'@ is no longer a successor.
  pred1 :: a -> (a, Natural)
  pred1 = predMulti' 0
    where
      predMulti' n x =
        case pred x of
          Just x' -> predMulti' (n + 1) x'
          _ -> (x, n)

  pred x = case getOrdLim x of
    Succ y -> Just y
    _ -> Nothing

  -- | Analyzes the ordinal as a zero/successor/limit.
  getOrdLim :: a -> OrdLimCases a

  -- | Analyzes the ordinal as a zero/successor/limit.
  -- where the successor case applies @pred1@ to strip out
  -- all successors.
  getOrdLim1 :: a -> OrdLimCases1 a
  getOrdLim1 x =
    case getOrdLim x of
      Zero -> Zero1
      Succ s -> PlusFin s' (n + 1) where (s', n) = pred1 s
      Limit f -> Limit1 f where

-- * Common order types

-- | Has order type of @w@.
instance OrdLim Natural where
  limSeq = [0 ..]
  succ = (+ 1)
  pred 0 = Nothing
  pred n = Just (n - 1)

  getOrdLim 0 = Zero
  getOrdLim n = Succ (n - 1)

-- | The sum order. @Left@ instances are ordered before @Right@ instances.
instance (OrdZero a, OrdZero b, OrdLim a, OrdLim b) => OrdLim (Either a b) where
  limSeq = map Right limSeq
  succ = either (Left . succ) (Right . succ)
  pred (Left x) = Left <$> pred x
  pred (Right x) = Right <$> pred x
  getOrdLim (Left x) = Left <$> getOrdLim x
  getOrdLim (Right x) = Right <$> getOrdLim x

-- | The product order. Lexicographical order from left to right.
instance (OrdZero a, OrdZero b, OrdLim a, OrdLim b) => OrdLim (a, b) where
  limSeq = map (,zero) limSeq
  succ (x, y) = (x, succ y)
  pred (x, y) = (x,) <$> pred y
  getOrdLim (x, y)
    | isZero y =
        case getOrdLim x of
          Zero -> Zero
          Succ x' -> Limit ((x',) <$> limSeq)
          Limit l -> Limit ((,zero) <$> l)
    | otherwise = (x,) <$> getOrdLim y
