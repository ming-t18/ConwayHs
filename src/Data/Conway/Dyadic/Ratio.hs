module Data.Conway.Dyadic.Ratio (LongDivState, defaultLongDivState, stepBisectCheck, divByInteger) where

import Data.Conway.Dyadic
import Data.Conway.Dyadic.Bisect
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (isJust)

data LongDivState = LongDivState
  { graph :: Map Dyadic (Bool, Dyadic),
    divisor :: !Integer,
    num :: !Dyadic,
    signs :: [Bool],
    path :: [(Dyadic, Dyadic, Bool)],
    hasCycle :: Maybe Dyadic
  }
  deriving (Show)

defaultLongDivState :: Dyadic -> Integer -> LongDivState
defaultLongDivState n d =
  LongDivState
    { graph = M.empty,
      divisor = d,
      num = n,
      -- [True, False] omitted
      signs = [],
      path = [],
      hasCycle = Nothing
    }

-- r/d == q -> r == q*d

stepBisectCheck :: LongDivState -> Dyadic -> Dyadic -> (LongDivState, Ordering)
stepBisectCheck st0@LongDivState {graph = g, divisor = d, num = n, signs = ss, path = p, hasCycle = hasCycle0} q dq
  | isJust hasCycle0 = (st0, EQ)
  | otherwise = (st', ord)
  where
    ord = (q * fromIntegral d) `compare` n
    inv = (1 :: Integer) %/ negate (snd $ unmakeDyadic dq)
    rem0' = inv * rem0 where rem0 = n - (q * fromIntegral d)
    rem1' = 2 * inv * rem1 where rem1 = n - (q + (if ord == LT then dq else -dq)) * fromIntegral d
    g' = M.insert rem0' (sign, rem1') g
    sign = ord == LT
    p' = p ++ [(q, rem0', sign)]
    hasCycle' = if rem1' `M.member` g then Just rem1' else Nothing
    st' = LongDivState {graph = g', divisor = d, num = n, signs = ss ++ [ord == LT], path = p', hasCycle = hasCycle'}

divByInteger :: Dyadic -> Integer -> (LongDivState, Dyadic)
divByInteger n d = (st, q)
  where
    (st, q, _) = bisect stepBisectCheck (defaultLongDivState n d) f
    f = floor (toDouble n / fromIntegral d) :: Integer
