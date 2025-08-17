module Dyadic.Ratio (LongDivState, defaultLongDivState, stepBisectCheck, stepLongDiv) where

import Data.Map (Map)
import qualified Data.Map as M
import Dyadic
import Dyadic.Bisect (stepBisect)

data LongDivState = LongDivState
  { graph :: Map Dyadic (Bool, Dyadic),
    divisor :: !Integer,
    num :: !Dyadic,
    signs :: [Bool],
    path :: [Dyadic]
  }
  deriving (Show)

defaultLongDivState :: Dyadic -> Integer -> LongDivState
defaultLongDivState n d =
  LongDivState
    { graph = M.empty,
      divisor = d,
      num = n,
      signs = [True, False],
      path = [1, half]
    }

-- r/d == q -> r == q*d

stepBisectCheck :: LongDivState -> Dyadic -> Dyadic -> (LongDivState, Ordering)
stepBisectCheck LongDivState {graph = g, divisor = d, num = n, signs = ss, path = p} q dq = (st', ord)
  where
    ord = (q * fromIntegral d) `compare` n
    inv = (1 :: Integer) %/ negate (snd $ unmakeDyadic dq)
    rem0 = n - (q * fromIntegral d)
    rem1 = n - (q + (if ord == LT then dq else -dq)) * fromIntegral d
    g' = M.insert (inv * rem0) (sign, 2 * inv * rem1) g
    sign = ord == LT
    p' = p ++ [inv * rem0]
    st' = LongDivState {graph = g', divisor = d, num = n, signs = ss ++ [ord == LT], path = p'}

stepLongDiv :: (LongDivState, Dyadic, Dyadic) -> (LongDivState, Dyadic, Dyadic)
stepLongDiv = stepBisect stepBisectCheck
