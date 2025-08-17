module Dyadic.Bisect
  ( bisect,
    stepBisect,
    dSqrt,
  )
where

import Dyadic

stepBisect :: (a -> Dyadic -> Dyadic -> (a, Ordering)) -> (a, Dyadic, Dyadic) -> (a, Dyadic, Dyadic)
stepBisect comp s@(acc, xMid, xStep)
  | ord == EQ = s
  | ord == LT = (acc', xMid + xStep, xStep / 2)
  | otherwise = (acc', xMid - xStep, xStep / 2)
  where
    (acc', ord) = comp acc xMid xStep

-- | Performs a binary search on the interval @[n, n + 1]@ starting at @[n + 1/2]@.
bisect :: (a -> Dyadic -> Dyadic -> (a, Ordering)) -> a -> Integer -> (a, Dyadic, Dyadic)
bisect comp s0 x0 = loop (s0, fromIntegral x0 + half, half)
  where
    loop (s, xMid, xStep) =
      case comp s xMid xStep of
        (s', EQ) -> (s', xMid, xStep)
        (s', LT) -> loop (s', xMid + xStep, xStep / 2)
        (s', GT) -> loop (s', xMid - xStep, xStep / 2)

dSqrt :: Dyadic -> [Dyadic]
dSqrt n =
  map (\(_, x', _) -> x0 + x') $
    iterate (stepBisect (\s xm _ -> (s, ((x0 + xm) * (x0 + xm)) `compare` n))) $
      ((), half, half * half)
  where
    x0 :: Dyadic
    x0 = (fromIntegral :: Integer -> Dyadic) $ floor $ sqrt $ toDouble n

-- x^2 - n = 0
-- (n x)^2 - n = 0
-- f^2 - 1 = 0
