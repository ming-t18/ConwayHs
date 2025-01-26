module Main (main) where

import Lib (Conway, omega, mono1, veb1, epsilon, epsilon0)
import Dyadic(Dyadic)

test1, test2 :: Conway Dyadic
test1 = mono1 (mono1 (veb1 omega 1 + 1) + 1)
test2 = mono1 (veb1 5 0 + 1)

main :: IO ()
main = do
    print (omega :: Conway Dyadic)
