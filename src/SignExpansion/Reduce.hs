{-# LANGUAGE ViewPatterns #-}

module SignExpansion.Reduce (reduce, reduceSingle, unreduceSingle) where

import Data.Foldable (maximumBy)
import Data.Ord (comparing)
import Data.Set (Set)
import qualified Data.Set as S
import OrdinalArith (ordRightSub')
import SignExpansion.Types as SE

-- | Given a list of sign expansions of Cantor/Conway normal form exponents in descending order,
-- returns a list of reduced sign expansion exponents.
--
-- Reduced sign expansions is explained in [Gonshor] Theorem 5.11(c) and rest of the chapter.
reduce :: [SignExpansion] -> [SignExpansion]
reduce = snd . foldl reduceStep (S.empty, [])
  where
    reduceStep :: (Set SignExpansion, [SignExpansion]) -> SignExpansion -> (Set SignExpansion, [SignExpansion])
    reduceStep (ps, pos) p = (S.insert p ps, pos ++ [po])
      where
        -- Choose a previous @p@ by longest common prefix.
        pChosen = maximumBy (comparing $ SE.length . commonPrefix p) ps
        -- The reduced sign expansion
        po = if null ps then p else pChosen `reduceSingle` p

-- | Constructs a reduced sign expansion of the second argument given first argument as a base.
--
-- Property: @p < p0 ==> unreduceSingle p0 (reduce p0 p) === p@
-- This property can be false or call @error@ if the condition @p < p0@ is false.
reduceSingle :: SignExpansion -> SignExpansion -> SignExpansion
reduceSingle pb (takeCommonPrefix pb -> (pre, (_, suffix))) = plus (SE.countSigns True pre) +++ suffix

unreduceSingle :: SignExpansion -> SignExpansion -> SignExpansion
unreduceSingle pb (takeLeading True -> (nLead, pRest))
  | nLead > nPlus = pb +++ plus (ordRightSub' nPlus nLead) +++ pRest
  | otherwise = SE.takeUntilNthSign (True, nLead) pb +++ pRest
  where
    nPlus = countSigns True pb
