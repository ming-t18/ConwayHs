{-# LANGUAGE ViewPatterns #-}

module SignExpansion.Reduce (reduce, reduceSingle, unreduce, unreduceSingle, unreduceStep) where

import Control.Monad (foldM)
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
        pChosen = longestCommonPrefix p ps
        -- The reduced sign expansion
        po = if null ps then p else pChosen `reduceSingle` p

longestCommonPrefix :: (Foldable t) => SignExpansion -> t SignExpansion -> SignExpansion
longestCommonPrefix p = maximumBy (comparing $ SE.length . commonPrefix p)

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

unreduce :: [SignExpansion] -> Maybe [SignExpansion]
unreduce = foldM unreduceStepAndAppend []
  where
    unreduceStepAndAppend :: [SignExpansion] -> SignExpansion -> Maybe [SignExpansion]
    unreduceStepAndAppend ps0 po = (ps0 ++) . (: []) <$> unreduceStep ps0 po

-- | Given unreduced sign expansions in descending order
-- and a reduced sign expansion, unreduce it
-- given the unreduced sign expansions and make sure the descending order is preserved.
unreduceStep :: [SignExpansion] -> SignExpansion -> Maybe SignExpansion
unreduceStep [] po = Just po
unreduceStep ps0@(last -> pLast) po
  | null ps' = Nothing
  | otherwise = Just $ snd $ maximumBy (comparing fst) ps'
  where
    ps' = filter ((< pLast) . snd) $ map cpLenAndUnreduce ps0
    cpLenAndUnreduce p0 = (SE.length $ commonPrefix p p0, p)
      where
        p = unreduceSingle p0 po
