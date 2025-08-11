module SignExpansion.Reduce (reduce, reduceSingle) where

import Control.Arrow ((&&&))
import Data.Set (Set)
import qualified Data.Set as S
import SignExpansion.Types as SE

-- | Given a list of sign expansions of Cantor/Conway normal form exponents in descending order,
-- returns a list of reduced sign expansion exponents.
reduce :: [SignExpansion] -> [SignExpansion]
reduce = snd . foldl reduceStep (S.empty, [])
  where
    reduceStep :: (Set SignExpansion, [SignExpansion]) -> SignExpansion -> (Set SignExpansion, [SignExpansion])
    reduceStep (ps, pos) p = (S.insert p ps, pos ++ [po])
      where
        pChosen = fmap (snd . fst) $ S.maxView $ S.map ((SE.length . commonPrefix p) &&& id) ps
        po = maybe p (`reduceSingle` p) pChosen

reduceSingle :: SignExpansion -> SignExpansion -> SignExpansion
reduceSingle po p = plus (SE.countSigns True pre) +++ suffix where (pre, (_, suffix)) = takeCommonPrefix po p
