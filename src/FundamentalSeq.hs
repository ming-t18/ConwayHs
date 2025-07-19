module FundamentalSeq
  ( FSeq,
    fsOrd,
    fsFefermanShutte,
    removeSucc,
    levelDown,
    levelDownSeq,
    truncateFS,
    fsToList,
  )
where

import Data.Either (fromRight)
import qualified Data.List.NonEmpty as NE hiding (takeWhile)
import qualified Data.Map.Strict as M
import Lib
import Numeric.Natural (Natural)
import Typeclasses (isZero)

type VebMonoOrd = VebMono Natural

type FSeq = NE.NonEmpty Ordinal

m1 :: Ordinal -> Ordinal
m1 = mono1

nest :: (a -> a) -> a -> NE.NonEmpty a
nest = NE.iterate

fsOrdMono :: VebMonoOrd -> FSeq
fsOrdMono (VebMono 0 p) =
  case fsOrd p of
    -- w^(c + 1) [n] = w^c . n
    Left cPred -> nest (+ m1 cPred) 0
    -- w^L [n] = w^L[n]
    Right f -> NE.map m1 f
fsOrdMono (VebMono b 0) =
  case fsOrd b of
    -- V[b + 1, 0] [n] = (V[b, -])^(n times) 0
    Left bPred -> nest (bPred `veb1`) 0
    -- V[L, 0] [n] = V[L[n], 0]
    Right f -> NE.map (`veb1` 0) f
fsOrdMono (VebMono b0 p) =
  case fsOrd p of
    -- V[b0, c + 1]
    Left c ->
      case fsOrd b0 of
        -- V[b + 1, c + 1][n] = (V[b, -])^(n times) V[b + 1, c] + 1
        Left b -> nest (b `veb1`) $ veb1 b0 c + 1
        -- V[L, c + 1][n] = V[L[n], V[b, c] + 1]
        Right g -> NE.map (\sub -> veb1 sub $ veb1 b0 c + 1) g
    -- V[b, L] [n] = V[b, L[n]]
    Right f -> NE.map (veb1 b0) f

-- | Function to determine the fundamental sequence of an ordinal number.
-- - If the ordinal number is zero, return @Left 0@.
-- - If the ordinal number is a successor, return @Left@ of the predecessor.
-- - If the ordinal number is a limit, return @Right@ of the fundamental sequence as a function from natural number.
fsOrd :: Ordinal -> Either Ordinal FSeq
fsOrd o = case M.toAscList om of
  [] -> Left 0
  x : _ ->
    let o' = conway $ M.deleteMin om
     in case fsOrd' x of
          Left y -> Left $ y + o'
          Right f -> Right $ NE.map (o' +) f
  where
    om = toMap o
    fsOrd' :: ((Ordinal, Ordinal), Natural) -> Either Ordinal FSeq
    fsOrd' x = case x of
      ((0, 0), 0) -> error "fsOrd: not possible (normalization)"
      -- finite ordinal
      ((0, 0), n) -> Left $ finite (n - 1)
      -- V[b, c][i] = fsOrdMono ...
      ((b, c), 1) -> Right $ fsOrdMono (VebMono b c)
      -- (V[b, c]. k)[i] = V[b, c].(k - 1) + V[b, c][i]
      ((b, c), k) ->
        let f = fromRight undefined $ fsOrd' ((b, c), 1)
         in Right $ NE.map (+ veb b c (k - 1)) f

removeSucc :: Ordinal -> Maybe Ordinal
removeSucc o = case M.toAscList om of
  [] -> Nothing
  ((0, 0), _) : _ ->
    Just $ conway $ M.deleteMin om
  _ -> Nothing
  where
    om = toMap o

-- | The fundamental sequence of the Feferman-Schütte ordinal, $Gamma_0$
fsFefermanShutte :: FSeq
fsFefermanShutte = nest (`veb1` 0) 0

levelDown :: Ordinal -> Maybe Ordinal
levelDown o
  | o == omega = Just 1
  | otherwise =
    case removeSucc o of
      Just x -> Just x
      Nothing ->
        case fsOrd o of
          Left 0 -> Nothing
          Left _ -> error "levelDown: not possible"
          Right ys -> Just $ head $ dropWhile (<= 1) $ NE.toList ys

levelDownSeq :: Ordinal -> [Ordinal]
levelDownSeq o = case levelDown o of
                   Nothing -> []
                   Just x -> x : levelDownSeq x

fsToList :: FSeq -> [Ordinal]
fsToList = NE.toList

truncateFS :: Int -> FSeq -> [Ordinal]
truncateFS 0 _ = []
truncateFS n xs = take n $ NE.toList xs
