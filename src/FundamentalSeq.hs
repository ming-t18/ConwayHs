module FundamentalSeq
  ( FSeq,
    fsOrd,
    fsOrd',
    fsFefermanShutte,
    removeSucc,
    levelDown,
    levelDownSeq,
    truncateFS,
    fsToList,
    isLimit,
  )
where

import Conway
import Data.Either (fromRight, isRight)
import qualified Data.Map.Strict as M
import Seq.InfList (Infinite)
import qualified Seq.InfList as NE

type VebMonoOrd = VebMono Natural

-- | A fundamental sequence is an infinite list, represented by
-- a `Data.List.NonEmpty Ordinal`, listing
-- @[f 0, f 1, f 2, f 3, ...]@
type FSeq = Infinite Ordinal

m1 :: Ordinal -> Ordinal
m1 = mono1

nest :: (a -> a) -> a -> Infinite a
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
        Right g -> NE.map (\s -> veb1 s $ veb1 b0 c + 1) g
    -- V[b, L] [n] = V[b, L[n]]
    Right f -> NE.map (veb1 b0) f

-- | Function to determine the fundamental sequence of an ordinal number.
--
-- * If the ordinal number is zero, return @Left 0@.
--
-- * If the ordinal number is a successor, return @Left@ of the predecessor.
--
-- * If the ordinal number is a limit, return @Right@ of the fundamental sequence as a function from natural number.
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
    fsOrd' :: (VebMono Natural, Natural) -> Either Ordinal FSeq
    fsOrd' x = case x of
      (VebMono 0 0, 0) -> error "fsOrd: not possible (normalization)"
      -- finite ordinal
      (VebMono 0 0, n) -> Left $ finite (n - 1)
      -- V[b, c][i] = fsOrdMono ...
      (VebMono b c, 1) -> Right $ fsOrdMono (VebMono b c)
      -- (V[b, c]. k)[i] = V[b, c].(k - 1) + V[b, c][i]
      (VebMono b c, k) ->
        let f = fromRight undefined $ fsOrd' (VebMono b c, 1)
         in Right $ NE.map (+ veb b c (k - 1)) f

-- | Like @fsOrd@, except it is a partial function for limit ordinals only.
fsOrd' :: Ordinal -> FSeq
fsOrd' x = case fsOrd x of
  Left _ -> error "fsOrd': not a limit ordinal"
  Right xs -> xs

-- | Given an ordinal number, returns a new ordinal (zero/limit) without the successor part.
--
-- * If the input is zero, return `Nothing`
--
-- * If the input is finite, return `Just 0`
--
-- * If the input is a successor ordinal, return `Just x` where `x` is the ordinal with the successors removed.
removeSucc :: Ordinal -> Maybe (Ordinal, Natural)
removeSucc o = case M.toAscList om of
  [] -> Nothing
  (VebMono 0 0, n) : _ ->
    Just (conway $ M.deleteMin om, n)
  _ -> Nothing
  where
    om = toMap o

-- | The fundamental sequence of the Feferman-Schütte ordinal, Γ_0.
fsFefermanShutte :: FSeq
fsFefermanShutte = nest (`veb1` 0) 0

-- | Given an ordinal number, returns a smaller and simpler ordinal by either picking the first infinite value
-- from its fundamental sequence, or @1@ for @omega@.
levelDown :: Ordinal -> Maybe Ordinal
levelDown o
  | o == omega = Just 1
  | otherwise =
      case removeSucc o of
        Just (x, _) -> Just x
        Nothing ->
          case fsOrd o of
            Left 0 -> Nothing
            Left _ -> error "levelDown: not possible"
            Right ys ->
              case dropWhile (<= 1) $ NE.toList ys of
                [] -> error "levelDown: not possible"
                (x : _) -> Just x

-- | Given an ordinal number, returns a iterating sequence of `levelDown` until reaching zero.
levelDownSeq :: Ordinal -> [Ordinal]
levelDownSeq o = case levelDown o of
  Nothing -> []
  Just x -> x : levelDownSeq x

-- | Converts a fundamental sequence to a Haskell list.
fsToList :: FSeq -> [Ordinal]
fsToList = NE.toList

-- | Truncates a fundamental sequence to a limited number of terms.
truncateFS :: Int -> FSeq -> [Ordinal]
truncateFS 0 _ = []
truncateFS n xs = take n $ NE.toList xs

isLimit :: Ordinal -> Bool
isLimit = isRight . fsOrd
