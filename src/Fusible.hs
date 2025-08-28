{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ViewPatterns #-}

-- | Helpers for dealing with fusible numbers.
module Fusible
  ( -- * Binary tree
    BinTree (..),
    mkTree,
    truncTree,
    printTree,
    inOrder,

    -- * Fundamental sequence
    fsFusible,
    fsFusible',
    fsFusibleBetween,

    -- * Order type
    ord,
    ord',
    fus,
    fus',
  )
where

import Conway
import Data.Either (fromRight)
import Data.List (intercalate)
import qualified Data.Map.Strict as M
import Dyadic
import OrdinalArith (ordAdd, ordRightSub')
import Seq.InfList (Infinite)
import qualified Seq.InfList as NE
import SignExpansion.Dyadic (FiniteSignExpansion (finiteSE))
import qualified SignExpansion.Dyadic as D
import Prelude hiding (seq)

data BinTree a = Node a (Maybe (BinTree a)) (Maybe (BinTree a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type VebMonoOrd = VebMono Natural

nest :: (a -> a) -> a -> Infinite a
nest = NE.iterate

m1 :: Ordinal -> Ordinal
m1 = mono1

fsFusibleMono :: VebMonoOrd -> Infinite Ordinal
fsFusibleMono (VebMono 0 p) =
  case fsFusible p of
    -- w^(c + 1) [n] = w^c . n
    Left cPred -> nest (+ m1 cPred) 0
    -- w^L [n] = w^L[n]
    Right f -> NE.cons 0 $ NE.tail $ NE.map m1 f
fsFusibleMono (VebMono 1 0) = NE.cons 0 $ nest m1 omega
fsFusibleMono _ = error "fsFusibleMono: not implemented: above eps0"

fsFusible :: Ordinal -> Either Ordinal (Infinite Ordinal)
fsFusible o = case M.toAscList om of
  [] -> Left 0
  x : _ ->
    let o' = conway $ M.deleteMin om
     in case fsFusible'' x of
          Left y -> Left $ y + o'
          Right f -> Right $ NE.map (o' +) f
  where
    om = toMap o
    fsFusible'' :: (VebMono Natural, Natural) -> Either Ordinal (Infinite Ordinal)
    fsFusible'' x = case x of
      (VebMono 0 0, 0) -> error "fsFusible: not possible (normalization)"
      -- finite ordinal
      (VebMono 0 0, n) -> Left $ finite (n - 1)
      -- V[b, c][i] = fsFusibleMono ...
      (VebMono b c, 1) -> Right $ fsFusibleMono (VebMono b c)
      -- (V[b, c]. k)[i] = V[b, c].(k - 1) + V[b, c][i]
      (VebMono b c, k) ->
        let f = fromRight undefined $ fsFusible'' (VebMono b c, 1)
         in Right $ NE.map (+ veb b c (k - 1)) f

fsFusible' :: Ordinal -> Infinite Ordinal
fsFusible' x = case fsFusible x of
  Right xs -> xs
  Left _ -> error "fsFusible': not a limit"

fsFusibleBetween :: Ordinal -> Ordinal -> Maybe (Infinite Ordinal)
fsFusibleBetween a b
  | hasLeading = Just $ NE.skipWhile (< a) $ fsFusible' b
  | otherwise = ((a `ordAdd`) <$>) <$> rightToMaybe (fsFusible $ ordRightSub' a b)
  where
    hasLeading = case fsFusible b of
      Right (NE.skipWhile (< a) -> seq) -> NE.head seq == a
      _ -> False

rightToMaybe :: Either a b -> Maybe b
rightToMaybe (Left _) = Nothing
rightToMaybe (Right x) = Just x

-- | Given a fundamental sequence, constructs the portion of the binary search tree
-- for the fusibles.
mkTree :: Infinite Ordinal -> BinTree Ordinal
mkTree = mkTreeBackbone Nothing
  where
    mkTreeBackbone :: Maybe Ordinal -> Infinite Ordinal -> BinTree Ordinal
    mkTreeBackbone Nothing (NE.consView -> (x, xs)) = Node x Nothing $ Just $ mkTreeBackbone (Just x) xs
    mkTreeBackbone (Just x) (NE.consView -> (x', xs)) =
      let between = NE.tail <$> fsFusibleBetween x x'
       in Node x' (mkTreeBackbone (Just x) <$> between) (Just $ mkTreeBackbone (Just x') xs)

-- | The binary search tree of the order types of all fusibles.
-- The sign expansion of a @Dyadic@ is the traversal path to find its order type in this tree.
fusibleTree :: BinTree Ordinal
fusibleTree = mkTree $ fsFusible' eps0

truncTree :: Natural -> BinTree a -> BinTree a
truncTree 0 (Node x _ _) = Node x Nothing Nothing
truncTree n (Node x a b) = Node x (f <$> a) (f <$> b) where f = truncTree (n - 1)

ind0 :: String
ind0 = ".   "

printTree :: (Show a) => BinTree a -> String
printTree = intercalate "\n" . printTreeList "" . Just

printTreeList :: (Show a) => String -> Maybe (BinTree a) -> [String]
printTreeList ind Nothing = [ind ++ "---"]
printTreeList ind (Just (Node x l r)) =
  printTreeList (ind ++ ind0) l
    ++ [ind ++ "Node " ++ show x]
    ++ printTreeList (ind ++ ind0) r

inOrder :: BinTree a -> [a]
inOrder (Node x a b) = maybe [] inOrder a ++ [x] ++ maybe [] inOrder b

-- | Given a dyadic rational, determine if it is a fusible number and returns its order type.
--
-- * Not a fusible number: @Nothing@
--
-- * Is a fusible number: @Just o@ where @o@ is its order type.
ord :: Dyadic -> Maybe Ordinal
ord d = trav tree se
  where
    trav :: BinTree Ordinal -> [(Bool, Natural)] -> Maybe Ordinal
    trav (Node o _ _) [] = Just o
    trav (Node _ _ r) ((True, i) : xs)
      | i <= 1 = r >>= (`trav` xs)
      | otherwise = r >>= (`trav` ((True, i - 1) : xs))
    trav (Node _ l _) ((False, i) : xs)
      | i <= 1 = l >>= (`trav` xs)
      | otherwise = l >>= (`trav` ((False, i - 1) : xs))
    se = D.toList $ finiteSE d
    tree = fusibleTree

ord' :: Dyadic -> Ordinal
ord' x = case ord x of
  Nothing -> error "Fusible.ord': not a fusible number"
  Just o -> o

-- | Given an @Ordinal@, find the @Maybe@ of its corresponding fusible number if exists.
fus :: Ordinal -> Maybe Dyadic
fus o
  | o >= epsilon0 = Nothing
  | otherwise = D.parseDyadicSE <$> binarySearch D.empty fusibleTree
  where
    binarySearch :: D.FSE -> BinTree Ordinal -> Maybe D.FSE
    binarySearch se (Node o' l r)
      | o == o' = Just se
      | o < o' = l >>= binarySearch (se D.+++. D.minus (1 :: Natural))
      | otherwise = r >>= binarySearch (se D.+++. D.plus (1 :: Natural))

fus' :: Ordinal -> Dyadic
fus' x = case fus x of
  Nothing -> error "Fusible.fus': not a fusible order type"
  Just o -> o
