{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

-- | Parsing sign expansions
--
-- The basic algorithm for parsing sign expansions is:
--
-- 1. Parse the sign expansion term-by-term (@mono p_i c_i@)
--
-- 2. Unreduce the exponents @p_i@ of each term
--
-- 3. Detect the Veblen order of each term @p_i = veb1 o_i p_i' @ and parse them recursively
module Data.Conway.SignExpansion.Parser
  ( -- * Helpers
    ParseVeb (..),
    lookVebMono,

    -- * Parsing multiple terms
    parseToConway,
    parseToUnreduced,
    combineToConway,

    -- ** Reduced sign expansions
    parseToReduced,
    unreduceReduced,

    -- * Detecting Veblen order
    detectFixedPointSE,
    detectVebOrder,
    detectVebOrderCandidates,

    -- * Parsing terms
    parseMono,
    parseRealSuffix,

    -- * Parsing @mono1@s
    parseVeb1,
    vebOrdersFromMinusPart,
  )
where

import Control.Arrow (first)
import Control.Monad (guard)
import Control.Monad.State
import Data.Conway.Conway
import Data.Conway.Dyadic (Dyadic)
import Data.Conway.OrdinalArith (ordAdd, ordDivRem, ordPow, ordSymDiff, unMono1)
import Data.Conway.Seq as Seq
import Data.Conway.SignExpansion.Dyadic (FSE, parseDyadicSE)
import qualified Data.Conway.SignExpansion.Dyadic as SD
import Data.Conway.SignExpansion.Reduce (Reduced (..), unreduce')
import Data.Conway.SignExpansion.Types (SignExpansion)
import qualified Data.Conway.SignExpansion.Types as SE
import Data.Conway.SignExpansion.Veb (veb1SE)
import Data.Conway.Typeclasses (One (..), OrdZero (..), Zero (..))
import qualified Data.Set as Set
import Prelude hiding (replicate)

-- * Parser monad

newtype SEParser se a = SEP {getSEParser :: State se a}
  deriving (Functor, Applicative, Monad, MonadState se)

sep :: (se -> (a, se)) -> SEParser se a
sep = SEP . state

runSEP :: SEParser se a -> se -> (a, se)
runSEP = runState . getSEParser

data ParseVeb se cse
  = ParseVeb
  { nPlusArg :: Ordinal,
    vebOrder :: Ordinal,
    vebArgSE :: se,
    coeffSE :: cse,
    coeffDidBacktrack :: Bool
  }
  deriving (Show)

emptyParseVeb :: (Zero se, Zero cse) => ParseVeb se cse
emptyParseVeb = (ParseVeb {nPlusArg = zero, vebOrder = zero, vebArgSE = zero, coeffSE = zero, coeffDidBacktrack = False})

-- * Parsing @Conway@

parseToConway :: SignExpansion -> Conway Dyadic
parseToConway se =
  case detectFixedPointSE se res of
    Just (0, _) -> error "parseToConway: detected infinite recursion, detected vebOrder is 0."
    Just (o, p') | p' == se -> error $ "parseToConway: detected infinite recursion, detected vebOrder is " ++ show o ++ "."
    Just (o, p') -> veb1 o $ parseToConway p'
    Nothing -> combineToConway res
  where
    -- veb1 p s
    res = parseToUnreduced se

detectFixedPointSE :: SignExpansion -> [(SignExpansion, FSE)] -> Maybe (Ordinal, SignExpansion)
detectFixedPointSE se res =
  case res of
    [(se', c)]
      | isPositive se && isOne c && se == se' ->
          let o = detectVebOrder se'
           in let (vebArgSE -> p', _) = parseVeb1 True o se
               in Just (o, p')
    _ -> Nothing

combineToConway :: [(SignExpansion, FSE)] -> Conway Dyadic
combineToConway =
  sum . map (\(pse, cse) -> parseToConway pse `mono` parseDyadicSE cse)

parseToUnreduced :: SignExpansion -> [(SignExpansion, FSE)]
parseToUnreduced = unreduceReduced . parseToReduced

unreduceReduced :: [(Reduced SignExpansion, FSE)] -> [(SignExpansion, FSE)]
unreduceReduced = uncurry zip . (first unreduce' . unzip)

parseToReduced :: SignExpansion -> [(Reduced SignExpansion, FSE)]
parseToReduced = fst . finalIteration parseToReducedStep . ([],)

-- | The results are in ascending order of
parseToReducedStep ::
  ([(Reduced SignExpansion, FSE)], SignExpansion) -> Maybe ([(Reduced SignExpansion, FSE)], SignExpansion)
parseToReducedStep (prevs, se)
  | Seq.null se = Nothing
  | otherwise = Just (prevs ++ [(Reduced po, cse)], se')
  where
    po = toExponentSE o pse
    (ParseVeb {vebOrder = o, vebArgSE = pse, coeffSE = cse}, se') = parseMono se

toExponentSE :: Ordinal -> SignExpansion -> SignExpansion
toExponentSE o pse = if isZero o then pse else veb1SE o pse

toExponent :: (One a, OrdZero a) => Ordinal -> Conway a -> Conway a
toExponent vo p = if isZero vo then p else veb1 vo p

-- * Parsing monomials

lookVebMono :: (ParsableSeq se Ordinal Bool) => se -> Maybe ((Ordinal, Natural), Bool)
lookVebMono se = do
  (b, m) <- lookahead se
  ((v, c), _) <- leadingView m
  return ((unMono1 v, c), b)

-- * Parsing monomials

-- TODO change detected `vo`:
-- Counterexample: w^[eps0 - 1] = [+^eps0 -^(w^(eps0 + 1))]
-- Calling parseVeb1 1 causes the parsing to break into
--    [+^eps0] [-^(w^(eps0 + 1))]
-- which makes the result
--    w^eps0 - w^(eps0 + 1), failing the unreduce process
-- Backtracking and calling parseVeb1 0 is required to fix it
parseMono :: SignExpansion -> (ParseVeb SignExpansion FSE, SignExpansion)
parseMono se = maybe (emptyParseVeb, se) parse $ lookahead se
  where
    parse (plus, leadingView -> Just _) = (`runSEP` se) $ do
      res0@ParseVeb {vebArgSE = pm1} <- sep $ parseMono1 plus
      let vo = detectVebOrder pm1
      let res = if isZero vo then res0 else fst $ parseVeb1 True vo pm1
      (didBacktrack, rs) <- sep $ parseRealSuffix res plus
      return res {coeffSE = rs, coeffDidBacktrack = didBacktrack}
    parse r = error $ "parseMono: not possible: " ++ show r

-- | Given @p@ of @mono p c@, detect if @p = veb o p' c@ where @p /= p@ and returns the @o@.
-- @o@ can be zero if no solutions found.
detectVebOrder :: SignExpansion -> Ordinal
detectVebOrder se
  | compareZero se /= GT = 0
  | otherwise =
      case os of
        [] -> 0
        o : _ -> o
  where
    -- candidates: +^veb o p  -^(w^(TERM))
    os = filter isSolution $ Set.toDescList $ Set.fromList $ detectVebOrderCandidates se
    isSolution :: Ordinal -> Bool
    isSolution o =
      case lookahead se of
        Nothing -> False
        Just (True, np) | np >= veb1 o 0 -> Seq.null rest && se' /= se
        Just _ -> False
      where
        (vebArgSE -> se', rest) = parseVeb1 True o se

detectVebOrderCandidates :: SignExpansion -> [Ordinal]
detectVebOrderCandidates (SE.toList -> xs) =
  directVebOrders ++ concatMap (vebOrdersFromMinusPart 2) minuses
  where
    directVebOrders = [o | (_, veb1PowView -> Just (VebMono o _)) <- xs]
    minuses = [t | (False, t) <- xs]

vebOrdersFromMinusPart :: Int -> Ordinal -> [Ordinal]
vebOrdersFromMinusPart 0 _ = []
vebOrdersFromMinusPart depth (termsList -> ts) =
  concat
    [ [o', p'] ++ subTerms p' ++ vebOrdersFromMinusPart depth' p'
    | (VebMono o' p', _) <- ts
    ]
  where
    depth' = depth - 1
    subTerms :: Ordinal -> [Ordinal]
    subTerms (ascTermsList -> ts') =
      filter isPositive $
        [ fromTermsList $ take i ts'
        | i <- [1 .. n]
        ]
      where
        n = Prelude.length ts'

finalIteration :: (a -> Maybe a) -> a -> a
finalIteration f = loop where loop x = maybe x loop $ f x

mkSEParser ::
  (ParsableSeq se Ordinal Bool) =>
  (st -> (Ordinal, Natural) -> Bool -> Maybe (Ordinal, st)) ->
  st ->
  se ->
  (st, se)
mkSEParser f st0 se0 = finalIteration parseStep (st0, se0)
  where
    parseStep (st, se) =
      lookVebMono se >>= \(t, s) -> do
        (toConsume, st') <- f st t s
        se' <- consume se (s, toConsume)
        return (st', se')

veb1PowView :: Ordinal -> Maybe (VebMono Natural)
-- w^(veb o p 1) . 1 = veb1 o p
veb1PowView (leadingView -> Just ((vm, isOne -> True), isZero -> True)) = Just vm
veb1PowView _ = Nothing

parseMono1 :: Bool -> SignExpansion -> (ParseVeb SignExpansion FSE, SignExpansion)
parseMono1 plus = parseBody . parseInitialPlus
  where
    parseInitialPlus se =
      case consume se (plus, 1) of
        Nothing -> error $ "parseMono1: cannot consume initial plus: " ++ show (se, (plus, 1 :: Ordinal))
        Just se' -> se'
    parseBody =
      mkSEParser
        ( \res0@ParseVeb {nPlusArg = nPlus, vebArgSE = se'} (p, c) s ->
            if s == plus
              then do
                (GT, d) <- Just $ ordSymDiff p nPlus
                Just (mono1 p, res0 {nPlusArg = nPlus `ordAdd` d, vebArgSE = se' <> replicate d True})
              else do
                let unit = nPlus `ordAdd` 1
                guard $ p >= unit
                let mpc = mono p c
                let (q, _) = ordDivRem mpc $ mono1 unit
                guard $ not $ isZero q
                Just (mpc, res0 {vebArgSE = se' <> replicate q False})
        )
        (emptyParseVeb {vebOrder = 0} :: ParseVeb SignExpansion FSE)

parseVeb1 :: Bool -> Ordinal -> SignExpansion -> (ParseVeb SignExpansion FSE, SignExpansion)
parseVeb1 plus 0 = parseMono1 plus
parseVeb1 plus o = parseBody . parseInitialPlus
  where
    v1 = veb1 o
    parseInitialPlus se =
      case consume se (plus, veb1 o 0) of
        Nothing -> error $ "parseVeb1: cannot consume initial plus: " ++ show (plus, veb1 o 0 :: Ordinal, se)
        Just se' -> se'
    parseBody =
      mkSEParser
        ( \res0@ParseVeb {nPlusArg = nPlus, vebArgSE = se'} (p, c) s ->
            if s == plus
              then do
                (VebMono o'@((>= o) -> True) p0) <- veb1PowView p
                -- If o' > o: use fixed point rule: veb1 o' p0 == veb1 o (veb1 o' p0)
                let p' = if o' == o then p0 else veb1 o' p0
                (GT, d) <- Just $ ordSymDiff p' nPlus
                Just (v1 p', res0 {nPlusArg = nPlus `ordAdd` d, vebArgSE = se' <> replicate d True})
              else do
                let unit = v1 nPlus `ordPow` mono1 o
                let mpc = mono p c
                let (q, _) = ordDivRem mpc unit
                guard $ not $ isZero q
                Just (mpc, res0 {vebArgSE = se' <> replicate q False})
        )
        (emptyParseVeb {vebOrder = o} :: ParseVeb SignExpansion FSE)

parseRealSuffix :: ParseVeb SignExpansion FSE -> Bool -> SignExpansion -> ((Bool, FSE), SignExpansion)
parseRealSuffix (ParseVeb {vebOrder = vo, vebArgSE = va, nPlusArg = nPlusA}) plus se
  | shouldBacktrack = ((True, SD.omitLast fse), se'')
  | otherwise = ((False, fse), se')
  where
    nPlus = toExponent vo nPlusA
    se'' = replicate (mono1 nPlus) (SD.lastSign fse) <> se'
    nLeadingPlus = SE.countSigns True $ toExponentSE vo va
    shouldBacktrack =
      case lookahead se' of
        Nothing -> False
        -- the next segment is treated as w^(+^p1 & ...) and p1 has more leading pluses than nLeadingPlus:
        -- the next term won't unreduce properly
        Just (_, leadingView -> Just ((VebMono o p, _), _)) -> toExponent o p >= nLeadingPlus
        Just _ -> False

    (fse, se') =
      mkSEParser
        ( \fse' (p, c) s ->
            if p /= nPlus
              then Nothing
              else
                Just (mono p c, fse' <> replicate c s)
        )
        (replicate 1 plus)
        se
