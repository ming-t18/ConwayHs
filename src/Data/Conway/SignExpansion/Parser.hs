{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Conway.SignExpansion.Parser
  ( ParseVeb (..),
    lookVebMono,
    parseMono,
    parseVeb1,
    parseToConway,
    combineToConway,
    unreduceReduced,
    detectVebOrder,
  )
where

import Control.Arrow (first)
import Control.Monad (guard)
import Control.Monad.State
import Data.Conway.Conway
import Data.Conway.Dyadic (Dyadic)
import Data.Conway.OrdinalArith (ordAdd, ordDivRem, ordPow, ordSymDiff, unMono1)
import Data.Conway.Seq.Types as Seq
import Data.Conway.SignExpansion.Dyadic (FSE, parseDyadicSE)
import Data.Conway.SignExpansion.Reduce (Reduced (..), unreduce')
import Data.Conway.SignExpansion.Types (SignExpansion)
import qualified Data.Conway.SignExpansion.Types as SE
import Data.Conway.Typeclasses (One (..), Zero (..))
import Data.Foldable (foldl')
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
    coeffSE :: cse
  }
  deriving (Show)

emptyParseVeb1 :: (Zero se, Zero cse) => ParseVeb se cse
emptyParseVeb1 = (ParseVeb {nPlusArg = zero, vebOrder = zero, vebArgSE = zero, coeffSE = zero})

-- * Parsing @Conway@

parseToConway :: SignExpansion -> Conway Dyadic
parseToConway = combineToConway . parseToUnreduced

combineToConway :: [(SignExpansion, FSE)] -> Conway Dyadic
combineToConway =
  foldl'
    ( \s (p, c) ->
        s + (mono1 (parseToConway p) * finite (parseDyadicSE c))
    )
    zero

unreduceReduced :: [(Reduced SignExpansion, cse)] -> [(SignExpansion, cse)]
unreduceReduced = uncurry zip . (first unreduce' . unzip)

parseToUnreduced :: SignExpansion -> [(SignExpansion, FSE)]
parseToUnreduced = fst . finalIteration parseToReducedStep . ([],)

-- | The results are in ascending order of
parseToReducedStep ::
  (RunLengthSeq cse Natural Bool) =>
  ([(SignExpansion, cse)], SignExpansion) -> Maybe ([(SignExpansion, cse)], SignExpansion)
parseToReducedStep (prevs, se)
  | Seq.null se = Nothing
  | otherwise =
      error "TODO implement this"

-- let (ParseVeb {nPlusArg = nPlus, vebOrder = o, vebArgSE = va, coeffSE = c}, se') = parseMono se
--     unreduce = unreduceStep (map fst prevs) . Reduced
--     po = if isZero o then va else veb1SE o va
--  in case unreduce po of
--       Just p -> Just (prevs ++ [(p, c)], se')
--       Nothing -> error "TODO"

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
parseMono se = maybe (emptyParseVeb1, se) parse $ lookahead se
  where
    parse (plus, leadingView -> Just _) = (`runSEP` se) $ do
      res0@ParseVeb {vebArgSE = pm1} <- sep $ parseMono1 plus
      let vo = detectVebOrder pm1
      let res@ParseVeb {nPlusArg = nPlus} =
            if isZero vo
              then res0
              else fst $ parseVeb1 True vo pm1
      let nPlus' = if isZero vo then nPlus else veb1 vo nPlus
      rs <- sep $ parseRealSuffix nPlus'
      return res {coeffSE = replicate 1 plus <> rs}
    parse r = error $ "parseMono: not possible: " ++ show r

-- | Given @p@ of @mono p c@, detect if @p = veb o p' c@ and returns the @o@
detectVebOrder :: SignExpansion -> Ordinal
detectVebOrder se@(SE.toList -> xs)
  | compareZero se /= GT = 0
  | otherwise =
      case os of
        [] -> 0
        o : _ -> o
  where
    os =
      [ o
      | (_, veb1PowView -> Just (VebMono o _)) <- xs,
        ( case lookahead se of
            Just (True, r) -> (r :: Ordinal) >= veb1 o 0
            _ -> False
        )
          && Seq.null (snd (parseVeb1 True o se))
      ]

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
        ( \ParseVeb {nPlusArg = nPlus, vebOrder = o, vebArgSE = se', coeffSE = cse} (p, c) s ->
            if s == plus
              then do
                (GT, d) <- Just $ ordSymDiff p nPlus
                Just (mono1 p, ParseVeb {nPlusArg = nPlus `ordAdd` d, vebOrder = o, vebArgSE = se' <> replicate d True, coeffSE = cse})
              else do
                let unit = nPlus `ordAdd` 1
                guard $ p >= unit
                let mpc = mono p c
                let (q, _) = ordDivRem mpc $ mono1 unit
                guard $ not $ isZero q
                Just (mpc, ParseVeb {nPlusArg = nPlus, vebOrder = o, vebArgSE = se' <> replicate q False, coeffSE = cse})
        )
        (emptyParseVeb1 {vebOrder = 0} :: ParseVeb SignExpansion FSE)

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
        ( \ParseVeb {nPlusArg = nPlus, vebArgSE = se', coeffSE = cse} (p, c) s ->
            if s == plus
              then do
                (VebMono o'@((>= o) -> True) p0) <- veb1PowView p
                -- If o' > o: use fixed point rule: veb1 o' p0 == veb1 o (veb1 o' p0)
                let p' = if o' == o then p0 else veb1 o' p0
                (GT, d) <- Just $ ordSymDiff p' nPlus
                Just (v1 p', ParseVeb {nPlusArg = nPlus `ordAdd` d, vebOrder = o, vebArgSE = se' <> replicate d True, coeffSE = cse})
              else do
                let unit = v1 nPlus `ordPow` mono1 o
                let mpc = mono p c
                let (q, _) = ordDivRem mpc unit
                guard $ not $ isZero q
                Just (mpc, ParseVeb {nPlusArg = nPlus, vebOrder = o, vebArgSE = se' <> replicate q False, coeffSE = cse})
        )
        (emptyParseVeb1 {vebOrder = o} :: ParseVeb SignExpansion FSE)

parseRealSuffix :: (ParsableSeq se Ordinal Bool, RunLengthSeq cse Natural Bool) => Ordinal -> se -> (cse, se)
parseRealSuffix nPlus =
  mkSEParser
    ( \se' (p, c) s ->
        if p /= nPlus
          then Nothing
          else
            Just (mono p c, se' <> replicate c s)
    )
    mempty
