{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Conway.SignExpansion.Parser
  ( ParseVeb1 (..),
    lookVebMono,
    parseMono,
    parseVeb1,
    parseToConway,
    combineToConway,
    unreduceReduced,
  )
where

import Control.Arrow (first)
import Control.Monad.State
import Data.Conway.Conway
import Data.Conway.Dyadic (Dyadic)
import Data.Conway.OrdinalArith (ordAdd, ordDivRem, ordPow, ordSymDiff, unMono1)
import Data.Conway.Seq.Types as Seq
import Data.Conway.SignExpansion.Dyadic (FSE, parseDyadicSE)
import Data.Conway.SignExpansion.Reduce (Reduced (..), unreduce')
import Data.Conway.SignExpansion.Types (SignExpansion)
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

data ParseVeb1 se cse
  = ParseVeb1
  { nPlusArg :: Ordinal,
    vebOrder :: Ordinal,
    vebArgSE :: se,
    coeffSE :: cse
  }
  deriving (Show)

emptyParseVeb1 :: (Zero se, Zero cse) => ParseVeb1 se cse
emptyParseVeb1 = (ParseVeb1 {nPlusArg = zero, vebOrder = zero, vebArgSE = zero, coeffSE = zero})

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

-- let (ParseVeb1 {nPlusArg = nPlus, vebOrder = o, vebArgSE = va, coeffSE = c}, se') = parseMono se
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

parseMono :: SignExpansion -> (ParseVeb1 SignExpansion FSE, SignExpansion)
parseMono se = maybe (emptyParseVeb1, se) parse $ lookahead se
  where
    parse (plus, leadingView -> Just ((VebMono vo _, _), _)) = (`runSEP` se) $ do
      res@ParseVeb1 {nPlusArg = nPlus} <- sep $ parseVeb1 plus vo
      let nPlus' = if isZero vo then nPlus else veb1 vo nPlus
      rs <- sep $ parseRealSuffix nPlus'
      return res {coeffSE = replicate 1 plus <> rs}
    parse _ = error "parseMono: not possible"

finalIteration :: (a -> Maybe a) -> a -> a
finalIteration f = loop where loop x = maybe x loop $ f x

mkSEParser ::
  (ParsableSeq se Ordinal Bool) =>
  (pl -> st -> (Ordinal, Natural) -> Bool -> Maybe (Ordinal, st)) ->
  st ->
  pl ->
  se ->
  (st, se)
mkSEParser f0 st0 plus se0 = finalIteration parseStep (st0, se0)
  where
    f = f0 plus
    parseStep (st, se) =
      lookVebMono se >>= \(t, s) -> do
        (toConsume, st') <- f st t s
        se' <- consume se (s, toConsume)
        return (st', se')

veb1PowView :: Ordinal -> VebMono Natural
-- w^(veb o p 1) . 1 = veb1 o p
veb1PowView (leadingView -> Just ((vm, isOne -> True), isZero -> True)) = vm
veb1PowView p = VebMono 0 p

parseVeb1 :: Bool -> Ordinal -> SignExpansion -> (ParseVeb1 SignExpansion FSE, SignExpansion)
parseVeb1 plus0 vebOrder0 = parseBody . parseInitialPlus
  where
    parseInitialPlus se =
      case consume se (plus0, if isZero vebOrder0 then 1 else veb1 vebOrder0 0) of
        Nothing -> error "parseMono1: cannot consume initial plus"
        Just se' -> se'
    parseBody =
      mkSEParser
        ( \plus ParseVeb1 {nPlusArg = nPlus, vebOrder = o, vebArgSE = se', coeffSE = cse} (p@(veb1PowView -> VebMono o' p'), c) s ->
            let v1 = veb1 o
             in if isZero o
                  then
                    -- Case 1, mono1: w^p.c
                    if s == plus
                      then case ordSymDiff p nPlus of
                        (GT, d) -> Just (mono1 p, ParseVeb1 {nPlusArg = nPlus `ordAdd` d, vebOrder = o, vebArgSE = se' <> replicate d True, coeffSE = cse})
                        _ -> Nothing
                      else
                        let unit = nPlus `ordAdd` 1
                            mpc = mono p c
                         in if p < unit
                              then Nothing
                              else
                                let (q, _) = ordDivRem mpc (mono1 unit)
                                 in if isZero q then Nothing else Just (mpc, ParseVeb1 {nPlusArg = nPlus, vebOrder = o, vebArgSE = se' <> replicate q False, coeffSE = cse})
                  else
                    -- Case 2, veb1 o: w^(o `veb1` va').c = veb o va' c
                    if s == plus
                      then
                        if o' == o
                          then case ordSymDiff p' nPlus of
                            (GT, d) -> Just (v1 p', ParseVeb1 {nPlusArg = nPlus `ordAdd` d, vebOrder = o, vebArgSE = se' <> replicate d True, coeffSE = cse})
                            _ -> Nothing
                          else
                            if o' > o
                              then
                                error "parseVeb1: plus-veb case: not possible"
                              else
                                Nothing
                      else
                        let unit = v1 nPlus `ordPow` mono1 o
                            mpc = mono p c
                            (q, _) = ordDivRem mpc unit
                         in if isZero q then Nothing else Just (mpc, ParseVeb1 {nPlusArg = nPlus, vebOrder = o, vebArgSE = se' <> replicate q False, coeffSE = cse})
        )
        (emptyParseVeb1 {vebOrder = vebOrder0} :: ParseVeb1 SignExpansion FSE)
        plus0

parseRealSuffix :: (ParsableSeq se Ordinal Bool, RunLengthSeq cse Natural Bool) => Ordinal -> se -> (cse, se)
parseRealSuffix nPlus =
  mkSEParser
    ( \_ se' (p, c) s ->
        if p /= nPlus
          then Nothing
          else
            Just (mono p c, se' <> replicate c s)
    )
    mempty
    ()
