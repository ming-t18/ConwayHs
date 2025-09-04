{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Conway.SignExpansion.Parser
  ( SEParser (..),
    sep,
    runSEP,
    lookVebMono,
    lookVebMono1,
    parseMono,
    parseMono1,
  )
where

import Control.Monad.State
import Data.Conway.Conway
import Data.Conway.OrdinalArith (ordAdd, ordDivRem, ordSymDiff, unMono1)
import Data.Conway.Seq.Types
import Data.Conway.SignExpansion.Reduce (Reduced)
import Data.Conway.Typeclasses ()
import Prelude hiding (replicate)

-- * Parser monad

newtype SEParser se a = SEP {getSEParser :: State se a}
  deriving (Functor, Applicative, Monad, MonadState se)

sep :: (se -> (a, se)) -> SEParser se a
sep = SEP . state

runSEP :: SEParser se a -> se -> (a, se)
runSEP = runState . getSEParser

-- * Parsing @Conway@

parseReduced ::
  (ParsableSeq se Ordinal Bool, RunLengthSeq pse Ordinal Bool, RunLengthSeq cse Natural Bool) =>
  se -> ([((Ordinal, Reduced pse), cse)], se)
parseReduced _ = error "TODO implement this"

-- * Parsing monomials

lookVebMono1 :: (ParsableSeq se Ordinal Bool) => se -> Maybe (Ordinal, Bool)
lookVebMono1 se = do
  (b, m) <- lookahead se
  ((v, _), _) <- leadingView m
  return (unMono1 v, b)

lookVebMono :: (ParsableSeq se Ordinal Bool) => se -> Maybe ((Ordinal, Natural), Bool)
lookVebMono se = do
  (b, m) <- lookahead se
  ((v, c), _) <- leadingView m
  return ((unMono1 v, c), b)

-- * Parsing monomials

parseMono :: (ParsableSeq se Ordinal Bool, RunLengthSeq pse Ordinal Bool, RunLengthSeq cse Natural Bool) => se -> (((Ordinal, pse), cse), se)
parseMono se = maybe emptyResult parse $ lookahead se
  where
    emptyResult = (((0, mempty), mempty), se)
    parse (plus, _) = (`runSEP` se) $ do
      (nPlus, se') <- sep $ parseMono1 plus
      rs <- sep $ parseRealSuffix nPlus
      return ((nPlus, se'), replicate 1 plus <> rs)

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

parseMono1 :: (ParsableSeq se Ordinal Bool, RunLengthSeq pse Ordinal Bool) => Bool -> se -> ((Ordinal, pse), se)
parseMono1 plus0 = parseBody . parseInitialPlus
  where
    parseInitialPlus se =
      case consume se (plus0, 1) of
        Nothing -> error "parseMono1: cannot consume initial plus"
        Just se' -> se'

    parseBody =
      mkSEParser
        ( \plus (nPlus, se') (p, c) s ->
            if s == plus
              then case ordSymDiff p nPlus of
                (GT, d) -> Just (mono1 p, (nPlus `ordAdd` d, se' <> replicate d True))
                _ -> Nothing
              else
                let b1 = nPlus `ordAdd` 1
                 in if p < b1
                      then Nothing
                      else
                        let (q, _) = ordDivRem (mono p c) (mono1 b1)
                         in Just (mono p c, (nPlus, se' <> replicate q False))
        )
        (0, mempty)
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
