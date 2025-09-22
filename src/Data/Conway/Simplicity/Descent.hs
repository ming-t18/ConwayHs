module Data.Conway.Simplicity.Descent (descend, descent, descentSeq) where

import Data.Conway.Conway
import qualified Data.Conway.Seq.InfList as I
import Data.Conway.SignExpansion.Dyadic (FiniteSignExpansion)
import Data.Conway.Simplicity.Completion (parentSeq)
import Data.Conway.Simplicity.Seq
import Data.Conway.Simplicity.Types (ConwaySeq (..), MonoSeq (..), Veb1Seq (..))
import Data.Conway.Typeclasses
import Data.List (unfoldr)

descend :: (OrdRing a, FiniteSignExpansion a) => Conway a -> Maybe (Conway a)
descend x =
  do
    s <- parentSeq x
    case s of
      Left pt -> Just pt
      Right s' ->
        let cs = conwaySeq s'
         in Just $ I.index cs $ decideIndex s'

decideIndex :: ConwaySeq a -> Natural
decideIndex (ConwaySeq {csTerm = t}) = decideIndexTerm t

decideIndexTerm :: MonoSeq a -> Natural
decideIndexTerm (Mono1Seq (Veb1ArgSeq _ a)) = decideIndex a
decideIndexTerm (Mono1Seq (Veb1OrderSeq o _)) = decideIndex o
decideIndexTerm (Mono1Seq (Veb1IterSeq _ Nothing)) = 3
decideIndexTerm (Mono1Seq (Veb1IterSeq _ _)) = 1
decideIndexTerm (MonoMultSeq _ True) = 1
decideIndexTerm (MonoMultSeq _ False) = 0

descent :: (OrdRing a, FiniteSignExpansion a) => Conway a -> [Conway a]
descent = unfoldr (fmap (\x -> (x, x)) . descend)

descentSeq :: (OrdRing a, FiniteSignExpansion a) => Conway a -> [(ParentSeq a, Conway a)]
descentSeq _ = error "TODO"

-- TODO minimum exponent constraint on the sequence: w^(-3.5) + [w^-w][i] starts at w^(-3.5) + [w^-4] by skipping terms
