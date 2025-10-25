module Data.Conway.Simplicity.OrdinalSeq
  ( OrdMonoSeq,
    ParentSeqOrd,
  )
where

import Data.Conway.Conway
import Data.Conway.Simplicity.Types

type OrdMonoSeq = MonoSeq Natural

type ParentSeqOrd = ParentSeq Natural