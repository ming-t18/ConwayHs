module SignExpansion
  ( SignExpansion,
    (+++),
    empty,
    isEmpty,
    toList,
    fromList,
    length,
    negate,
    single,
    plus,
    minus,
    consSE,
    mono1SE,
    mono1SE',
    veb1SE,
    veb1SE',
    commonPrefix,
    takeCommonPrefix,
  )
where

import SignExpansion.Types
import SignExpansion.Veb
import Prelude hiding (length, negate)
