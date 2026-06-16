module IUTPproto where

import Data.Tuple(swap)
import Data.Set (Set)
import qualified Data.Set as S

data Category obj
  = C { objects :: Set obj
      , morphisms :: Set (obj,obj) }
-- morphisms should be minimal? maximal?

type Signature = Set String



newtype SET set = SET set -- the ultimate abstraction ;-)
newtype CAT cat = CAT cat

data Institution sig set cat
  = I { category :: Category sig
      , sentencef :: sig -> Category set
      , modelf :: sig -> CAT cat -- use comorphisms, rather than morphisms
      , satrel :: Set (CAT cat,SET set)
      -- derived:
      , comorphisms :: Set (sig,sig)
      }

iDerive :: Ord sig => Institution sig set cat -> Institution sig set cat
iDerive inst = inst{ comorphisms = S.map swap (morphisms (category inst))}

sat :: (Ord (CAT cat), Ord (SET set)) 
    => Institution sig set cat -> CAT cat -> SET set -> Bool
sat inst catobj setobj
  = (catobj,setobj) `S.member` satrel inst
