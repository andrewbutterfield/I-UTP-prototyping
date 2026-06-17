module IUTPproto where

import Data.Tuple(swap)
import Data.Set (Set)
import qualified Data.Set as S

data Category obj
  = C { objects :: Set obj
      , morphisms :: Set (obj,obj) }
-- morphisms should be minimal? maximal?

morph :: Eq obj => Set (obj,obj) -> obj -> obj
morph m o 
  = search o $ S.toList m
  where
    search o [] = o -- always an identity arrow
    search o ((d,r):rest)
      | o == d  =  r
      | otherwise  =  search o rest

data Fun dom rng -- Functor defined in Prelude
  = F { objf :: Set (dom,rng)
      , arrf :: Set ((dom,dom),(rng,rng)) }

apply :: Eq dom => Set (dom,mrg) -> dom -> mrg
apply f x 
  = search x $ S.toList f
  where
    search x [] = error ""
    search x ((d,r):rest)
      | x == d  =  r
      | otherwise  =  search x rest

data Institution sig sent model
  = I { category :: Category sig
      , sentencef :: Fun sig sent
      , modelf :: Fun sig model -- use comorphisms, rather than morphisms
      , satrel :: Set (model,sent)
      -- derived:
      , comorphisms :: Set (sig,sig)
      }

iDerive :: Ord sig => Institution sig set cat -> Institution sig set cat
iDerive inst = inst{ comorphisms = S.map swap (morphisms (category inst))}

iSen :: Eq sig => Institution sig sent model -> sig -> sent
iSen inst sig = apply (objf (sentencef inst)) sig

-- iMod :: Eq obj => Institution obj 

sat :: (Ord sent, Ord model) 
    => Institution sig sent model -> model -> sent -> Bool
sat inst modobj sentobj
  = (modobj,sentobj) `S.member` satrel inst

type Signature = Set String

type Sentence = [String] 
