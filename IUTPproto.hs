module IUTPproto where

import Data.Tuple(swap)
import Data.Set (Set)
import qualified Data.Set as S

data Category obj
  = C { objects :: Set obj
      , morphisms :: Set (obj,obj) }
-- morphisms should be minimal? maximal?

apply :: Eq obj => Set (obj,obj) -> obj -> obj
apply m o 
  = search o $ S.toList m
  where
    search o [] = o -- always an identity arrow
    search o ((d,r):rest)
      | o == d  =  r
      | otherwise  =  search o rest

data Fun dom rng -- Functor defined in Prelude
  = F { objf :: Set (dom,rng)
      , arrf :: Set ((dom,dom),(rng,rng)) }

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

iSen :: Eq obj => Institution obj obj model -> obj -> obj
iSen inst sig = apply (objf (sentencef inst)) sig

sat :: (Ord sent, Ord model) 
    => Institution sig sent model -> model -> sent -> Bool
sat inst modobj sentobj
  = (modobj,sentobj) `S.member` satrel inst

type Signature = Set String

type Sentence = [String] 
