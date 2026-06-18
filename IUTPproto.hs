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
  = Fun { objf :: Set (dom,rng)
      , arrf :: Set ((dom,dom),(rng,rng)) }

apply :: Eq dom => Set (dom,mrg) -> dom -> mrg
apply f x 
  = search x $ S.toList f
  where
    search x [] = error "undefined"
    search x ((d,r):rest)
      | x == d  =  r
      | otherwise  =  search x rest

data Institution sig sentence model
  = I { category :: Category sig
      , sentencef :: Fun sig sentence
      , modelf :: Fun sig model -- use comorphisms, rather than morphisms
      , satrel :: Set (model,sentence)
      -- derived:
      , comorphisms :: Set (sig,sig)
      }

iDerive :: Ord sig => Institution sig set cat -> Institution sig set cat
iDerive inst = inst{ comorphisms = S.map swap (morphisms (category inst))}

iSen :: Eq sig => Institution sig sentence model -> sig -> sentence
iSen inst sig = apply (objf (sentencef inst)) sig

iMod :: Eq sig => Institution sig sentence model -> sig -> model
iMod inst sig = apply (objf (modelf inst)) sig

sat :: (Ord sentence, Ord model) 
    => Institution sig sentence model -> model -> sentence -> Bool
sat inst modobj sentobj
  = (modobj,sentobj) `S.member` satrel inst

-- sig is a given signature
-- this does not use morphisms, arrf, or comorphisms
-- it does use objf, sentencef, modelf, satrel
satcond :: (Ord sentence, Ord model, Eq sig) 
        => Institution sig sentence model -> sig -> sentence -> model -> Bool
satcond inst sig sentence model' 
  = let 
      m'sat = sat inst model' (iSen inst sig)
      modm'sat = sat inst (iMod inst sig) sentence
    in m'sat == modm'sat

-- examples

data TruthValues 
  = T | F | U -- this may be extended....
  deriving (Eq,Show,Read)

threeV = [T,F,U]

strictD = [T]
mcCarthyD = [T]

strictAnd U _ = U
strictAnd _ U = U
strictAnd T T = T
strictAnd _ _ = F

mcCarthyAnd F _ = F
mcCarthyAnd T b = b
mcCarthyAnd U _ = U
