module IUTPproto where

import Data.Tuple(swap)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

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

-- Section 6 Strict and McCarthy logic for undefinedness

data XmplSig
  = XSigNum  Int              -- 0,1,2,...
  | XSigVar  String           -- x,y,a,b
  | XSigDiv  XmplSig XmplSig  -- x / y
  | XSigGT   XmplSig XmplSig  -- x > y
  | XSigNE   XmplSig XmplSig  -- a /= b
  | XSigNot  XmplSig          -- !a
  | XSigAnd  XmplSig XmplSig  -- a /\ b
  | XSigOr   XmplSig XmplSig  -- a \/ b
  -- | XSigImpl XmplSig XmplSig  -- a ==> b
  deriving (Eq,Ord)

instance Show XmplSig where
  show (XSigNum n)  =  show n
  show (XSigVar v)  =  v
  show (XSigDiv xs1 xs2) =  show xs1 ++ "/" ++ show xs2
  show (XSigGT xs1 xs2)  =  "("++show xs1++" > "++show xs2++")"
  show (XSigNE xs1 xs2)  =  "("++show xs1++" /= "++show xs2++")"
  show (XSigNot xs)  =  "!("++show xs++")"
  show (XSigAnd xs1 xs2)  =  "("++show xs1++" /\\ "++show xs2++")"
  show (XSigOr xs1 xs2)  =  "("++show xs1++" \\/ "++show xs2++")"
  -- show (XSigImpl xs1 xs2)  =  "("++show xs1++" ==> "++show xs2++")"

type XmplSent = XmplSig -- sentence functor is the identity functor !?

lit0 = XSigNum 0 ; lit1 = XSigNum 1
varx = XSigVar "x" ; vary = XSigVar "y"
assertA = XSigGT (XSigDiv varx vary ) lit1
assertG = XSigNE vary lit0
bothAG = XSigAnd assertA assertG
bothGA = XSigAnd assertG assertA



data TruthValues 
  = T | F | U -- this may be extended....
  deriving (Eq,Ord,Show,Read)

threeV = [T,F,U]

strictD = [T]
mcCarthyD = [T]

-- Basic Propositions

strictNot T = F ; strictNot F = T ; strictNot U = U
mcCarthyNot = strictNot

strictAnd U _ = U
strictAnd _ U = U
strictAnd T T = T
strictAnd _ _ = F

mcCarthyAnd F _ = F
mcCarthyAnd T b = b
mcCarthyAnd U _ = U

strictOr U _ = U
strictOr _ U = U
strictOr F F = F
strictOr _ _ = T

mcCarthyOr T _ = T
mcCarthyOr F b = b
mcCarthyOr U _ = U

-- Implication
-- we allow for other possible truth-value types,  not just TruthValues
mkImplication :: (tv -> tv) -> (tv -> tv -> tv) -> tv -> tv -> tv
mkImplication negation disjunction a b = (negation a) `disjunction` b

strictImpl = mkImplication strictNot strictOr

mcCarthyImpl = mkImplication mcCarthyNot mcCarthyOr

data XmplLogic  
  = Logic { lnot :: TruthValues -> TruthValues
          , land, lor, impl :: TruthValues -> TruthValues -> TruthValues
          }
mkLogic not and or = Logic not and or $ mkImplication not or


strictLogic    =  mkLogic strictNot   strictAnd   strictOr
mcCarthyLogic  =  mkLogic mcCarthyNot mcCarthyAnd mcCarthyOr

-- Models

type XmplModel = Map String Int

model42, model10 :: XmplModel
model42 = M.fromList [("x",4),("y",2)]
model10 = M.fromList [("x",1),("y",0)]

data XpmlDomain 
  = XDomNum Int | XDomTruth TruthValues
  deriving (Eq,Ord,Show)


-- Evaluation
-- Here we assume things are well-typed!
-- Also that the model is complete enough
-- however we can have failed evaluations in division (x/0)
eval :: XmplLogic -> XmplModel -> XmplSent -> Maybe XpmlDomain
eval logic model (XSigNum n) = return $ XDomNum n
eval logic model (XSigVar v) = do -- assumes v in model !!!!
  n <-  M.lookup v model
  return $ XDomNum n
eval logic model (XSigDiv xs1 xs2) = do -- assumes xs1,xs2 are "total" numbers
  (XDomNum n1) <- eval logic model xs1
  (XDomNum n2) <- eval logic model xs2
  if n2 == 0 then fail "divide by zero"
             else return $ XDomNum (n1 `div` 2)
eval logic model pred = return $ XDomTruth $ evalPred logic model pred

-- here we catch any undefinedess, and return U if it occurs
evalPred :: XmplLogic -> XmplModel -> XmplSent -> TruthValues
evalPred logic model (XSigGT xs1 xs2) = expreval logic model (>) xs1 xs2
evalPred logic model (XSigNE xs1 xs2) = expreval logic model (/=) xs1 xs2
evalPred logic model (XSigNot xs)
 = case eval logic model xs of
     Nothing             ->  U
     Just (XDomTruth b)  ->  (lnot logic) b
evalPred logic model (XSigAnd xs1 xs2)
  = predeval logic model (land logic) xs1 xs2
evalPred logic model (XSigOr xs1 xs2)  
  = predeval logic model (lor logic) xs1 xs2
evalPred logic model pred = U

expreval logic model rel xs1 xs2
  = case eval logic model xs1 of
      Nothing           -> U
      Just (XDomNum n1) ->
        case eval logic model xs2 of
          Nothing           -> U
          Just (XDomNum n2) -> if n1 `rel` n2 then T else F

predeval logic model lop xs1 xs2
  = case eval logic model xs1 of
      Nothing           -> U
      Just (XDomTruth b1) ->
        case eval logic model xs2 of
          Nothing           -> U
          Just (XDomTruth b2) -> b1 `lop` b2

