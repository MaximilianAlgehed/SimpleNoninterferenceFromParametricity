{-# LANGUAGE MultiParamTypeClasses
           , PolyKinds
           , KindSignatures
           , ScopedTypeVariables
           , FlexibleInstances
           , TypeFamilies
#-}
module Classes where

import Data.Proxy
import Control.DeepSeq

import DCC 

class CanFlowTo (flow :: lattice -> lattice -> *) (low :: lattice) (high :: lattice) where
  evidence :: Proxy flow -> Proxy low -> Proxy high -> flow low high

class Secure (flow :: lattice -> lattice -> *) (l :: lattice) a where
  proof :: Proxy flow -> Proxy l -> Proxy a -> Protected flow l a

instance (Secure f l a, Secure f l b) => Secure f l (a, b) where
  proof f l p = protect_x (proof f l Proxy) (proof f l Proxy)

instance Secure f l b => Secure f l (a -> b) where
  proof f l p = protect_fun (proof f l Proxy)

instance (NFData (f l h), CanFlowTo f l h) => Secure f l (T f h a) where
  proof f l p = protect_T (evidence f l Proxy)

instance Secure f l a => Secure f l (T f l' a) where
  proof f l p = protect_T' (proof f l Proxy)

mu' :: Secure f l a => T f l a -> a
mu' = mu (proof Proxy Proxy Proxy)
