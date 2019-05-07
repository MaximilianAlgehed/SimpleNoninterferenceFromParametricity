{-# LANGUAGE GADTs
           , KindSignatures
           , PolyKinds
           , DataKinds
#-}
module DCC (T, eta, mu, Protected, protect_T, protect_T', protect_x, protect_fun) where

import Control.DeepSeq

data T (f :: lattice -> lattice -> *) (l :: lattice) (a :: *) = T a deriving Show {- Leaky instance -}

data Protected :: (l -> l -> *) -> l -> * -> * where
  Proof :: Protected f l a

eta :: a -> T f l a
eta = T

mu :: Protected f l a -> T f l a -> a
mu Proof (T a) = a 

protect_T :: NFData (f l l') => f l l' -> Protected f l (T f l' a)
protect_T f = f `deepseq` Proof

protect_T' :: Protected f l a -> Protected f l (T f l' a)
protect_T' Proof = Proof

protect_x :: Protected f l a -> Protected f l b -> Protected f l (a, b)
protect_x Proof Proof = Proof 

protect_fun :: Protected f l b -> Protected f l (a -> b)
protect_fun Proof = Proof
