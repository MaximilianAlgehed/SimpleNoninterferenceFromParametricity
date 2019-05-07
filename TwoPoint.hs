{-# LANGUAGE DataKinds
           , GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , FlexibleInstances
#-}
module TwoPoint (TwoPoint(..), TPFlow(..), Stp) where
import Classes
import Static

data TwoPoint where
  L :: TwoPoint
  H :: TwoPoint

data TPFlow :: TwoPoint -> TwoPoint -> * where
  Up   :: TPFlow L H
  Same :: TPFlow l l

type Stp = S TPFlow

instance CanFlowTo TPFlow l l where
  evidence _ _ _ = Same

instance CanFlowTo TPFlow L H where
  evidence _ _ _ = Up
