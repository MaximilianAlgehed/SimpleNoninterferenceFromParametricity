{-# LANGUAGE DataKinds #-}
module TerminationLeaks where
import TwoPoint
import Static

value :: Stp H (Stp H Int, Stp L Bool)
value = eta (eta 42, eta False)

-- Non-termination leak in the lazy version of mu
leak :: Stp H a -> a
leak = mu proof 
  where
    proof = proof

nonTerminating :: (Stp H Int, Stp L Bool)
nonTerminating = leak value

-- Partly valid proofs
proof :: Safe TPFlow H (Stp H Int, Stp L Bool)
proof = Pair (Safe Same) loop
  where
    loop = loop

partlyTerminating :: (Stp H Int, Stp L Bool)
partlyTerminating = mu proof value
