module Dynamic (D, eta, mu, Lattice) where

class Lattice l where
  bot :: l
  lub :: l -> l -> l

data D l a = D l a

dMap :: (a -> b) -> D l a -> D l b
dMap f (D l a) = D l (f a)

eta :: Lattice l =>  a -> D l a
eta = D bot

mu :: Lattice l => D l (D l a) -> D l a
mu (D l (D l' a)) = D (l `lub` l') a

{- After TCB -}

mu' :: Safe l a -> D l a -> a
mu' = ($)

type Safe l a = D l a -> a

safe_D :: Lattice l => Safe l (D l a) 
safe_D = mu

safe_X :: Safe l a -> Safe l b -> Safe l (a, b)
safe_X f g d = (f (dMap fst d), g (dMap snd d))

safe_Fun :: Safe l b -> Safe l (a -> b)
safe_Fun f d a = f (dMap ($a) d)

safe_Unit :: Safe l ()
safe_Unit d = ()
