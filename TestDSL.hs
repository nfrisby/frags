{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module TestDSL (
  module Data.Frag,
  module Data.Proxy,
  module GHC.TypeLits,
  module TestDSL,
  ) where

import GHC.TypeLits (Nat)
import Data.Proxy (Proxy(..))

import Data.Frag

pFrag :: Proxy k -> Proxy (Frag k)
pFrag _ = Proxy

pNil :: Proxy 'Nil
pNil = Proxy

infixl 6 .+
(.+) :: Proxy p -> Proxy b -> Proxy (p :+ b)
(.+) _ _ = Proxy

infixl 6 .-
(.-) :: Proxy p -> Proxy b -> Proxy (p :- b)
(.-) _ _ = Proxy

-----

pFragCard ::  Proxy fr -> Proxy (FragCard fr)
pFragCard _ = Proxy

pFragEQ :: Proxy b -> Proxy fr -> Proxy (FragEQ b fr)
pFragEQ _ _ = Proxy

pFragNE :: Proxy b -> Proxy fr -> Proxy (FragNE b fr)
pFragNE _ _ = Proxy

pKnownFragCard :: Proxy fr -> Proxy (KnownFragCard fr)
pKnownFragCard _ = Proxy

pSetFrag :: Proxy fr -> Proxy ('() ~ SetFrag fr)
pSetFrag _ = Proxy

pMult :: Proxy b -> Proxy fr -> Proxy z -> Proxy (FragEQ b fr ~ z)
pMult _ _ _ = Proxy

want :: c => Proxy c -> ()
want _ = ()

give :: Proxy c -> (c => ()) -> ()
give _ _ = ()

-----

p1 :: Proxy 1; p1 = Proxy
p2 :: Proxy 2; p2 = Proxy
pA :: Proxy "A"; pA = Proxy
pB :: Proxy "B"; pB = Proxy

pBool :: Proxy Bool; pBool = Proxy
pChar :: Proxy Char; pChar = Proxy
pInt :: Proxy Int; pInt = Proxy

pU :: Proxy '(); pU = Proxy

pNat :: Proxy Nat; pNat = Proxy
pStar :: Proxy *; pStar = Proxy
pKindOf :: Proxy (p :: k) -> Proxy k
pKindOf _ = Proxy

-----

data Var_a k = forall (a :: k). Var_a (Proxy a)
data Var_b k = forall (b :: k). Var_b (Proxy b)
data Var_k kk = forall (k :: kk). Var_k (Proxy k)
data Var_p k = forall (p :: k). Var_p (Proxy p)
data Var_q k = forall (q :: k). Var_q (Proxy q)
data Var_x k = forall (x :: k). Var_x (Proxy x)
data Var_y k = forall (y :: k). Var_y (Proxy y)

nabla :: (x -> r) -> ()
nabla _ = ()

nablaAt :: Proxy k -> (f k -> r) -> ()
nablaAt _ _ = ()
