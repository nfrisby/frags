{-# LANGUAGE UndecidableInstances #-}

module FragTest25 (
  module FragTest,
  module FragTest25,
  ) where

import GHC.Generics

import FragTest

type family SumFrag (rep :: k -> *) :: Frag (k -> *) where
  SumFrag V1 = 'Nil
  SumFrag (M1 i c f) = 'Nil :+ M1 i c f
  SumFrag (l :+: M1 i c f) = SumFrag l :+ M1 i c f
  SumFrag (l :+: (l2 :+: r2)) = SumFrag ((l :+: l2) :+: r2)

pSumFrag :: Proxy rep -> Proxy (SumFrag rep)
pSumFrag _ = Proxy

class C l where
  method :: Proxy l -> ()
