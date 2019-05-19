{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module FragTest (
  module Data.Frag,
  module Data.Proxy,
  module Data.Type.Equality,
  module GHC.TypeLits,
  module FragTest,
  ) where

import GHC.TypeLits (Nat,Symbol)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))

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

infixl 7 .=
(.=) :: Proxy k -> Proxy v -> Proxy (k := v)
(.=) _ _ = Proxy

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
pSymbol :: Proxy Symbol; pSymbol = Proxy
pStar :: Proxy *; pStar = Proxy
pKindOf :: Proxy (p :: k) -> Proxy k
pKindOf _ = Proxy

-----

data Is1or2 :: Frag Nat -> * where
  Is1 :: Is1or2 ('Nil :+ 1)
  Is2 :: Is1or2 ('Nil :+ 2)

-----

class IsEq l r
instance IsEq a a

isEq :: Proxy l -> Proxy r -> Proxy (IsEq l r)
isEq _ _ = Proxy

popK ::
    (SetFrag p ~ '(),SetFrag (DomFrag p) ~ '(),FragEQ k (DomFrag p) ~ 'Nil)
  =>
    Proxy k -> Proxy (p :+ k := v) -> Proxy v
popK _ _ = Proxy
