{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module FragTest_SmallProdSig (
  module FragTest,
  module FragTest_SmallProdSig,
  ) where

import FragTest

proofProd :: Prod fr f -> SetFrag fr :~: '()
proofProd = undefined

data Prod :: Frag k -> (k -> *) -> * where
  MkCons :: (FragLT a p ~ 'Nil,FragEQ a p ~ 'Nil) => !(Prod p f) -> f a -> Prod (p :+ a) f
  MkNil :: Prod 'Nil f

ext :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod p f -> f a -> Prod (p :+ a) f
ext = undefined

proxy2 :: proxyp p -> proxya a -> Proxy (q :- a)
proxy2 _ _ = Proxy

axiom_minimum_and_minus ::
    proxyp p
  ->
    proxya a
  ->
    proxyz z
  ->
    SetFrag (p :+ a) :~: '()
  ->
    FragEQ z (p :+ a) :~: ('Nil :+ '())
  ->
    FragLT z (p :+ a) :~: 'Nil
  ->
    FragRep (p :+ a) a
  ->
    Either
      (a :~: z)
      (FragRep (p :+ a :- z) a,FragLT z p :~: 'Nil)
axiom_minimum_and_minus _ = undefined
