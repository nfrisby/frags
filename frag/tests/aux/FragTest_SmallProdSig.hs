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
