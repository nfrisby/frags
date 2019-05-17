{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import FragTest_SmallProdSig

main :: IO ()
main = pure ()

-----

ret :: forall a p f. (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod (p :+ a) f -> (Prod p f,f a)
ret = go (Proxy @p) MkFragRep

go :: forall b g q proxy. proxy q -> FragRep (q :+ b) b -> Prod (q :+ b) g -> (Prod q g,g b)
go q frep@MkFragRep tip = case tip of
  MkCons tip' x -> case axiom_minimum2 q (proofProd tip) frep x of
    Left Refl -> (tip',x)
    Right (frep_down,still_min) -> let
      (inner,fa) = go (proxy2 q x) frep_down tip'
      in
      (case (proofProd inner,still_min) of (Refl,Refl) -> inner `ext` x,fa)
  _ -> error "https://gitlab.haskell.org/ghc/ghc/issues/16639"
