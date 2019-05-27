{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import FragTest_SmallProdSig

main :: IO ()
main = pure ()

-----

-- this once caught a bug in the interval that (SetFrag (FragEQ a q :- '())) added to the multiplicity table

ret :: forall a p f. (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod (p :+ a) f -> (Prod p f,f a)
ret = go (Proxy @p) MkFragRep
  where
  go :: forall g b q proxy. proxy q -> FragRep (q :+ b) b -> Prod (q :+ b) g -> (Prod q g,g b)
  go q frep@MkFragRep tip = case tip of
    MkCons tip' x -> case axiom_minimum_and_minus q frep x (proofProd tip) Refl Refl frep of
      Left Refl -> (tip',x)
      Right (frep_down,still_min) -> let
        (inner,fa) = go (proxy2 q x) frep_down tip'
        in
        (case (proofProd inner,still_min) of (Refl,Refl) -> inner `ext` x,fa)
    _ -> error "https://gitlab.haskell.org/ghc/ghc/issues/16639"
