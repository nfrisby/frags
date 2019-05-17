{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import FragTest_SmallProdSig

main :: IO ()
main = pure ()

-----

-- this once caught a bug that
-- reduction of FragEQ a q when the multiplicity table has a corresponding singleton interval
-- did not trigger setM

ret :: forall a p f. (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod (p :+ a) f -> Prod p f
ret = go (Proxy @p) MkFragRep
  where
  go :: forall g b q proxy. proxy q -> FragRep (q :+ b) b -> Prod (q :+ b) g -> Prod q g
  go q frep@MkFragRep tip = case tip of
    MkCons tip' x -> case axiom_minimum2 q (proofProd tip) frep x of
      Left Refl -> (tip')
      Right (frep_down,still_min) -> let
        inner = go (proxy2 q x) frep_down tip'
        in
        (case (proofProd inner,still_min) of (Refl,Refl) -> inner `ext` x)
    _ -> error "https://gitlab.haskell.org/ghc/ghc/issues/16639"
