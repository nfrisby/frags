{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror #-}

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Data.Frag.Plugin:trace #-}

-- {-# OPTIONS_GHC -fprint-explicit-kinds #-}
-- {-# OPTIONS_GHC -dppr-debug -dsuppress-all #-}
-- {-# OPTIONS_GHC -ddump-tc-trace #-}

module Test where

import TestDSL

eqs :: Proxy (x :: k) -> Proxy (y :: k) -> ()
eqs px py =
    [   pNil .+ px   ,   pNil .+ px .+ px .- px   ,   pNil .+ px .- px .+ px   ,   pNil .- px .+ px .+ px   ]
  `seq`
    [   pNil .+ px .+ py   ,   pNil .+ py .+ px   ]
  `seq`
    [   pNil .+ px .- py   ,   pNil .- py .+ px   ]
  `seq`
    [   pNil .- px .+ py   ,   pNil .+ py .- px   ]
  `seq`
    [   pNil .- px .- py   ,   pNil .- py .- px   ]
  `seq`
    [   pNil   ,   pNil .+ px .- px   ,   pNil .+ py .- py   ]
  `seq`
    ()

preds :: ()
preds =
    want (pKnownFragCard (pNil .+ p1))
  `seq`
    want (pSetFrag (pNil .+ p2))
  `seq`
    ()

infer1 :: ('() ~ SetFrag p,FragEQ 1 p ~ ('Nil :+ '() :- '() :+ '())) => Proxy p -> ()
infer1 pp =
    want (pSetFrag (pp .- p1))
  `seq`
    want (pSetFrag (pFragEQ p1 (pNil .+ p2)))
  `seq`
    ()

infer2 :: KnownFragCard (FragEQ a ('Nil :+ b :+ a)) => Proxy a -> Proxy b -> ()
infer2 pa pb =
    want (pKnownFragCard $ pFragEQ pa $ pNil .+ pb)
  `seq`
    ()

main :: IO ()
main = do
  print $ fragCard (Proxy :: Proxy (FragLT 1 ('Nil :+ 1 :+ 2)))
  print $ fragCard (Proxy :: Proxy (FragLT 2 ('Nil :+ 1 :+ 2)))
  print $ fragCard (Proxy :: Proxy (FragLT 1 ('Nil :+ 2 :+ 1)))
  print $ fragCard (Proxy :: Proxy (FragLT 2 ('Nil :+ 2 :+ 1)))

test :: proxy a -> proxy a1 -> q :~: (p1 :+ a1) -> FragLT a (p1 :+ a1) :~: 'Nil -> FragLT a q :~: 'Nil
test _ _ Refl Refl = Refl
