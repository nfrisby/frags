{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall -Werror #-}

{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin -dcore-lint #-}
{-# OPTIONS_GHC -fplugin-opt Data.Frag.Plugin:trace #-}

-- {-# OPTIONS_GHC -ddump-tc-trace #-}
-- {-# OPTIONS_GHC -dppr-debug -dsuppress-all #-}

module Test where

import TestDSL

eqs :: ()
eqs = nabla $ \(Var_x px,Var_y py) ->
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

inferred_preds :: ()
inferred_preds = nablaAt (pFrag pNat) $ \(Var_p pp) ->
  give (pSetFrag pp) $ give (pMult p1 pp (pNil .+ pU)) $
    want (pSetFrag (pp .- p1))
  `seq`
    want (pSetFrag (pFragEQ p1 (pNil .+ p2)))
  `seq`
    ()
