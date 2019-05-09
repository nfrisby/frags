{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

test :: ()   -- once triggered a bug in Frag.interpret
test = [ pNil , pFragNE pChar (pFragNE pBool (pNil .- pBool)) ]
  `seq`
  ()

main :: IO ()
main = pure ()

{-
test ::   -- once triggered overly aggressive Equivalence.transferred
  TIP fr (Op z) -> TIS fr Identity -> z
test tos = \case
   MkTIS MkFragRep x -> let Op f = prj tos in f x {- Identity a instead of a! -}
-}

{-
test ::   -- once triggered overly conservative Equivalence.transferred
  (SetFrag fr ~ '()) => TIP fr (Op z) -> TIS fr Identity -> z
test = \tos (MkTIS MkFragRep x) -> prj tos `getOp` runIdentity x
-}
