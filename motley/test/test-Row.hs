{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Main where

import Data.Functor.Identity (Identity(..))
import Data.Motley.Row
import Data.Proxy (Proxy(..))

main :: IO ()
main = do
  let
    foo :: Proxy "foo"
    foo = Proxy

    bar :: Proxy "bar"
    bar = Proxy
  let
    r1 = emp `ext` foo .= Identity True
    r2 = r1 `ext` bar .= Identity 'c'
  print $ unRecord r1
  print $ unRecord r2
  print $ unRecord $ rmv foo r2
  print $ unRecord $ rmv bar r2
  print $ prj foo r2
  print $ prj bar r2
