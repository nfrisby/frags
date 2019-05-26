{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}

module AuxMTLState where

import Control.Monad.State
import Control.Lens (over)
import Control.Lens.Wrapped (Rewrapped,Wrapped)
import Data.Coerce (coerce)
import Data.Motley
import Data.Type.Equality
import GHC.Generics (Generic)

newtype A = MkA{getA :: Int}
  deriving (Generic,Show)
instance Wrapped A
instance Rewrapped A t

newtype B = MkB{getB :: [String]}
  deriving (Generic,Show)
instance Wrapped B
instance Rewrapped B t

modifyProd :: _ => _
modifyProd f = modify $ opticProd' `over` f

s0 = nil `ext` Identity (MkA 3) `ext` Identity (MkB [])
