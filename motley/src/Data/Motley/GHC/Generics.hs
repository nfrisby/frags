{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}   -- :+:

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}

-- | This module converts the 'Rep' types arising from @-XDeriveGeneric@ to 'Sum' or 'Prod'.

module Data.Motley.GHC.Generics (
  ProdFrag,
  ProdRep(..),
  SumFrag,
  SumRep(..),
  ) where

import Data.Motley
import GHC.Generics

type family SumFrag (rep :: k -> *) :: Frag (k -> *) where
  SumFrag (M1 D c f) = SumFrag f
  SumFrag V1 = 'Nil
  SumFrag (M1 C c f) = 'Nil :+ M1 C c f
  SumFrag (l :+: M1 C c f) = SumFrag l :+ M1 C c f
  SumFrag (l :+: (l2 :+: r2)) = SumFrag ((l :+: l2) :+: r2)

class SumRep (rep :: k -> *) where
  toSum :: rep x -> Sum (SumFrag rep) (At x)
  fromSum :: Sum (SumFrag rep) (At x) -> rep x

instance SumRep f => SumRep (M1 D c f) where
  toSum = toSum . unM1
  fromSum = M1 . fromSum

instance SumRep V1 where
  toSum = \_ -> error "SumRep V1"
  fromSum = absurd "fromSum V1"

instance SumRep (M1 C c f) where
  toSum = toSingletonSum . MkAt
  fromSum = getAt . fromSingletonSum

instance (KnownFragCard (FragLT (M1 C c f) (SumFrag l)),FragEQ (M1 C c f) (SumFrag l) ~ 'Nil,SetFrag (SumFrag l) ~ '(),SumRep l) => SumRep (l :+: M1 C c f) where
  toSum = \case
    L1 x -> plusSum (toSum x) (Proxy :: Proxy rep)
    R1 x -> inj (MkAt x)
  fromSum = alt (L1 . fromSum) (R1 . getAt)

instance (SumRep ((l :+: l2) :+: r2)) => SumRep (l :+: (l2 :+: r2)) where
  toSum = toSum . \case
    L1 x -> L1 (L1 x)
    R1 (L1 x) -> L1 (R1 x)
    R1 (R1 x) -> R1 x
  fromSum = (. fromSum) $ \case
    L1 (L1 x) -> L1 x
    L1 (R1 x) -> R1 (L1 x)
    R1 x -> R1 (R1 x)

-----

type family ProdFrag (rep :: k -> *) :: Frag (k -> *) where
  ProdFrag (M1 D c f) = ProdFrag f
  ProdFrag (M1 C c f) = ProdFrag f
  ProdFrag U1 = 'Nil
  ProdFrag (M1 S c f) = 'Nil :+ M1 S c f
  ProdFrag (l :*: M1 S c f) = ProdFrag l :+ M1 S c f
  ProdFrag (l :*: (l2 :*: r2)) = ProdFrag ((l :*: l2) :*: r2)

class ProdRep (rep :: k -> *) where
  toProd :: rep x -> Prod (ProdFrag rep) (At x)
  fromProd :: Prod (ProdFrag rep) (At x) -> rep x

instance ProdRep f => ProdRep (M1 D c f) where
  toProd = toProd . unM1
  fromProd = M1 . fromProd

-- | No instances for 'V1' or ':+:', so this only handles /single-constructor/ data types
instance ProdRep f => ProdRep (M1 C c f) where
  toProd = toProd . unM1
  fromProd = M1 . fromProd

instance ProdRep U1 where
  toProd = \_ -> nil
  fromProd = \_ -> U1

instance ProdRep (M1 S c f) where
  toProd = toSingletonProd . MkAt
  fromProd = getAt . fromSingletonProd

instance (KnownFragCard (FragLT (M1 S c f) (ProdFrag l)),FragEQ (M1 S c f) (ProdFrag l) ~ 'Nil,SetFrag (ProdFrag l) ~ '(),ProdRep l) => ProdRep (l :*: M1 S c f) where
  toProd = \(l :*: r) -> toProd l `ext` MkAt r
  fromProd = \p -> let (l,MkAt r) = ret p in fromProd l :*: r

instance (ProdRep ((l :*: l2) :*: r2)) => ProdRep (l :*: (l2 :*: r2)) where
  toProd = \(l :*: (l2 :*: r2)) -> toProd ((l :*: l2) :*: r2)
  fromProd = (\((l :*: l2) :*: r2) -> (l :*: (l2 :*: r2))) . fromProd
