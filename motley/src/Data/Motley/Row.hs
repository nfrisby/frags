{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}   -- at least Show OnVal

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Data.Motley.Row (
  Field(..),
  OnVal(..),
  Record(..),
  (.=),
  emp,
  ext,
  prj,
  proofRecord,
  ret,
  rmv,
  ) where

import Data.Frag
import Data.Motley (Prod)
import qualified Data.Motley as Mot
import Data.Type.Equality ((:~:)(..))

import Unsafe.Coerce (unsafeCoerce)

data OnVal :: (cod -> *) -> Mapping dom cod -> * where
  MkOnVal :: f a -> OnVal f (lbl := a)

instance Show (f (MappingVal mapping)) => Show (OnVal f mapping) where
  show (MkOnVal x) = show x

newtype Record p f = MkRecord{unRecord :: Prod p (OnVal f)}

newtype Field lbl fa = MkField fa

infix 7 .=
(.=) :: proxy lbl -> fa -> Field lbl fa
(.=) = \_ -> MkField

proofRecord :: Record p f -> SetFrag (DomFrag p) :~: '()
proofRecord r = r `seq` unsafeCoerce Refl   -- simple inductive proof

-- | Empty record
emp :: Record 'Nil f
emp = MkRecord Mot.nil

-- | Add a field
ext ::
  forall lbl a p f.
    (FragEQ lbl (DomFrag p) ~ 'Nil,KnownFragCard (FragLT (lbl := a) p))
  =>
    Record p f -> Field lbl (f a) -> Record (p :+ lbl := a) f
ext r@(MkRecord prod) (MkField fa) = case proofRecord r of
  Refl -> case Mot.proofProd prod of
    Refl -> MkRecord $ Mot.ext prod (MkOnVal fa :: OnVal f (lbl := a))

-- | TODO Can FragEQ lbl (DomFrag p) ~ 'Nil be enough?
ret ::
    (FragEQ (lbl := a) p ~ 'Nil,KnownFragCard (FragLT (lbl := a) p))
  =>
    proxylbl lbl -> Record (p :+ lbl := a) f -> (Record p f,f a)
ret _ (MkRecord prod) = case Mot.proofProd prod of
  Refl -> let
    (prod',MkOnVal fa) = Mot.ret prod
    in (MkRecord prod',fa)

-- | TODO Can FragEQ lbl (DomFrag p) ~ 'Nil be enough?
prj :: (FragEQ (lbl := a) p ~ 'Nil,KnownFragCard (FragLT (lbl := a) p)) => proxylbl lbl -> Record (p :+ lbl := a) f -> f a
prj = \lbl -> snd . ret lbl

-- | TODO Can FragEQ lbl (DomFrag p) ~ 'Nil be enough?
rmv :: (FragEQ (lbl := a) p ~ 'Nil,KnownFragCard (FragLT (lbl := a) p)) => proxylbl lbl -> Record (p :+ lbl := a) f -> Record p f
rmv = \lbl -> fst . ret lbl
