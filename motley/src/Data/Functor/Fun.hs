{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Data.Functor.Fun (
  -- * '(~>)'
  type (~>)(..),
  -- * 'Identity ~> Const' - 'Op'
  fromOp,
  toOp,
  -- * negative 'Const' - '(->)'
  fromFun,
  toFun,
  fromComposeFun,
  toComposeFun,
  ) where

import Data.Coerce (coerce)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Contravariant (Op(..))
import Data.Functor.Identity (Identity(..))

infixr 0 ~>
newtype (f ~> g) a = MkFun{appFun :: f a -> g a}

toComposeFun :: (Const x ~> g) a -> Compose ((->) x) g a
toComposeFun = coerce

fromComposeFun :: Compose ((->) x) g a -> (Const x ~> g) a
fromComposeFun = coerce

toOp :: (Identity ~> Const x) a -> Op x a
toOp = coerce

fromOp :: Op x a -> (Identity ~> Const x) a
fromOp = coerce

toFun :: (Const x ~> Identity) a -> x -> a
toFun = coerce

fromFun :: (x -> a) -> (Const x ~> Identity) a
fromFun = coerce
