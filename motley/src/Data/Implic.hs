{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}   -- at least Implic QDict

module Data.Implic (
  -- * Class
  Implic(..),
  Imp,
  appImp,
  getImp,
  mkImp,

  -- * Wrappers
  -- ** Methods
  Cat(..),
  Def(..),
  Lbl(..),

  -- ** Dictionaries
  --
  -- | Even when not required, these may improve inference.
  Dict(..),
  Dict1(..),
  Dict2(..),
  Dict3(..),
  Dict4(..),
  Dict5(..),
  Dict6(..),
  Dict7(..),
  Dict8(..),
  Dict9(..),
  QDict(..),
  QDict1(..),
  QDict2(..),
  QDict3(..),
  QDict4(..),

  -- * Magic
  withImplic,
  unsafeMkImp,
  ) where

import Control.Applicative (Alternative,WrappedMonad(..),empty)
import qualified Control.Category as Cat
import Data.Coerce (Coercible)
import Data.Constraint (Dict(..))
import Data.Default (Default,def)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Product (Product(..))
import Data.Monoid (Alt(..),Ap(..))
import Data.Proxy (Proxy(..))
import Data.Semigroup (WrappedMonoid(..))
import Data.Type.Coercion (Coercion(..))
import Data.Type.Equality ((:~:)(..))
import Type.Reflection (Typeable,TypeRep,typeRep)
import GHC.Exts (magicDict)
import GHC.Generics ((:*:)(..),(:.:)(..),K1(..),M1(..),Par1(..),Rec1(..),U1(..))
import qualified GHC.OverloadedLabels as OL
import GHC.TypeLits (Symbol)

-- | The class of types that have an implicit value.
--
-- This notably includes -- but is not limited to -- /singleton types/,
-- those with exactly one genuine value.
--
-- This class focuses on structural types.
-- Structural product types should delegate to the 'Implic' instances of their component types.
-- Library authors should in general avoid 'Implic' instances for sum types and most nominal types.
-- In particular, 'Implic' is more conservative than 'Default' (see 'Def');
-- there is no instance for lists, for example.
--
-- However, any expections are subject to the fact
-- that the user can declare any instance:
-- 'implic' ultimately consists of \"the values the user told GHC to use\".
class Implic a where
  implic :: a

-- | A value necessarily constructed by only 'mkImp' and 'appImp'.
newtype Imp a = MkImp{getImp :: a}

unsafeMkImp :: a -> Imp a
unsafeMkImp = MkImp

appImp :: Imp (a -> b) -> Imp a -> Imp b
appImp = \(MkImp f) (MkImp a) -> MkImp (f a)

mkImp :: Implic a => Imp a
mkImp = MkImp implic

instance Implic a => Default (Imp a) where
  def = mkImp

instance Implic a => Implic (Imp a) where
  implic = mkImp

-----

instance Implic () where
  implic = ()

instance (Implic a,Implic b) => Implic (a,b) where
  implic = (implic,implic)

instance (Implic a,Implic b,Implic c) => Implic (a,b,c) where
  implic = (implic,implic,implic)

instance (Implic a,Implic b,Implic c,Implic d) => Implic (a,b,c,d) where
  implic = (implic,implic,implic,implic)

instance (Implic a,Implic b,Implic c,Implic d,Implic e) => Implic (a,b,c,d,e) where
  implic = (implic,implic,implic,implic,implic)

instance (Implic a,Implic b,Implic c,Implic d,Implic e,Implic f) => Implic (a,b,c,d,e,f) where
  implic = (implic,implic,implic,implic,implic,implic)

instance (Implic a,Implic b,Implic c,Implic d,Implic e,Implic f,Implic g) => Implic (a,b,c,d,e,f,g) where
  implic = (implic,implic,implic,implic,implic,implic,implic)

instance (Implic a,Implic b,Implic c,Implic d,Implic e,Implic f,Implic g,Implic h) => Implic (a,b,c,d,e,f,g,h) where
  implic = (implic,implic,implic,implic,implic,implic,implic,implic)

instance (Implic a,Implic b,Implic c,Implic d,Implic e,Implic f,Implic g,Implic h,Implic i) => Implic (a,b,c,d,e,f,g,h,i) where
  implic = (implic,implic,implic,implic,implic,implic,implic,implic,implic)

-----

instance Implic (Proxy a) where
  implic = Proxy

instance (Implic (l a),Implic (r a)) => Implic ((:*:) l r a) where
  implic = implic :*: implic

instance Implic (f (g a)) => Implic ((:.:) f g a) where
  implic = Comp1 implic

instance Implic c => Implic (K1 i c p) where
  implic = K1 implic

instance Implic (f p) => Implic (M1 i c f p) where
  implic = M1 implic

instance Implic p => Implic (Par1 p) where
  implic = Par1 implic

instance Implic (f p) => Implic (Rec1 f p) where
  implic = Rec1 implic

instance Implic (U1 a) where
  implic = U1

-----

instance Implic (f (g a)) => Implic (Compose f g a) where
  implic = Compose implic

instance Implic b => Implic (Const b a) where
  implic = Const implic

instance (Implic (l a),Implic (r a)) => Implic (Product l r a) where
  implic = Pair implic implic

instance Implic a => Implic (Identity a) where
  implic = Identity implic

-----

instance (a ~ b) => Implic ((:~:) a b) where
  implic = Refl

instance Coercible a b => Implic (Coercion a b) where
  implic = Coercion

instance Typeable a => Implic (TypeRep a) where
  implic = typeRep

-----

instance con => Implic (Dict con) where
  implic = Dict

-- |
data Dict1 con a = con a => MkDict1  -- ^
instance con a => Implic (Dict1 con a) where
  implic = MkDict1

data Dict2 con a b = con a b => MkDict2
instance con a b => Implic (Dict2 con a b) where
  implic = MkDict2

data Dict3 con a b c = con a b c => MkDict3
instance con a b c => Implic (Dict3 con a b c) where
  implic = MkDict3

data Dict4 con a b c d = con a b c d => MkDict4
instance con a b c d => Implic (Dict4 con a b c d) where
  implic = MkDict4

data Dict5 con a b c d e = con a b c d e => MkDict5
instance con a b c d e => Implic (Dict5 con a b c d e) where
  implic = MkDict5

data Dict6 con a b c d e f = con a b c d e f => MkDict6
instance con a b c d e f => Implic (Dict6 con a b c d e f) where
  implic = MkDict6

data Dict7 con a b c d e f g = con a b c d e f g => MkDict7
instance con a b c d e f g => Implic (Dict7 con a b c d e f g) where
  implic = MkDict7

data Dict8 con a b c d e f g h = con a b c d e f g h => MkDict8
instance con a b c d e f g h => Implic (Dict8 con a b c d e f g h) where
  implic = MkDict8

data Dict9 con a b c d e f g h i = con a b c d e f g h i => MkDict9
instance con a b c d e f g h i => Implic (Dict9 con a b c d e f g h i) where
  implic = MkDict9

-----

newtype Def a = MkDef{getDef :: a}
-- | 'def'
instance Default a => Implic (Def a) where
  implic = MkDef def

-- | 'empty'
instance Alternative f => Implic (Alt f a) where
  implic = Alt empty

newtype Cat cat a = MkCat{getId :: cat a a}
-- | 'Cat.id'
instance Cat.Category cat => Implic (Cat cat a) where
  implic = MkCat Cat.id

-- | 'mempty'
instance Monoid a => Implic (WrappedMonoid a) where
  implic = WrapMonoid mempty

-- | @'pure' 'implic'@
instance (Applicative f,Implic a) => Implic (Ap f a) where
  implic = Ap (pure implic)

-- | @'return' 'implic'@
instance (Monad f,Implic a) => Implic (WrappedMonad f a) where
  implic = WrapMonad (return implic)

newtype Lbl (x :: Symbol) a = MkLbl{getLbl :: a}
-- | 'OL.fromLabel'
instance OL.IsLabel x a => Implic (Lbl x a) where
  implic = MkLbl (OL.fromLabel @x)

-----

data QDict ante succ = (ante => succ) => MkQDict
instance (ante => succ) => Implic (QDict ante succ) where
  implic = MkQDict

data QDict1 ante succ a = (ante a => succ a) => MkQDict1
instance (ante a => succ a) => Implic (QDict1 ante succ a) where
  implic = MkQDict1

data QDict2 ante succ a b = (ante a b => succ a b) => MkQDict2
instance (ante a b => succ a b) => Implic (QDict2 ante succ a b) where
  implic = MkQDict2

data QDict3 ante succ a b c = (ante a b c => succ a b c) => MkQDict3
instance (ante a b c => succ a b c) => Implic (QDict3 ante succ a b c) where
  implic = MkQDict3

data QDict4 ante succ a b c d = (ante a b c d => succ a b c d) => MkQDict4
instance (ante a b c d => succ a b c d) => Implic (QDict4 ante succ a b c d) where
  implic = MkQDict4

-----

-- | See @Note [magicDictId magic]@ in GHC source.
data WrapImplic a b = MkWrapImplic (Implic a => Proxy a -> b)

withImplic :: forall a b. Imp a -> (Implic a => b) -> b
withImplic x k = magicDict
  (MkWrapImplic (\prx -> let _ = prx :: Proxy a in k))
  (getImp x)
  (Proxy :: Proxy a)
