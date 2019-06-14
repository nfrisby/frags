{-# LANGUAGE ConstraintKinds #-}   -- ImplicProd
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}
{-# OPTIONS_GHC -Wwarn=partial-type-signatures #-}

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

-- {-# OPTIONS_GHC -fplugin-opt Data.Frag.Plugin:trace #-}
-- {-# OPTIONS_GHC -fprint-explicit-kinds #-}
-- {-# OPTIONS_GHC -dppr-debug -dsuppress-all #-}
-- {-# OPTIONS_GHC -ddump-tc-trace #-}

-- | Structural types indexed by @frag@s.
module Data.Motley (
  -- * Products
  Prod(..),
  ext,
  prj,
  nil,
  ret,
  -- ** Evidence
  polyProd,
  proofProd,
  -- ** Zip
  foldZipWithProd,
  zipProd,
  zipWithProd,
  -- * Sums
  Sum(..),
  absurd,
  alt,
  inj,
  -- ** Zip
  sameSum,
  -- * Operators
  foldMapProd,
  foldMapSum,
  placeProd,
  placeSum,
  fromSingletonProd,
  fromSingletonSum,
  idProd,
  idSum,
  mapProd,
  mapSum,
  opticProd,
  opticProd',
  opticSum,
  opticSum',
  toSingletonProd,
  toSingletonSum,
  traverseProd,
  traverseSum,
  updateProd,
  updateSum,
  -- ** Eliminators
  elimProd,
  elimProdSum,
  elimSum,
  elimSumProd,
  -- ** Pedantry
  introProd,
  introSum,
  minusProd,
  minusSum,
  plusProd,
  plusSum,
  zeroProd,
  zeroSum,
  -- * Re-exports
  -- ** From "Data.Frag"
  type (:-), type (:+), Frag(Nil), FragEQ, FragLT, KnownFragCard, SetFrag,
  -- ** Useful functors
  At(..),
  Compose(..),
  Const(..),
  Identity(..),
  Op(..),
  Product(..),
  Proxy(..),
  U1(..),
  -- ** Implicit values
  Dict1(..),
  Implic(..),
  ImplicProd,
  implicProd,
  mapImplicProd,
  pullImplicProd,
  pushImplicProd,
  withImplicProd,
  ) where

import qualified Control.Lens as Lens
import qualified Control.Lens.Iso as Iso
import qualified Control.Lens.Prism as Prism
import qualified Data.Functor.Arity1ToHask.Classes as A1H
import Data.Functor.At (At(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Contravariant (Op(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Fun (type (~>)(..))
import Data.Frag
import Data.Implic (Dict1(..),Dict2(..),Implic(..),Imp,getImp,unsafeMkImp)
import Data.Motley.Place
import qualified Data.Monoid as M
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..),testEquality)
import GHC.Exts (Proxy#,magicDict,proxy#)
import GHC.Generics (U1(..))
import qualified Test.QuickCheck as QC

-- | @Sum p f@ contains the @f@ value for exactly one of the basis elements in the set @p@.
data Sum :: Frag k -> (k -> *) -> * where
  MkSum :: !(Place p a) -> f a -> Sum p f

-- | Alias of 'absurd'
zeroSum :: Sum 'Nil f -> a
zeroSum = absurd "zeroSum"

-- | Inject a value into the sum.
inj :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => f a -> Sum (p :+ a) f
inj = MkSum MkPlace

class    (FragEQ a p ~ ('Nil :+ '()),KnownFragCard (FragLT a p)) => ToMaybeConSum p a
instance (FragEQ a p ~ ('Nil :+ '()),KnownFragCard (FragLT a p)) => ToMaybeConSum p a
instance SetFrag p ~ '() => A1H.ToMaybe (Sum p) where
  type ToMaybeCon (Sum p) = ToMaybeConSum p
  toMaybe = const Nothing `alt` Just

-- | Weaken/widen the sum by adding a basis element to the frag index.
plusSum ::
    (SetFrag p ~ '(),FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    Sum p f -> proxy a -> Sum (p :+ a) f
plusSum = \(MkSum (frep :: Place p b) x) (_ :: proxy a) -> let
  cmp = case frep of
    MkPlace -> axiom_lessThan_total
      (Proxy :: Proxy p) (Proxy :: Proxy b) (Proxy :: Proxy a)
      Refl Refl Refl
  frep' = case cmp of
    Left lt -> place_plus_greater frep lt
    Right lt -> place_plus_lesser frep lt
  in
  MkSum frep' x

-- | Function for an impossible case. Compare to 'Data.Void.absurd'.
absurd :: String -> Sum 'Nil f -> a
absurd = \s _ -> error $ "absurd Sum: " ++ s

-- |
minusSum ::
    (SetFrag p ~ '(),FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    Sum (p :+ a) f -> Either (Sum p f) (f a)
minusSum = alt Left Right

-- | Eliminate a sum via two handlers, one for a particular summand and one for the rest of the sum.
--
-- Note that 'minusSum' and @either ('plusSum' Proxy) 'inj'@ are inverses.
--
-- With a chain of 'alt's and an 'absurd' at the root,
-- one can build a @case@ expression for a sum that is ensured to handle all cases.
alt ::
    (SetFrag p ~ '(),FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    (Sum p f -> ans) -> (f a -> ans) -> Sum (p :+ a) f -> ans
alt = \inner here (MkSum old x) -> case lemma_narrow Refl old MkPlace of
  Left refl -> here $ co x refl
  Right new -> inner $ MkSum new x
  where
  co :: f a -> a :~: b -> f b
  co x Refl = x

-- | Simple prism to a summand.
opticSum' ::
    (SetFrag p ~ '(),FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    Prism.Prism' (Sum (p :+ a) f) (f a)
opticSum' = opticSum

-- | Prism to a summand.
opticSum ::
    (SetFrag p ~ '(),FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p),FragEQ b p ~ 'Nil,KnownFragCard (FragLT b p))
  =>
    Prism.Prism (Sum (p :+ a) f) (Sum (p :+ b) f) (f a) (f b)
opticSum = \f -> let
  step1 = alt Left Right
  step2 = Prism.right' f
  step3 = \case
    Left miss -> pure $ miss `plusSum` Proxy
    Right hit -> inj <$> hit
  in Iso.dimap step1 step3 step2

-- | Specialization of 'inj'.
toSingletonSum :: f a -> Sum ('Nil :+ a) f
toSingletonSum = inj

-- | Inverse of 'toSingletonSum'.
fromSingletonSum :: Sum ('Nil :+ a) f -> f a
fromSingletonSum = \(MkSum MkPlace x) -> x

-- |
mapSum :: (forall a. f a -> g a) -> Sum fr f -> Sum fr g
mapSum = \f (MkSum rep x) -> MkSum rep (f x)

instance A1H.Functor (Sum fr) where fmap = mapSum
instance A1H.Foldable (Sum fr) where foldMap = foldMapSum
instance A1H.Traversable (Sum fr) where traverse = traverseSum

type family FromJustFragPop (just :: MaybeFragPop k) :: k where
  FromJustFragPop ('JustFragPop p a count) = a

instance (fr ~ ('Nil :+ a)) => A1H.Singleton (Sum fr) where
  type Point (Sum fr) = FromJustFragPop (FragPop_NonDet fr)
  singletonIso = Iso.iso toSingletonSum fromSingletonSum

-- |
foldMapSum :: Monoid m => (forall a. f a -> m) -> Sum fr f -> m
foldMapSum = \f (MkSum _ x) -> f x

-- |
traverseSum :: Applicative af => (forall a. f a -> af (g a)) -> Sum fr f -> af (Sum fr g)
traverseSum = \f (MkSum frep x) -> MkSum frep <$> f x

-- | Introduce the 'Place' of the injected value.
placeSum :: Sum p f -> Sum p (Product (Place p) f)
placeSum = \(MkSum frep x) -> MkSum frep (Pair frep x)

-- | Combine two sums if they are injections of the same summand.
sameSum :: (SetFrag p ~ '()) => Sum p f -> Sum p g -> Maybe (Sum p (Product f g))
sameSum (MkSum frep1 x1) (MkSum frep2 x2) = case testEquality frep1 frep2 of
  Just Refl -> Just $ MkSum frep1 (Pair x1 x2)
  Nothing -> Nothing

-----

-- | @Prod p f@ contains one @f@ value per basis element in the set @p@.
-- The values are ordered according to GHC's arbitrary type ordering.
data Prod :: Frag k -> (k -> *) -> * where
  MkCons :: (FragLT a p ~ 'Nil,FragEQ a p ~ 'Nil) => !(Prod p f) -> f a -> Prod (p :+ a) f
  MkNil :: Prod 'Nil f

-- | A non-bottom @Prod p fr@ evidences @SetFrag fr@.
proofProd :: Prod fr f -> SetFrag fr :~: '()
proofProd = \case
  MkNil -> Refl
  MkCons tip _ -> case proofProd tip of Refl -> Refl

-- | The empty product.
nil :: Prod 'Nil f
nil = MkNil

-- | Alias of 'nil'
zeroProd :: Prod 'Nil f
zeroProd = nil

-- | Alias of 'ext'
plusProd :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod p f -> f a -> Prod (p :+ a) f
plusProd = ext

-- | Alias of 'ret'
minusProd :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod (p :+ a) f -> (Prod p f,f a)
minusProd = ret

infixl 8 `ext`

-- | Extend a product with an additional factor.
ext :: forall a p f. (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod p f -> f a -> Prod (p :+ a) f
ext = go MkPlace
  where
  go :: forall q. Place (q :+ a) a -> Prod q f -> f a -> Prod (q :+ a) f
  go new tip x = case tip of
    MkNil -> MkCons tip x
    MkCons tip' (y :: f z) -> let
      apart :: a :/~: z
      apart = case (proofProd tip',new) of
        (Refl,MkPlace) ->
          axiom_apart_multiplicity01
            (Proxy :: Proxy q) (Proxy :: Proxy a) (Proxy :: Proxy z)
      case_ = lemma_ext
        (Proxy :: Proxy (q :- z)) new y
        (case proofProd tip' of Refl -> Refl)
        new
      in
      case case_ of
      Left Refl -> case new of MkPlace -> MkCons tip x
      Right (Refl,new') -> case apart of MkApart -> MkCons (go new' tip' x) y

-- | Lens to a factor.
opticProd ::
    (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p),FragEQ b p ~ 'Nil,KnownFragCard (FragLT b p))
  =>
    Lens.Lens (Prod (p :+ a) f) (Prod (p :+ b) f) (f a) (f b)
opticProd = \f prod -> let
  (prod',x) = ret prod
  in ext prod' <$> f x

-- | Simple lens to a factor.
opticProd' ::
  forall a p f.
    (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    Lens.Lens' (Prod (p :+ a) f) (f a)
opticProd' = go MkPlace
  where
  go :: forall q g. Functor g => Place q a -> (f a -> g (f a)) -> Prod q f -> g (Prod q f)
  go frep f tip = case tip of
    MkCons tip' x -> case lemma_narrow (proofProd tip') frep (MkPlace `asc1` x) of
      Left Refl -> case frep of MkPlace -> MkCons tip' <$> f x
      Right frep' -> flip MkCons x <$> go frep' f tip'
    _ -> error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

  asc1 :: fff xxx -> ggg xxx -> fff xxx
  asc1 = const

-- | Project out a factor.
prj :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod (p :+ a) f -> f a
prj = snd . ret

class    (FragEQ a p ~ ('Nil :+ '()),KnownFragCard (FragLT a p)) => ToMaybeConProd p a
instance (FragEQ a p ~ ('Nil :+ '()),KnownFragCard (FragLT a p)) => ToMaybeConProd p a
instance SetFrag p ~ '() => A1H.ToMaybe (Prod p) where
  type ToMaybeCon (Prod p) = ToMaybeConProd p
  toMaybe = Just . prj

-- | Retract a factor by splitting the product into the factor and the rest of the product.
ret :: forall a p f. (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod (p :+ a) f -> (Prod p f,f a)
ret = go (Proxy @p) MkPlace
  where
  go :: forall q proxy. proxy q -> Place (q :+ a) a -> Prod (q :+ a) f -> (Prod q f,f a)
  go q frep@MkPlace tip = case tip of
    MkCons tip' x -> case lemma_ret q frep x (proofProd tip) Refl MkPlace frep of
      Left Refl -> (tip',x)
      Right (frep_down,still_min) -> let
        (inner,fa) = go (proxy2 q x) frep_down tip'
        in
        (case (proofProd inner,still_min) of (Refl,Refl) -> inner `ext` x,fa)
    _ -> error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

-- | Introduce the 'Place' of each factor.
placeProd :: Prod p f -> Prod p (Product (Place p) f)
placeProd = go id
  where
  go :: (forall a. Place q a -> Place p a) -> Prod q f -> Prod q (Product (Place p) f)
  go = \f -> \case
    MkCons tip x -> let
      frep = MkPlace
      in
      MkCons (go (f . lemma_placeProd (proofProd tip) frep) tip) (Pair (f frep) x)
    MkNil -> MkNil

proxy2 :: proxyp p -> proxya a -> Proxy (q :- a)
proxy2 _ _ = Proxy

-- | Alias for @'ext' 'nil'@.
toSingletonProd :: f a -> Prod ('Nil :+ a) f
toSingletonProd = ext nil

-- | Inverse of 'toSingletonProd'.
fromSingletonProd :: Prod ('Nil :+ a) f -> f a
fromSingletonProd = \case
  MkCons MkNil x -> x
  _ -> error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

-- |
mapProd :: (forall a. f a -> g a) -> Prod fr f -> Prod fr g
mapProd f = \case
  MkNil -> MkNil
  MkCons tip fa -> MkCons (mapProd f tip) (f fa)

-- |
traverseProd :: Applicative af => (forall a. f a -> af (g a)) -> Prod fr f -> af (Prod fr g)
traverseProd f = \case
  MkNil -> pure MkNil
  MkCons tip fa -> MkCons <$> traverseProd f tip <*> f fa

instance A1H.Functor (Prod fr) where fmap = mapProd
instance A1H.Foldable (Prod fr) where foldMap = foldMapProd
instance A1H.Traversable (Prod fr) where traverse = traverseProd

instance (fr ~ ('Nil :+ a)) => A1H.Singleton (Prod fr) where
  type Point (Prod fr) = FromJustFragPop (FragPop_NonDet fr)
  singletonIso = Iso.iso toSingletonProd fromSingletonProd

-- |
foldMapProd :: Monoid m => (forall a. f a -> m) -> Prod fr f -> m
foldMapProd f = \case
  MkNil -> mempty
  MkCons tip fa -> f fa <> foldMapProd f tip

-- |
zipWithProd :: (forall a. f a -> g a -> h a) -> Prod fr f -> Prod fr g -> Prod fr h
zipWithProd _ MkNil MkNil = MkNil
zipWithProd f l@(MkCons ltip lx) (MkCons rtip rx) =
  case axiom_minimum_unique (mkProxy l) lx rx (proofProd l) Refl Refl Refl Refl of
    Refl -> MkCons (zipWithProd f ltip rtip) (f lx rx)
  where
  mkProxy :: proxy fr f -> Proxy fr
  mkProxy = \_ -> Proxy
zipWithProd _ _ _ = error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

instance Implic (Prod fr U1) => A1H.Applicative (Prod fr) where
  pure = polyProd
  liftA2 = zipWithProd

-- | Replicate a value to build a product.
--
-- Ideally the context would just be @'SetFrag' fr@,
-- but that doesn't (currently?) provide enough information to actually build the product.
polyProd :: Implic (Prod fr U1) => (forall a. f a) -> Prod fr f
polyProd = \f -> g f `A1H.fmap` implic
  where
  g :: (forall b. f b) -> U1 a -> f a
  g = \f U1 -> f

-- | Same as @'zipWithProd' 'Pair'@
zipProd :: Prod fr f -> Prod fr g -> Prod fr (Product f g)
zipProd = zipWithProd Pair

-- | Same as @\\f ls rs -> 'foldMapProd' (\\('Pair' l r) -> f l r) $ 'zipProd' ls rs@
foldZipWithProd :: Monoid m => (forall a. f a -> g a -> m) -> Prod fr f -> Prod fr g -> m
foldZipWithProd _ MkNil MkNil = mempty
foldZipWithProd f l@(MkCons ltip lx) (MkCons rtip rx) =
  case axiom_minimum_unique (mkProxy l) lx rx (proofProd l) Refl Refl Refl Refl of
    Refl -> f lx rx <> foldZipWithProd f ltip rtip
  where
  mkProxy :: proxy fr f -> Proxy fr
  mkProxy = \_ -> Proxy
foldZipWithProd _ _ _ = error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

-----

-- | All this contortion because magicDict only handles classes with one type argument.
data KFP_Bundle (k :: *) (f :: k -> *) (p :: MaybeFragPop k)
type family Get_k (x :: *) :: * where Get_k (KFP_Bundle k _ _) = k
type family Get_f (x :: *) :: Get_k x -> * where Get_f (KFP_Bundle _ f _) = f
type family Get_p (x :: *) :: MaybeFragPop (Get_k x) where Get_p (KFP_Bundle _ _ k) = k

newtype ImpProd (kfp :: *) = MkImpProd{getImpProd :: Prod (FragPush (Get_p kfp)) (Get_f kfp)}

class ImplicProd_ (kfp :: *) where
  -- |
  implicProd_ :: ImpProd kfp

-- | Same as 'implic'.
implicProd :: forall k (f :: k -> *) p. ImplicProd f p => Prod p f
implicProd = getImpProd (implicProd_ :: ImpProd (KFP_Bundle k f (FragPop_NonDet p)))

-- | Specialization of 'Implic' for 'Prod'.
--
-- Riddled with implementation details.
type ImplicProd (f :: k -> *) p = ImplicProd_ (KFP_Bundle k f (FragPop_NonDet p))

instance ImplicProd_ (KFP_Bundle k f (FragPop_NonDet p)) => Implic (Prod p (f :: k -> *)) where
  implic = getImpProd (implicProd_ :: ImpProd (KFP_Bundle k f (FragPop_NonDet p)))

instance ImplicProd_ (KFP_Bundle k f 'NothingFragPop) where
  implicProd_ = MkImpProd nil
instance (KnownFragCard (FragLT b p),FragEQ b p ~ 'Nil,Implic (Prod p f),count ~ ('Nil :+ '()),Implic (f b)) => ImplicProd_ (KFP_Bundle k f ('JustFragPop p b count)) where
  implicProd_ = MkImpProd $ let
    tip :: Prod p f
    tip = implic
    in
    case proofProd tip of Refl -> tip `ext` (implic :: f b)

-- | Manual 'Implic' manipulation.
pullImplicProd :: Prod fs (Compose Imp f) -> Imp (Prod fs f)
pullImplicProd = unsafeMkImp . mapProd (getImp . getCompose)

-- | Manual 'Implic' manipulation.
pushImplicProd :: Imp (Prod fs f) -> Prod fs (Compose Imp f)
pushImplicProd = mapProd (Compose . unsafeMkImp) . getImp

-- | Manual 'Implic' manipulation.
--
-- Particularly for accessing superclasses.
-- For example, @mapImplicProd (\\d -> case getImp d of MkDict1 -> mkImp)@ inhabits
-- @Imp (Prod fs (Dict1 Ord)) -> Imp (Prod fs (Dict1 Eq))@.
mapImplicProd ::
    (forall x. Imp (f x) -> Imp (g x))
  ->
    Imp (Prod fs f)
  ->
    Imp (Prod fs g)
mapImplicProd = \f -> unsafeMkImp . mapProd (getImp . f . unsafeMkImp) . getImp

-- | See @Note [magicDictId magic]@ in the GHC source.
data WrapImplicProd kfp b = MkWrapImplicProd (ImplicProd_ kfp => Proxy# () -> b)

-- | Manual 'Implic' manipulation.
withImplicProd :: forall (f :: k -> *) p b. Imp (Prod p f) -> (ImplicProd f p => b) -> b
withImplicProd = \x k -> magicDict
  (MkWrapImplicProd (\_ -> k) :: WrapImplicProd (KFP_Bundle k f (FragPop_NonDet p)) b)
  (MkImpProd (getImp x) :: ImpProd (KFP_Bundle k f (FragPop_NonDet p)))
  (proxy# :: Proxy# ())

-----

instance Implic (Prod fr (Compose (Dict1 Eq) f)) => Eq (Sum fr f) where
  c1 == c2 = case proofProd dicts of
    Refl -> case sameSum c1 c2 of
      Just (MkSum MkPlace (Pair x1 x2)) -> f (prj dicts) x1 x2
      Nothing -> False
    where
    dicts :: Prod fr (Compose (Dict1 Eq) f)
    dicts = implic

    f :: Compose (Dict1 Eq) f a -> f a -> f a -> Bool
    f (Compose MkDict1) = (==)

instance Implic (Prod fr (Compose (Dict1 Show) f)) => Show (Sum fr f) where
  showsPrec = \_p tis@(MkSum frep _) ->
      showChar '<' . showsPrec 0 (getPlace frep) . showChar ' '
    .
      (mapProd f implic `elimProdSum` tis)
    .
      showChar '>'
    where
    f :: Compose (Dict1 Show) f a -> Compose (Op ShowS) f a
    f (Compose MkDict1) = Compose $ Op $ showsPrec 0

instance Implic (Prod fr (Compose (Dict1 Eq) f)) => Eq (Prod fr f) where
  (==) = \l r -> M.getAll $ foldZipWithProd f implic (zipProd l r)
    where
    f :: Compose (Dict1 Eq) f a -> Product f f a -> M.All
    f = \(Compose MkDict1) (Pair l r) -> M.All $ l == r

instance Implic (Prod fr (Compose (Dict1 Show) f)) => Show (Prod fr f) where
  showsPrec = \_p tip ->
      showChar '{'
    .
      unShowField (foldZipWithProd f implic tip)
    .
      showChar '}'
    where
    f :: Compose (Dict1 Show) f a -> f a -> ShowField
    f = \(Compose MkDict1) fa -> let g = showsPrec 11 fa in MkShowField g (showChar ' ' . g)

data ShowField = MkShowField ShowS !ShowS

unShowField :: ShowField -> ShowS
unShowField = \(MkShowField f _) -> f

instance Monoid ShowField where
  mempty = MkShowField id id
instance Semigroup ShowField where
  MkShowField a1 b1 <> MkShowField _ b2 = MkShowField (a1 . b2) (b1 . b2)

-----

-- | Eliminate a sum with a function product. (Gaster and Jones 1996)
elimProdSum :: Prod fr (Compose (Op z) f) -> Sum fr f -> z
elimProdSum = \tos (MkSum MkPlace x) -> case proofProd tos of
  Refl -> getCompose (prj tos) `getOp` x

-- | Eliminate a product with a function sum. (Gaster and Jones 1996)
elimSumProd :: Sum fr (Compose (Op z) f) -> Prod fr f -> z
elimSumProd = \(MkSum MkPlace x) tos -> case proofProd tos of
  Refl -> getCompose x `getOp` (prj tos)

-- |
elimProd :: Monoid m => Prod fr (Const m) -> m
elimProd = foldMapProd getConst

-- |
elimSum :: Sum ('Nil :+ a) f -> f a
elimSum = fromSingletonSum

-- | Apply a function product to an argument. (Gaster and Jones 1996)
introProd :: Prod p (Compose ((->) a) f) -> a -> Prod p f
introProd = \fs a -> A1H.fmap (\(Compose f) -> f a) fs

-- | Apply a function sum to an argument. (Gaster and Jones 1996)
introSum :: Sum p (Compose ((->) a) f) -> a -> Sum p f
introSum = \(MkSum MkPlace f) a -> MkSum MkPlace (getCompose f a)

-- |
updateSum :: Prod p (f ~> g) -> Sum p f -> Sum p g
updateSum = \fs (MkSum frep@MkPlace x) -> MkSum frep $ prj fs `appFun` x

-- |
updateProd :: Sum p (Compose M.Endo f) -> Prod p f -> Prod p f
updateProd = \(MkSum MkPlace (Compose (M.Endo fun))) -> Lens.over opticProd' fun

-----

-- | An ascription.
idProd :: Prod p f -> Prod p f
idProd = id

-- | An ascription.
idSum :: Sum p f -> Sum p f
idSum = id

-----

class    QC.Arbitrary (f a) => ArbitraryF f a
instance QC.Arbitrary (f a) => ArbitraryF f a

-- | Generates each factor under @'QC.scale' (\sz -> div sz n)@
instance Implic (Prod p (Dict2 ArbitraryF f)) => QC.Arbitrary (Prod p f) where
  arbitrary = let
    arbs :: Prod p (Dict2 ArbitraryF f)
    arbs = implic

    len = M.getSum $ foldMapProd (\_ -> M.Sum (1 :: Int)) arbs

    f :: Dict2 ArbitraryF f a -> QC.Gen (f a)
    f = \MkDict2 -> QC.scale (`div` len) $ QC.arbitrary
    in
    traverseProd f implic

  shrink = \tip -> let
    f :: forall a. Product (Place p) (Dict2 ArbitraryF f) a -> [[Prod p f]]
    f = \(Pair MkPlace MkDict2) -> [opticProd' (\x -> QC.shrink (x :: f a)) tip]

    interleave [] [] = []
    interleave acc [] = interleave [] acc
    interleave acc ([]:xss) = interleave acc xss
    interleave acc ((x:xs):xss) = x : interleave (xs : acc) xss
    in
    interleave [] $ foldMapProd f (placeProd implic)

-- | Does not adjust size
instance Implic (Prod p (Dict2 ArbitraryF f)) => QC.Arbitrary (Sum p f) where
  arbitrary = let
    f :: Product (Place p) (Dict2 ArbitraryF f) a -> [QC.Gen (Sum p f)]
    f = \(Pair frep MkDict2) -> [MkSum frep <$> QC.arbitrary]
    in
    QC.oneof $ foldMapProd f (placeProd implic)

  shrink = let
    f :: Dict2 ArbitraryF f a -> (f ~> Compose [] f) a
    f = \MkDict2 -> MkFun (Compose . QC.shrink)

    shrinks :: Prod p (f ~> Compose [] f)
    shrinks = mapProd f implic
    in
    traverseSum getCompose . updateSum shrinks
