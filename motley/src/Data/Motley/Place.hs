{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}

module Data.Motley.Place (
  -- * Frag-based 'Type.Reflection.Typeable'
  Place(..),
  getPlace,
  testPlace0,
  -- * Place order
  comparePlace,
  comparePlaceD,
  -- * Place adjustments
  place_minus_greater,
  place_minus_lesser,
  place_plus_greater,
  place_plus_lesser,
  -- * Lemmas
  lemma_ext,
  lemma_narrow,
  lemma_placeProd,
  lemma_ret,
  ) where

import Data.Frag
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..),TestEquality(..))
import GHC.Exts (Proxy#,proxy#)

import Unsafe.Coerce (unsafeCoerce)

unsafeRefl :: proxya a -> proxyb -> a :~: b
unsafeRefl = \_ _ -> unsafeCoerce Refl

-----

-- | A basis element has a /place/ in a frag if its multiplicity is one
-- and the total multiplicity of lesser elements is known.
--
-- If the frag is a set,
-- then there is a unique isomorphism
-- between the elements and their places
-- that preserves order.
--
-- Compare to 'Type.Reflection.TypeRep'
data Place :: Frag k -> k -> * where
  MkPlace :: (FragEQ a fr ~ ('Nil :+ '()),KnownFragCard (FragLT a fr)) => Place fr a

-- |
getPlace :: Place fr a -> Int
getPlace (MkPlace :: Place fr a) = fragCard' (proxy# :: Proxy# (FragLT a fr))

instance SetFrag fr ~ '() => TestEquality (Place fr) where
  testEquality l r = case comparePlace l r of
    TypeLT _ -> Nothing
    TypeEQ eq -> Just eq
    TypeGT _ -> Nothing

testPlace0 :: Place fr a -> Maybe (FragLT a fr :~: 'Nil)
testPlace0 (MkPlace :: Place fr a) =
  test_FragLT0 (Proxy :: Proxy fr) (Proxy :: Proxy a)

-----

-- internal use only
unsafe_shiftPlace :: (Int -> Int) -> Place fr a -> Place fr a
{-# INLINE unsafe_shiftPlace #-}
unsafe_shiftPlace = \f frep@MkPlace ->
    (fromOffset . repack . (\(MkHeapKnownFragCardD i) -> MkHeapKnownFragCardD $! f i) . unpack . toOffset)
  $
    frep
  where
  unpack :: KnownFragCardD fr a -> HeapKnownFragCardD fr a
  unpack = unsafeCoerce

  repack :: HeapKnownFragCardD fr a -> KnownFragCardD fr a
  repack = unsafeCoerce

  toOffset :: Place fr a -> KnownFragCardD fr a
  toOffset MkPlace = MkKnownFragCardD

  fromOffset :: (FragEQ a fr ~ ('Nil :+ '())) => KnownFragCardD fr a -> Place fr a
  fromOffset MkKnownFragCardD = MkPlace

-- THESE TWO MUST HAVE THE SAME HEAP REPRESENATION
data HeapKnownFragCardD :: Frag k -> k -> * where MkHeapKnownFragCardD :: Int -> HeapKnownFragCardD fr a
data KnownFragCardD :: Frag k -> k -> * where MkKnownFragCardD :: KnownFragCard (FragLT a fr) => KnownFragCardD fr a

-----

place_minus_lesser :: Place p b -> a :<: b -> Place (p :- a) b
place_minus_lesser frep LessThan = unsafeCoerce $ unsafe_shiftPlace (\i -> i - 1) frep

place_minus_greater :: Place p b -> b :<: a -> Place (p :- a) b
place_minus_greater frep LessThan = unsafeCoerce frep

place_plus_lesser :: Place p b -> a :<: b -> Place (p :+ a) b
place_plus_lesser frep LessThan = unsafeCoerce $ unsafe_shiftPlace (\i -> i + 1) frep

place_plus_greater :: Place p b -> b :<: a -> Place (p :+ a) b
place_plus_greater frep LessThan = unsafeCoerce frep

-----

comparePlace :: (SetFrag p ~ '()) => Place p a -> Place p b -> Ordered a b
comparePlace a b = case getPlace a `compare` getPlace b of
  LT -> TypeLT $ unsafeLessThan a b
  EQ -> TypeEQ $ unsafeRefl a b
  GT -> TypeGT $ unsafeLessThan b a

comparePlaceD :: SetFrag p :~: '() -> Place p a -> Place p b -> Ordered a b
comparePlaceD Refl = comparePlace

-----

-- | @+1@
lemma_placeProd ::
    (FragLT z fr ~ 'Nil)
  =>
    SetFrag fr :~: '()
  ->
    Place (fr :+ z) z
  ->
    Place fr a
  ->
    Place (fr :+ z) a
{-# INLINE lemma_placeProd #-}
lemma_placeProd
  set
  z@MkPlace a@(MkPlace :: Place fr a)
  = let
  apart = axiom_apart_multiplicity01
    (Proxy :: Proxy fr) z a
  z_lt_a = axiom_FragLT0 (Proxy :: Proxy fr) z a
    set Refl
    Refl (case apart of MkApart -> MkApart)
  in
  place_plus_lesser a z_lt_a

-- | Compare to the @Lacks@ axiom from Gaster and Jones.
lemma_narrow ::
    (FragEQ b fr ~ 'Nil)
  =>
    SetFrag fr :~: '()
  ->
    Place (fr :+ b) a
  ->
    Place (fr :+ b) b
  ->
    Either (a :~: b) (Place fr a)
lemma_narrow Refl a@MkPlace b = case comparePlace a b of
  TypeLT lt -> Right $ place_minus_greater a lt
  TypeEQ eq -> Left eq
  TypeGT lt -> Right $ place_minus_lesser a lt

-- | If @z@ is the minimum of @p :+ z@ then either @a@ or @z@ is the minimum of @p :+ z :+ a@.
lemma_ext :: (
      FragLT z p ~ 'Nil
    ,
      FragEQ z p ~ 'Nil
  ) =>
    proxyp p -> proxya a -> proxyz z
  ->
    SetFrag p :~: '()
  ->
    Place (p :+ z :+ a) a
  ->
    Either
      (FragLT a (p :+ z) :~: 'Nil)
      (FragLT z (p :+ a) :~: 'Nil,Place (p :+ a) a)
lemma_ext
  (_ :: proxyp p) (a :: proxya a) (z :: proxyz z)
  !set
  frep@MkPlace
  =
  let
  case_ =
    axiom_lessThan_total
      (Proxy :: Proxy (p :+ z)) z a
      (case set of Refl -> Refl) Refl (case (set,frep) of (Refl,MkPlace) -> Refl)
  in
  case case_ of
    Left z_lt_a -> Right (
        axiom_FragLT_plus_greater (Proxy :: Proxy p) (Proxy :: Proxy 'Nil) z_lt_a Refl
      ,
        place_minus_lesser frep z_lt_a
      )
    Right a_lt_z -> Left $ axiom_FragLT0_trans (Proxy :: Proxy (p :+ z)) a_lt_z Refl

-- | If @z@ is the minimum of @p :+ a@, then @z ~ a@ or @z < a@.
lemma_ret ::
    proxyp p -> proxya a -> proxyz z
  ->
    SetFrag (p :+ a) :~: '()
  ->
    FragLT z (p :+ a) :~: 'Nil
  ->
    Place (p :+ a) z
  ->
    Place (p :+ a) a
  ->
    Either
      (a :~: z)
      (Place (p :+ a :- z) a,FragLT z p :~: 'Nil)
lemma_ret
  (p :: proxyp p) (a :: proxya a) (z :: proxyz z)
  set zmin
  zfrep frep
  =
  case comparePlaceD set frep zfrep of
    TypeLT a_lt_z -> let
      z_lt_a = axiom_FragLT0 (Proxy :: Proxy (p :+ a)) z a
        set (case frep of MkPlace -> Refl)
        zmin (axiom_lessThan_apart a_lt_z)
      in
      axiom_lessThan_antisym
        "Data.Motley.Place.lemma_minimum_minus"
        a_lt_z z_lt_a
    TypeEQ eq -> Left eq
    TypeGT lt -> Right (
        place_minus_lesser frep lt
      ,
        axiom_FragLT0_apart
          p a z
          set (case axiom_lessThan_apart lt of MkApart -> MkApart) zmin
      )
