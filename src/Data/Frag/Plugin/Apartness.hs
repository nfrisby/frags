{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

module Data.Frag.Plugin.Apartness (
  Env(..),
  UnificationResult(..),
  interpret,
  orientedPair,
  simplify,
  ) where

import Data.Foldable (toList)
import Data.List.NonEmpty (nonEmpty)
import Data.Monoid (Endo(..))

import Data.Frag.Plugin.Types

data UnificationResult u1 =
    UApart
  |
    -- | This MGU is idempotent and its individual mappings are each irreflexive and smaller than the two terms that were unified.
    -- Moreover, they should be correctly oriented and all have been checked for manifest apartness already.
    Unifiable ![u1]

data Env l r = MkEnv{
    -- | The representation of @(False,True)@.
    envTrivial :: !(l,r)
  ,
    -- | See 'UnificationResult'.
    --
    -- In particular, unifying two different variables in a vacuum will give 'Nothing'.
    envTryUnify :: !(l -> r -> Maybe (UnificationResult (l,r)))
  }

interpret :: (Key b,Monad m) => RawApartness b -> AnyT m (Apartness (b,b))
interpret = \(MkRawApartness pairs) -> go 0 emptyFM (toList pairs)
  where
  go !i !fm = \case
    (l,r):pairs -> do
      lr <- orientedPair l r    -- mis-oriented: Apartness ('OneApart b a)
      let
        fm' = insertFMS lr (mkPos i) fm
      go (i + 1) fm' pairs
    [] -> do
      let
        changed = isChanged $ (`appEndo` ExpectingFirst 0) $ flip foldMap fm $ \pos ->
          Endo $ \check -> case (pos,check) of
            (OneAt j,ExpectingFirst expected)
              | j == expected    -- unsorted: Apartness ('ConsApart x y ('OneApart a b))
              -> ExpectingFirst $! expected + 1
            _ -> Changed   -- redundant: Apartness ('ConsApart x y ('OneApart x y))

      setM changed
      pure $ MkApartness $ fmap (\_ -> ()) fm

data Pos =
    Multiple
  |
    OneAt !Int

instance Semigroup Pos where
  _ <> _ = Multiple

mkPos :: Int -> Pos
mkPos = OneAt

-- | Orders the components according to the 'Key' instance.
orientedPair :: (Key b,Monad m) => b -> b -> AnyT m (b,b)
orientedPair l r = case compareViaFM l r of
  -- we invert, because of the whole "left fold" thing
  LT -> do setM True; pure (r,l)   -- misoriented: Apartness ('OneApart b a)
  EQ -> pure (l,r)
  GT -> pure (l,r)

-----

simplify :: (Key b,Monad m) => Env b b -> Apartness (b,b) -> AnyT m (Contra (Apartness (b,b)))
simplify env (MkApartness fm) = case (MkRawApartness . fmap fst) <$> nonEmpty (toListFM fm) of
  Nothing -> do setM True; pure Contradiction
  Just raw -> (snd <$> hypotheticallyM (interpret raw)) >>= simplify_
    (envTrivial env)
    (envTryUnify env)
    id
    id

simplify_ ::
    (Key lr,Key lr',Monad m)
  =>
    lr'
  ->
   (l -> r -> Maybe (UnificationResult lr'))
  ->
    (lr -> (l,r))
  ->
    (lr -> lr')
  ->
    Apartness lr
  ->
    AnyT m (Contra (Apartness lr'))
simplify_ trivial tryUnify prj inj = \(MkApartness fm) -> go1 $ toKeysFM fm
  where
  ok = OK . MkApartness

  -- no-op on trivial
  go1 [lr] | EQ == compareViaFM (inj lr) trivial = pure $ ok $ singletonFM trivial ()
  go1 pairs = go emptyFM pairs

  go acc = \case
    lr:pairs -> case tryUnify l r of
      Nothing -> go (insertFMS (inj lr) () acc) pairs
      Just res -> (\x -> do setM True; x) $ case res of
        UApart -> pure $ ok $ singletonFM trivial ()   -- Found an apartness; stop now, returning a trivial constraint.
        Unifiable mgu -> go (foldr (\u1 -> insertFMS u1 ()) acc mgu) pairs   -- Do not recur into mgu; envTryUnify does that already.
      where
      (l,r) = prj lr
    [] -> if nullFM acc
      then do setM True; pure Contradiction   -- Everything unified away, so nothing was apart after all.
      else pure $ ok acc
