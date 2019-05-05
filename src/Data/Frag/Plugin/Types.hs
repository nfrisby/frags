{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}   -- at least Show

module Data.Frag.Plugin.Types where

import qualified Control.Monad
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Char (chr,ord)
import Data.Functor.Const
import Data.Functor.Identity
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid (All(..),Any(..),Endo(..),First(..),Sum(..))
import Data.Semigroup (Last(..))

--import qualified CoreMap
import qualified Outputable as O
import qualified VarEnv
import Type (Type,Var,eqType,nonDetCmpType)
import UniqFM (nonDetFoldUFM)

data Sign = Neg | Pos
  deriving (Eq,Ord,Show)

instance Semigroup Sign where (<>) = applySign

class Signed a where invertSign :: a -> a

instance Signed Sign where
  invertSign = \case
    Neg -> Pos
    Pos -> Neg

applySign :: Signed a => Sign -> a -> a
applySign = \case
  Neg -> invertSign
  Pos -> id

data instance FM Sign a = MkSignFM !(Maybe a) !(Maybe a)

instance Key Sign where
  alterFM k f (MkSignFM nfm pfm) = case k of
    Neg -> MkSignFM (f nfm) pfm
    Pos -> MkSignFM nfm (f pfm)
  emptyFM = MkSignFM Nothing Nothing
  foldMapFM f (MkSignFM nfm pfm) =
    foldMap (f Neg) nfm <> foldMap (f Pos) pfm
  lookupFM k (MkSignFM nfm pfm) = case k of
    Neg -> nfm
    Pos -> pfm
  mapFM f (MkSignFM nfm pfm) =
    MkSignFM `fmap_` traverse_ (f Neg) nfm `splat_` traverse_ (f Pos) pfm
  nullFM = \case
    MkSignFM Nothing Nothing -> True
    _ -> False

-----

data RawExt b = NilRawExt | ExtRawExt (RawExt b) !Sign b
  deriving (Eq,Foldable,Functor,Show,Traversable)

instance Signed (RawExt b) where
  invertSign = \case
    NilRawExt -> NilRawExt
    ExtRawExt ext s b -> ExtRawExt (invertSign ext) (invertSign s) b

data Fun b =
    FragCard
  |
    FragEQ !b
  |
    FragLT !b
  |
    FragNE !b
  deriving (Foldable,Functor,Show,Traversable)

instance (O.Outputable b) => O.Outputable (Fun b) where
  pprPrec p = \case
    FragCard -> O.text "FragCard"
    FragEQ b -> f b "FragEQ"
    FragLT b -> f b "FragLT"
    FragNE b -> f b "FragNE"
    where
    f b s = O.cparen (p > 10) $ O.text s O.<+> O.pprPrec 11 b

data FunRoot k b fr = MkFunRoot !k !(Fun b) !fr

instance (O.Outputable b,O.Outputable fr) => O.Outputable (FunRoot k b fr) where
  pprPrec p (MkFunRoot _ fun fr) = O.cparen (p > 10) $ O.ppr fun O.<+> O.parens (O.pprPrec 11 fr)

data RawFrag b r = MkRawFrag{
    rawFragExt :: RawExt b
  ,
    rawFragRoot :: r
  }
  deriving (Eq,Foldable,Functor,Show,Traversable)

instance (O.Outputable b,O.Outputable r) => O.Outputable (RawFrag b r) where
  pprPrec _ fr = (O.text "RawFrag" O.<>) $ O.braces $ case rawFragExt fr of
    NilRawExt -> O.ppr root
    ext0 -> go (O.pprPrec 6 root) ext0
    where
    root = rawFragRoot fr
    go acc = \case
      NilRawExt -> acc
      ExtRawExt ext s b -> go (acc O.<> O.char ' ' O.<> O.char ':' O.<> O.char c O.<> O.char ' ' O.<> O.pprPrec 6 b) ext
        where
        c = case s of
          Neg -> '-'
          Pos -> '+'      

forgetFrag :: Key b => Frag b r -> RawFrag b r
forgetFrag fr = MkRawFrag{
    -- TODO two lefts make a right? make this whole traversal thing less confusing!
    rawFragExt = ($ NilRawExt) $ foldlExt (fragExt fr) id $ \acc b count ->
      let sgn = if count < 0 then Neg else Pos in
      foldl (\acc' b' x -> acc' $ ExtRawExt x sgn b') acc (replicate (abs (getCount count)) b)
  ,
    rawFragRoot = fragRoot fr
  }

flattenRawFrag :: Key b => RawFrag b (RawFrag b r) -> RawFrag b r
flattenRawFrag outer = MkRawFrag{
    rawFragExt = go (rawFragExt inner)
  ,
    rawFragRoot = rawFragRoot inner
  }
  where
  inner = rawFragRoot outer

  go = \case
    NilRawExt -> rawFragExt outer
    ExtRawExt e s b -> ExtRawExt (go e) s b

-----

newtype Count = MkCount{unCount :: Sum Int}
  deriving (Eq,Ord,Monoid,Num,Semigroup)

instance O.Outputable Count where
  pprPrec _ count = O.ppr (getCount count)

mkCount :: Int -> Count
mkCount = MkCount . Sum

getCount :: Count -> Int
getCount = getSum . unCount

instance Show Count where show = show . getCount

instance Signed Count where invertSign = negate

newtype Ext b = MkExt{unExt :: FM b Count}

deriving instance (Eq (FM b Count)) => Eq (Ext b)

emptyExt :: Key b => Ext b
emptyExt = MkExt emptyFM

nullExt :: Key b => Ext b -> Bool
nullExt = \ext -> getAll $ foldMap (All . (0 ==)) (unExt ext)

insertExt :: Key b => b -> Count -> Ext b -> Ext b
insertExt k count = MkExt . insertFMM k count . unExt

addExt :: Key b => Ext b -> Ext b -> Ext b
addExt l r = MkExt $ unExt l `addFMM` unExt r

subtractExt :: Key b => Ext b -> Ext b -> Ext b
subtractExt l r = MkExt $ unExt l `subtractFMM` unExt r

foldlExt :: Key b => Ext b -> r -> (r -> b -> Count -> r) -> r
foldlExt ext nil snoc = (`appEndo` nil) $ foldMapExt ext $ \b count ->
  Endo $ \acc -> snoc acc b count

foldMapExt :: (Key b,Monoid a) => Ext b -> (b -> Count -> a) -> a
foldMapExt ext f = flip foldMapFM (unExt ext) $ \b count ->
  if 0 == count then mempty else f b count

filterExt :: Key b => (b -> Count -> Bool) -> Ext b -> Ext b
filterExt f = MkExt . filterFM f . unExt

instance Show (FM b Count) => Show (Ext b) where
  showsPrec p = showsPrec p . unExt

instance (Key b,O.Outputable b) => O.Outputable (Ext b) where
  ppr ext = foldlExt ext (O.text "Ext") $ \acc b count ->
    acc O.<+> O.ppr (b,getCount count)

instance Key b => Signed (Ext b) where
  invertSign = MkExt . mapFM (\_ -> invertSign) . unExt

data Frag b r = MkFrag{
    fragExt :: Ext b
  ,
    fragRoot :: r
  }
  deriving (Foldable,Functor,Traversable)

deriving instance (Eq r,Eq (FM b Count)) => Eq (Frag b r)

instance (Show b,Show r,Show (FM b Count)) => Show (Frag b r) where
  showsPrec p fr = showParen (p > 10) $ showsPrec 11 (fragRoot fr) . showChar ' ' . showsPrec 11 (fragExt fr)

instance (Key b,O.Outputable b,O.Outputable r) => O.Outputable (Frag b r) where
  pprPrec _ (MkFrag ext r) =
    O.text "MkFrag" O.<+> O.parens (O.ppr r) O.<+> O.ppr ext

forceExt :: Key b => Ext b -> Ext b
forceExt ext = foldlExt ext emptyExt $ \acc b count -> if 0 == count then acc else insertExt b count acc

forceFrag :: Key b => Frag b r -> Frag b r
forceFrag (MkFrag ext r) = MkFrag (forceExt ext) r

-----

data FragClass b r =
    KnownFragZ !(Frag b r) !Count
  |
    SetFrag !(Frag b r)
  deriving (Eq,Show)

instance (Key b,O.Outputable b,O.Outputable r) => O.Outputable (FragClass b r) where
  pprPrec _ = \case
    KnownFragZ fr count -> O.text "KnownFragZ" O.<+> O.parens (O.ppr fr) O.<+> O.ppr (getCount count)
    SetFrag fr -> O.text "SetFrag" O.<+> O.parens (O.ppr fr)

-----

data RawFragEquivalence b r = MkRawFragEquivalence !(Frag b r) !(Frag b r)

data FragEquivalence b r = MkFragEquivalence !r !r !(Ext b)
  deriving (Eq,Show)

instance (Key b,O.Outputable b,O.Outputable r) => O.Outputable (FragEquivalence b r) where
  pprPrec _ (MkFragEquivalence l r ext) =
    O.text "MkFragEquivalence" O.<+> O.parens (O.ppr l) O.<+> O.parens (O.ppr r) O.<+> O.ppr ext

-----

newtype RawApartness t = MkRawApartness (NonEmpty (t,t))

-- | INVARIANT: Non-empty.
newtype Apartness pair = MkApartness (FM pair ())
  deriving (Eq,Show)

instance (Key pair,O.Outputable pair) => O.Outputable (Apartness pair) where
  pprPrec _ (MkApartness fm) = O.text "MkApartness" O.<+> O.ppr (toListFM fm)

-----

data AnyT m a = MkAnyT{runAnyT :: (O.SDoc -> m ()) -> Any -> m (Any,a)}

instance Functor m => Functor (AnyT m) where fmap f (MkAnyT g) = MkAnyT $ fmap (fmap (fmap (fmap f))) g

instance MonadTrans AnyT where
  lift m = MkAnyT $ \_ s -> (,) s <$> m

instance Monad m => Applicative (AnyT m) where
  pure = \a -> MkAnyT $ \_ s -> pure (s,a)
  (<*>) = Control.Monad.ap

instance Monad m => Monad (AnyT m) where
  MkAnyT f >>= k = MkAnyT $ \r s1 -> do
    (s2,a) <- f r s1
    s2 `seq` runAnyT (k a) r s2

setM :: Applicative m => Bool -> AnyT m ()
setM b = MkAnyT $ \_ s1 ->
  if getAny s1 then pure (s1,())
  else let
    s2 = s1 <> Any b
    in s2 `seq` pure (s2,())

printM :: Functor m => O.SDoc -> AnyT m ()
printM str = MkAnyT $ \r s -> (s,()) <$ r str

hypotheticallyM :: Monad m => AnyT m a -> AnyT m (Bool,a)
hypotheticallyM (MkAnyT f) = MkAnyT $ \r s1 -> do
  (s2,a) <- f r mempty
  pure (s1,(getAny s2,a))

listeningM :: Monad m => AnyT m a -> AnyT m (Bool,a)
listeningM (MkAnyT f) = MkAnyT $ \r s1 -> do
  (s2,a) <- f r mempty
  let s2' = s1 <> s2
  s2' `seq` pure (s2',(getAny s2,a))

preferM :: Monad m => a -> AnyT m a -> AnyT m a
preferM a1 (MkAnyT f) = MkAnyT $ \r s1 -> do
  (s2,a2) <- f r s1
  pure (s2,if getAny s2 then a2 else a1)

alreadyM :: Applicative m => AnyT m Any
alreadyM = MkAnyT $ \_ s -> pure (s,s)

type AnyM = AnyT Identity

runAny :: AnyM a -> Any -> (Any,a)
runAny m = runIdentity . runAnyT m (\_ -> pure ())

-----

data Comparison =
    Apart (Maybe Inequality)
  |
    Equal
  deriving (Eq,Ord,Show)

instance Semigroup Comparison where
  l@(Apart Just{}) <> Apart{} = l
  Apart Nothing <> r@Apart{} = r
  Equal <> a = a
  a <> Equal = a

data Inequality =
    Greater
  |
    Lesser
  deriving (Eq,Ord,Show)

-----

data ChangeCheckState =
    Changed
  |
    -- everything is ok so far, expecting next term to begin at this index
    ExpectingFirst !Int

isChanged :: ChangeCheckState -> Bool
isChanged = \case
  Changed -> True
  ExpectingFirst{} -> False

-----

data Contra a =
    Contradiction
  |
    OK a
  deriving (Eq,Foldable,Functor,Show,Traversable)

instance Monoid a => Monoid (Contra a) where mempty = OK mempty
instance Semigroup a => Semigroup (Contra a) where
  OK l <> OK r = OK (l <> r)
  _ <> _ = Contradiction

instance Applicative Contra where
  pure = OK
  (<*>) = Control.Monad.ap
instance Monad Contra where
  OK a >>= k = k a
  _ >>= _ = Contradiction

data Derived l r = MkDerived{
    deqs :: !(FM (l,r) ())
  ,
    dneqs :: !(FM (l,r) ())
  }
  deriving (Eq,Show)

lens_deqs :: Lens' (Derived l r) (FM (l,r) ())
lens_deqs f (MkDerived eqs neqs) = flip MkDerived neqs <$> f eqs

lens_dneqs :: Lens' (Derived l r) (FM (l,r) ())
lens_dneqs f (MkDerived eqs neqs) = MkDerived eqs <$> f neqs

emptyDerived :: (Key l,Key r) => Derived l r
emptyDerived = MkDerived emptyFM emptyFM

-----

data NegPosExt b = MkNegPosExt !(Ext b) !Count !(Ext b) !Count

splitExt :: Key b => Ext b -> NegPosExt b
splitExt = \ext -> foldlExt ext (MkNegPosExt emptyExt mempty emptyExt mempty) $ \st@(MkNegPosExt n ncount p pcount) b count ->
  case compare count 0 of
    LT -> MkNegPosExt (insertExt b (abs count) n) (ncount - count) p pcount
    EQ -> st
    GT -> MkNegPosExt n ncount (insertExt b count p) (pcount + count)

-----

-- A picolens interface
type Lens' s t = forall f. Functor f => (t -> f t) -> s -> f s

over :: Lens' s t -> (t -> t) -> s -> s
over k f = runIdentity . k (Identity . f)

view :: Lens' s t -> s -> t
view k = getConst . k Const

-----

data CountInterval = MkCountInterval{
    atLeast :: !Count
  ,
    atMost :: !Count
  }
  deriving (Eq,Show)

instance O.Outputable CountInterval where
  pprPrec _ i = O.text "MkCountInterval" O.<+> O.ppr (getCount (atLeast i),getCount (atMost i))

instance Semigroup CountInterval where
  MkCountInterval ll lm <> MkCountInterval rl rm = MkCountInterval (max ll rl) (min lm rm)

singletonInterval :: CountInterval -> Maybe Count
singletonInterval (MkCountInterval ll lm) = if ll == lm then Just ll else Nothing

emptyInterval :: CountInterval -> Bool
emptyInterval i = atLeast i > atMost i

-----

data family FM k a

class Key k where
  alterFM :: k -> (Maybe a -> Maybe a) -> FM k a -> FM k a
  emptyFM :: FM k a
  foldMapFM :: Monoid m => (k -> a -> m) -> FM k a -> m
  lookupFM :: k -> FM k a -> Maybe a
  mapFM :: (k -> a -> b) -> FM k a -> FM k b
  nullFM :: FM k a -> Bool

toListFM :: Key k => FM k a -> [(k,a)]
toListFM = (`appEndo` []) . foldMapFM (\k a -> Endo $ (:) (k,a))

toKeysFM :: Key k => FM k a -> [k]
toKeysFM = (`appEndo` []) . foldMapFM (\k _ -> Endo $ (:) k)

fromListFMS :: (Key k,Semigroup a) => [(k,a)] -> FM k a
fromListFMS = foldl (flip (uncurry insertFMS)) emptyFM

fromListFM :: Key k => [(k,a)] -> FM k (Last a)
fromListFM = fromListFMS . map (fmap Last)

fromListFMSet :: (Key k) => [k] -> FM k ()
fromListFMSet = foldl (\acc k -> insertFMS k () acc) emptyFM

deleteFM :: Key k => k -> FM k a -> FM k a
deleteFM k = alterFM k (const Nothing)

filterFM :: Key k => (k -> a -> Bool) -> FM k a -> FM k a
filterFM f = mapMaybeFM (\k a -> if f k a then Just a else Nothing)

mapMaybeFM :: Key k => (k -> a -> Maybe b) -> FM k a -> FM k b
mapMaybeFM f = (flip appEndo emptyFM .) $ foldMapFM $ \k a -> case f k a of
  Nothing -> mempty
  Just b -> Endo $ alterFM k (\_ -> Just b)

singletonFM :: Key k => k -> a -> FM k a
singletonFM k a = alterFM k (\_ -> Just a) emptyFM

insertFMS :: (Key k,Semigroup a) => k -> a -> FM k a -> FM k a
insertFMS k a = alterFM k (Just . maybe a (<> a))

insertFMM :: (Eq m,Key k,Monoid m) => k -> m -> FM k m -> FM k m
insertFMM k m = alterFMM k (<> m)

alterFMM :: (Eq m,Key k,Monoid m) => k -> (m -> m) -> FM k m -> FM k m
alterFMM k f = alterFM k (g . f . maybe mempty id)
  where
  g x = if mempty == x then Nothing else Just x

compareViaFM :: Key k => k -> k -> Ordering
compareViaFM l r = case getFirst $ foldMap (First . Just) fm of
  Nothing -> EQ
  Just c -> if c > 0 then LT else GT
  where
  fm = insertFMM l (Sum (1 :: Int)) $ insertFMM r (Sum (-1)) $ emptyFM

subtractFMS :: (Key k,Semigroup a,Signed a) => FM k a -> FM k a -> FM k a
subtractFMS l r = (`appEndo` l) $ flip foldMapFM r $ \k a ->
  Endo $ insertFMS k (invertSign a)

addFMM :: (Key k,Eq a,Monoid a,Signed a) => FM k a -> FM k a -> FM k a
addFMM l r = (`appEndo` l) $ flip foldMapFM r $ \k a ->
  Endo $ insertFMM k a

subtractFMM :: (Key k,Eq a,Monoid a,Signed a) => FM k a -> FM k a -> FM k a
subtractFMM l r = (`appEndo` l) $ flip foldMapFM r $ \k a ->
  Endo $ insertFMM k (invertSign a)

instance Key k => Foldable (FM k) where foldMap f = foldMapFM (\_ -> f)
instance Key k => Functor (FM k) where fmap f = mapFM (\_ -> f)
instance (Eq k,Eq a,Key k) => Eq (FM k a) where
  l == r = toListFM l == toListFM r
-- instance (Eq m,Key k,Monoid m) => Monoid (FM k m) where mempty = emptyFM
-- instance (Eq m,Key k,Monoid m) => Semigroup (FM k m) where
--   l <> r = foldMapFM (\k m -> Endo (insertFMM k m)) l `appEndo` r

instance (Key k,Show a,Show k) => Show (FM k a) where
  showsPrec p fm = (if nullFM fm then id else showParen (p > 10)) $ (showString "FM" .) $ appEndo $ flip foldMapFM fm $ \k a ->
    Endo $ showChar ' ' . showsPrec 0 (k,a)

newtype instance FM (o,i) a = MkTuple2FM{unTuple2FM :: FM o (FM i a)}

instance (Key o,Key i) => Key (o,i) where
  alterFM (o,i) f =
      MkTuple2FM
    .
      alterFM o (Just . alterFM i f . maybe emptyFM id)
    .
      unTuple2FM
  emptyFM = MkTuple2FM emptyFM
  foldMapFM f = foldMapFM (\o -> foldMapFM (\i -> f (o,i))) . unTuple2FM
  lookupFM (k1,k2) m = lookupFM k1 (unTuple2FM m) >>= lookupFM k2
  mapFM f = fmap_ MkTuple2FM . mapFM (\o -> mapFM (\i -> f (o,i))) . unTuple2FM
  nullFM = nullFM . unTuple2FM

newtype instance FM (k1,k2,k3) a = MkTuple3FM{unTuple3FM :: FM k1 (FM k2 (FM k3 a))}

instance (Key k1,Key k2,Key k3) => Key (k1,k2,k3) where
  alterFM (k1,k2,k3) f =
      MkTuple3FM
    .
      alterFM k1 (Just . alterFM k2 (Just . alterFM k3 f . maybe emptyFM id) . maybe emptyFM id)
    .
      unTuple3FM
  emptyFM = MkTuple3FM emptyFM
  foldMapFM f = foldMapFM (\k1 -> foldMapFM (\k2 -> foldMapFM (\k3 -> f (k1,k2,k3)))) . unTuple3FM
  lookupFM (k1,k2,k3) m = lookupFM k1 (unTuple3FM m) >>= lookupFM k2 >>= lookupFM k3
  mapFM f = fmap_ MkTuple3FM . mapFM (\k1 -> mapFM (\k2 -> mapFM (\k3 -> f (k1,k2,k3)))) . unTuple3FM
  nullFM = nullFM . unTuple3FM

newtype instance FM (k1,k2,k3,k4) a = MkTuple4FM{unTuple4FM :: FM k1 (FM k2 (FM k3 (FM k4 a)))}

instance (Key k1,Key k2,Key k3,Key k4) => Key (k1,k2,k3,k4) where
  alterFM (k1,k2,k3,k4) f =
      MkTuple4FM
    .
      alterFM k1 (Just . alterFM k2 (Just . alterFM k3 (Just . alterFM k4 f . maybe emptyFM id) . maybe emptyFM id) . maybe emptyFM id)
    .
      unTuple4FM
  emptyFM = MkTuple4FM emptyFM
  foldMapFM f = foldMapFM (\k1 -> foldMapFM (\k2 -> foldMapFM (\k3 -> foldMapFM (\k4 -> f (k1,k2,k3,k4))))) . unTuple4FM
  lookupFM (k1,k2,k3,k4) m = lookupFM k1 (unTuple4FM m) >>= lookupFM k2 >>= lookupFM k3 >>= lookupFM k4
  mapFM f = fmap_ MkTuple4FM . mapFM (\k1 -> mapFM (\k2 -> mapFM (\k3 -> mapFM (\k4 -> f (k1,k2,k3,k4))))) . unTuple4FM
  nullFM = nullFM . unTuple4FM

data instance FM (Maybe k) a = MkMaybeFM !(Maybe a) !(FM k a)

instance (Key k) => Key (Maybe k) where
  alterFM mk f (MkMaybeFM nfm jfm) = case mk of
    Nothing -> MkMaybeFM (f nfm) jfm
    Just k -> MkMaybeFM nfm (alterFM k f jfm)
  emptyFM = MkMaybeFM Nothing emptyFM
  foldMapFM f (MkMaybeFM nfm jfm) =
    foldMap (f Nothing) nfm <> foldMapFM (f . Just) jfm
  lookupFM k (MkMaybeFM nfm jfm) = maybe nfm (flip lookupFM jfm) k
  mapFM f (MkMaybeFM nfm jfm) =
    MkMaybeFM `fmap_` traverse_ (f Nothing) nfm `splat_` mapFM (f . Just) jfm
  nullFM = \case
    MkMaybeFM Nothing jfm -> nullFM jfm
    _ -> False

data instance FM (Either l r) a = MkEitherFM !(FM l a) !(FM r a)

instance (Key l,Key r) => Key (Either l r) where
  alterFM lr f (MkEitherFM lfm rfm) = case lr of
    Left k -> MkEitherFM (alterFM k f lfm) rfm
    Right k -> MkEitherFM lfm (alterFM k f rfm)
  emptyFM = MkEitherFM emptyFM emptyFM
  foldMapFM f (MkEitherFM lfm rfm) =
    foldMapFM (f . Left) lfm <> foldMapFM (f . Right) rfm
  lookupFM k (MkEitherFM lfm rfm) = either (flip lookupFM lfm) (flip lookupFM rfm) k
  mapFM f (MkEitherFM lfm rfm) =
    MkEitherFM `fmap_` mapFM (f . Left) lfm `splat_` mapFM (f . Right) rfm
  nullFM (MkEitherFM lfm rfm) = nullFM lfm && nullFM rfm

newtype instance FM () a = MkUnitFM (Maybe a)

instance Key () where
  alterFM _ f (MkUnitFM m) = MkUnitFM (f m)
  emptyFM = MkUnitFM Nothing
  foldMapFM f (MkUnitFM m) = foldMap (f ()) m
  lookupFM _ (MkUnitFM m) = m
  mapFM f (MkUnitFM m) = MkUnitFM `fmap_` traverse_ (f ()) m
  nullFM = \case
    MkUnitFM Nothing -> True
    _ -> False

data instance FM Bool a = MkBoolFM !(Maybe a) !(Maybe a)

instance Key Bool where
  alterFM k f (MkBoolFM ffm tfm)
    | k = MkBoolFM ffm (f tfm)
    | otherwise = MkBoolFM (f ffm) tfm
  emptyFM = MkBoolFM Nothing Nothing
  foldMapFM f (MkBoolFM ffm tfm) =
    foldMap (f False) ffm <> foldMap (f True) tfm
  lookupFM k (MkBoolFM ffm tfm) = if k then tfm else ffm
  mapFM f (MkBoolFM ffm tfm) =
    MkBoolFM `fmap_` traverse_ (f False) ffm `splat_` traverse_ (f True) tfm
  nullFM = \case
    MkBoolFM Nothing Nothing -> True
    _ -> False

data instance FM Ordering a = MkOrderingFM !(Maybe a) !(Maybe a) !(Maybe a)

instance Key Ordering where
  alterFM k f (MkOrderingFM lfm efm gfm) = case k of
    LT -> MkOrderingFM (f lfm) efm gfm
    EQ -> MkOrderingFM lfm (f efm) gfm
    GT -> MkOrderingFM lfm efm (f gfm)
  emptyFM = MkOrderingFM Nothing Nothing Nothing
  foldMapFM f (MkOrderingFM lfm efm gfm) =
    foldMap (f LT) lfm <> foldMap (f EQ) efm <> foldMap (f GT) gfm
  lookupFM k (MkOrderingFM lfm efm gfm) = case k of
    LT -> lfm
    EQ -> efm
    GT -> gfm
  mapFM f (MkOrderingFM lfm efm gfm) =
    MkOrderingFM `fmap_` traverse_ (f LT) lfm `splat_` traverse_ (f EQ) efm `splat_` traverse_ (f GT) gfm
  nullFM = \case
    MkOrderingFM Nothing Nothing Nothing -> True
    _ -> False

newtype instance FM Int a = MkIntFM{unIntFM :: IntMap.IntMap a}

instance Key Int where
  alterFM k f (MkIntFM im) = MkIntFM $ IntMap.alter f k im
  emptyFM = MkIntFM IntMap.empty
  foldMapFM f = IntMap.foldrWithKey (\k a m -> m <> f k a) mempty . unIntFM
  lookupFM k = IntMap.lookup k . unIntFM
  mapFM f = fmap_ MkIntFM . IntMap.mapWithKey f . unIntFM
  nullFM = IntMap.null . unIntFM

newtype instance FM Char a = MkCharFM{unCharFM :: IntMap.IntMap a}

instance Key Char where
  alterFM k f (MkCharFM im) = MkCharFM $ IntMap.alter f (ord k) im
  emptyFM = MkCharFM IntMap.empty
  foldMapFM f = IntMap.foldrWithKey (\k a m -> m <> f (chr k) a) mempty . unCharFM
  lookupFM k = IntMap.lookup (ord k) . unCharFM
  mapFM f = fmap_ MkCharFM . IntMap.mapWithKey (\k -> f (chr k)) . unCharFM
  nullFM = IntMap.null . unCharFM

newtype Str = MkStr String
  deriving (Eq,Show)

instance O.Outputable Str where ppr (MkStr s) = O.text s

unStr :: Str -> String
unStr (MkStr s) = s

newtype instance FM Str a = MkStrFM{unStrFM :: Map.Map String a}

instance Key Str where
  alterFM k f (MkStrFM sm) = MkStrFM $ Map.alter f (unStr k) sm
  emptyFM = MkStrFM Map.empty
  foldMapFM f = Map.foldrWithKey (\k a m -> m <> f (MkStr k) a) mempty . unStrFM
  lookupFM k = Map.lookup (unStr k) . unStrFM
  mapFM f = fmap_ MkStrFM . Map.mapWithKey (f . MkStr) . unStrFM
  nullFM = Map.null . unStrFM

-----

{- A tombstone.

-- We cannot use CoreMap.TypeMap because it uses UDFM which is not the ORDER_FRAGILE we need.

newtype instance FM Type a = MkTypeFM{unTypeFM :: CoreMap.TypeMap (FMTypeCell a)}

data FMTypeCell a = MkFMTypeCell{
    fmtcType :: !Type
  ,
    fmtcValue :: a
  }

instance Key Type where
  alterFM k f = MkTypeFM . CoreMap.alterTM k (fmap (MkFMTypeCell k) . f . fmap fmtcValue) . unTypeFM
  emptyFM = MkTypeFM CoreMap.emptyTM
  foldMapFM f (MkTypeFM tm) = CoreMap.foldTM (\(MkFMTypeCell k a) m -> f k a <> m) tm mempty
  lookupFM k = fmap fmtcValue . CoreMap.lookupTM k . unTypeFM
  mapFM f = fmap_ MkTypeFM . CoreMap.mapTM (\(MkFMTypeCell k a) -> MkFMTypeCell k $ f k a) . unTypeFM
  nullFM (MkTypeFM tm) = CoreMap.foldTM (\_ _ -> False) tm True
  -- CoreMap.TypeMap unfortunately has no traverse method
-}

newtype NonDetType = MkNonDetType{unNonDetType :: Type}

instance Eq NonDetType where MkNonDetType l == MkNonDetType r = eqType l r
instance Ord NonDetType where compare (MkNonDetType l) (MkNonDetType r) = nonDetCmpType l r

newtype instance FM Type a = MkTypeFM{unTypeFM :: Map.Map NonDetType a}

data FMTypeCell a = MkFMTypeCell{
    fmtcType :: !Type
  ,
    fmtcValue :: a
  }

instance Key Type where
  alterFM k f (MkTypeFM sm) = MkTypeFM $ Map.alter f (MkNonDetType k) sm
  emptyFM = MkTypeFM Map.empty
  foldMapFM f = Map.foldrWithKey (\k a m -> m <> f (unNonDetType k) a) mempty . unTypeFM
  lookupFM k = Map.lookup (MkNonDetType k) . unTypeFM
  mapFM f = fmap_ MkTypeFM . Map.mapWithKey (f . unNonDetType) . unTypeFM
  nullFM = Map.null . unTypeFM

-----

data FMVarCell a = MkFMVarCell{
    fmvcVar :: !Var
  ,
    fmvcValue :: a
  }

newtype instance FM Var a = MkVarFM{unVarFM :: VarEnv.VarEnv (FMVarCell a)}
instance Key Var where
  alterFM k f (MkVarFM ve) = MkVarFM $ VarEnv.alterVarEnv (fmap (MkFMVarCell k) . f . fmap fmvcValue) ve k
  emptyFM = MkVarFM VarEnv.emptyVarEnv
  foldMapFM f (MkVarFM ve) = nonDetFoldUFM (\(MkFMVarCell k a) m -> f k a <> m) mempty ve
  lookupFM v (MkVarFM ve) = fmvcValue <$> VarEnv.lookupVarEnv ve v
  mapFM f = MkVarFM . VarEnv.mapVarEnv (\(MkFMVarCell k a) -> MkFMVarCell k (f k a)) . unVarFM
  nullFM = VarEnv.isEmptyVarEnv . unVarFM

-----

-- My lazy workaround to convert the traverseFM methods I wrote to mapFM methods,
-- hoping to convert back at some point.

infixl 4 `fmap_`
fmap_ :: (a -> b) -> a -> b
fmap_ = ($)

infixl 4 `splat_`
splat_ :: (a -> b) -> a -> b
splat_ = ($)

traverse_ :: Functor f => (a -> b) -> f a -> f b
traverse_ = fmap

-----

data Root k b r =
    FunRoot !k (Fun b) r
  |
    StuckRoot r
  deriving (Foldable,Functor,Traversable)

instance (Show (Fun b),Show k,Show r) => Show (Root k b r) where
  showsPrec p = \case
    FunRoot k fun r -> showParen (p > 10) $ showsPrec 0 fun . showChar ' ' . showsPrec 11 k . showChar ' ' . showsPrec 11 r
    StuckRoot r -> showsPrec p r

-----

data OrdSet b = MkOrdSet{
    ordSetFM :: !(FM b Int)
  ,
    ordSetSize :: !Int
  }

emptyOrdSet :: Key b => OrdSet b
emptyOrdSet = MkOrdSet emptyFM 0

insertOrdSet :: Key b => b -> OrdSet b -> OrdSet b
insertOrdSet b (MkOrdSet fm sz) = MkOrdSet (alterFM b (Just . maybe sz id) fm) (sz+1)

canonicalOrdSet :: Key b => OrdSet b -> Bool
canonicalOrdSet (MkOrdSet fm sz) = foldMapFM (\_ i -> [i]) fm == [0..sz-1]

-----

-- | INVARIANT: no constructor occurs as an argument to itself
data Context k b =
    -- | INVARIANT: Extension not empty.
    ExtC !(Ext b) !(Context k b)
  |
    -- | INVARIANT: Set is not empty if 'FragNEC'.
    FunC !k !(FunC b) !(FM b ()) !(Context k b)
  |
    OtherC
  deriving (Show)

instance (Key b,O.Outputable k,O.Outputable b) => O.Outputable (Context k b) where
  pprPrec _ = \case
    ExtC ext c -> O.text "ExtC" O.<+> O.parens (O.ppr ext) O.<+> O.ppr c
    FunC k fun fm c -> O.text "FunC" O.<+> O.parens (O.ppr k) O.<+> O.ppr fun O.<+> O.ppr (toListFM fm) O.<+> O.ppr c
    OtherC -> O.text "OtherC"

data FunC b =
    FragCardC
  |
    FragEQC !b
  |
    FragLTC !b
  |
    FragNEC
  deriving (Show)

instance O.Outputable b => O.Outputable (FunC b) where
  pprPrec _ = \case
    FragCardC -> O.text "FragCardC"
    FragEQC b -> O.text "FragEQC" O.<+> O.parens (O.ppr b)
    FragLTC b -> O.text "FragLTC" O.<+> O.parens (O.ppr b)
    FragNEC -> O.text "FragNEC"
