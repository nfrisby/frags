{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}

-- | The 'TestType' type is a severe simplication of GHC's @Type@:
-- no meta-vars, no binders, no kinds, no coercions, etc.
-- But it does have type constructor applications, type family applicatons, skolem variables, and flattening skolems.

module Data.Frag.Plugin.TestType where

import Debug.Trace

import qualified Data.Frag.Plugin.Apartness as Apartness
import qualified Data.Frag.Plugin.Class as Class
import qualified Data.Frag.Plugin.Equivalence as Equivalence
import qualified Data.Frag.Plugin.Frag as Frag
import qualified Data.Frag.Plugin.InertSet as InertSet
import Data.Frag.Plugin.Types

data TestKind = UnitKind | OtherKind
  deriving (Eq,Show)

data TestType =
    Con String [TestType]
  |
    Fun String [TestType]
  |
    Var String Int Bool   -- whether it's a fsk
  deriving (Eq,Show)

fsk_nil_plus_1 :: TestType
fsk_nil_plus_1 = Var "fsk(nil .+ 1)" 0 True

fsk_weird :: TestType
fsk_weird = Var "weird_fsk(nil .+ 1)" 1000 True

kind_inn :: TestKind -> TestType
kind_inn = \case
  OtherKind -> Con "OK" []
  UnitKind -> Con "UK" []

kind_out :: TestType -> TestKind
kind_out = \case
  Con "OK" [] -> OtherKind
  Con "UK" [] -> UnitKind
  o -> error $ "TestType.kind_out: " ++ show o

funRoot_out :: TestType -> Maybe (FunRoot TestKind TestType TestType)
funRoot_out = \case
  Fun "FragCard" [k,fr] -> Just $ MkFunRoot (kind_out k) FragCard fr
  Fun "FragEQ" [k,b,fr] -> Just $ MkFunRoot (kind_out k) (FragEQ b) fr
  Fun "FragLT" [k,b,fr] -> Just $ MkFunRoot (kind_out k) (FragLT b) fr
  Fun "FragNE" [k,b,fr] -> Just $ MkFunRoot (kind_out k) (FragNE b) fr
  _ -> Nothing

funRoot_inn :: FunRoot TestKind TestType TestType -> TestType
funRoot_inn = \case
  MkFunRoot k FragCard fr -> Fun "FragCard" [kind_inn k,fr]
  MkFunRoot k (FragEQ b) fr -> Fun "FragEQ" [kind_inn k,b,fr]
  MkFunRoot k (FragLT b) fr -> Fun "FragLT" [kind_inn k,b,fr]
  MkFunRoot k (FragNE b) fr -> Fun "FragNE" [kind_inn k,b,fr]

rawFrag_out :: TestType -> RawFrag TestType TestType
rawFrag_out = go id
  where
  go acc = \case
    Fun ":+" [fr,b] -> go (\x -> ExtRawExt (acc x) Pos b) fr
    Fun ":-" [fr,b] -> go (\x -> ExtRawExt (acc x) Neg b) fr
    r
      -- a wired-in unflattening
      | r == fsk_nil_plus_1 -> MkRawFrag (ExtRawExt (acc NilRawExt) Pos (Con "1" [])) (nilTT OtherKind)
      | r == fsk_weird -> MkRawFrag (ExtRawExt (acc NilRawExt) Pos (Con "1" [])) (nilTT OtherKind)
      | otherwise -> MkRawFrag (acc NilRawExt) r

rawFrag_inn :: RawFrag TestType TestType -> TestType
rawFrag_inn raw_fr = let x = go (rawFragRoot raw_fr) (rawFragExt raw_fr) in traceShow (raw_fr,x) x
  where
  go acc = \case
    NilRawExt -> acc
    ExtRawExt e s b -> go (Fun (case s of Neg -> ":-"; Pos -> ":+") [acc,b]) e

unitTT :: TestType
unitTT = Con "()" []

falseTT :: TestType
falseTT = Con "False" []

trueTT :: TestType
trueTT = Con "True" []

compareTT :: TestType -> TestType -> Maybe Comparison
compareTT (Con c1 args1) (Con c2 args2) = case compare c1 c2 of
  LT -> lt
  GT -> gt
  EQ -> go args1 args2
  where
  go [] [] = pure Equal
  go (l:ls) (r:rs) = case compareTT l r of
    Just Equal -> go ls rs
    o -> o
  go [] _ = lt
  go _ [] = gt

  lt = pure $ Apart (Just Lesser)
  gt = pure $ Apart (Just Greater)
compareTT Con{} _ = Nothing
compareTT _ Con{} = Nothing
compareTT (Fun f1 args1) (Fun f2 args2) = case compareTT (Con f1 args1) (Con f2 args2) of
  Just Equal -> Just Equal
  _ -> Nothing
compareTT Fun{} _ = Nothing
compareTT _ Fun{} = Nothing
compareTT (Var lc _ lfsk) (Var rc _ rfsk) = if lc == rc && lfsk == rfsk then pure Equal else Nothing

eqTT :: TestType -> TestType -> Bool
eqTT l r = Just Equal == compareTT l r

isNil :: TestType -> Bool
isNil = \case
  Con "Nil" _ -> True
  _ -> False

nilTT :: TestKind -> TestType
nilTT k = Con "Nil" [kind_inn k]

needSwap :: TestType -> TestType -> Bool
needSwap (Var lc llvl lfsk) (Var rc rlvl rfsk) =
    rlvl > llvl
  ||
    rfsk && not lfsk
  ||
    rc < lc
needSwap _ Var{} = True
needSwap Var{} _ = False
needSwap Fun{} Fun{} = False
needSwap _ Fun{} = True
needSwap Fun{} _ = False
needSwap _ _ = False

type V = (Str,Int,Bool)
type S = FM V TestType
data U =
    ApartTT
  |
    UnifiableTT S
  deriving (Eq,Show)

unifyTT :: TestType -> TestType -> Maybe U
unifyTT = f emptyFM
  where
  done = Just . UnifiableTT

  f u (Con s1 args1) (Con s2 args2)
    | s1 /= s2 = Just ApartTT
    | otherwise = fs u args1 args2

  f u l@(Var ls llvl lfsk) r@(Var rs rlvl rfsk)
    | lv == rv = done u
    | otherwise = case lookupFM lv u of
    Just tt -> f u tt r
    Nothing -> case lookupFM rv u of
      Just tt -> f u l tt
      Nothing -> done $ alterFM lv' (\_ -> Just r') u
        where
        (lv',r') = if needSwap l r then (rv,l) else (lv,r)
    where
    lv = (MkStr ls,llvl,lfsk)
    rv = (MkStr rs,rlvl,rfsk)
  f u l (Var s lvl fsk) = fvar u (MkStr s,lvl,fsk) l (f u)
  f u (Var s lvl fsk) r = fvar u (MkStr s,lvl,fsk) r (flip (f u))

  f _ Fun{} _ = Nothing
  f _ _ Fun{} = Nothing

  fs u [] [] = done u
  fs u (l:ls) (r:rs) = do
    uu' <- f u l r
    case uu' of
      ApartTT -> Just ApartTT
      UnifiableTT u' -> fs u' ls rs
  fs _ _ _ = Just ApartTT

  fvar u v tt k = case lookupFM v u of
    Just tt' -> k tt tt'
    Nothing -> done $ alterFM v (\_ -> Just tt) u

removeFVsTT :: FM V () -> TestType -> FM V ()
removeFVsTT = check go
  where
  check k vs tt = if nullFM vs then vs else k vs tt

  go vs = \case
    Con _ tts -> gos vs tts
    Fun _ tts -> gos vs tts
    Var nm lvl fsk
      | Just () <- lookupFM v vs -> alterFM v (\_ -> Nothing) vs
      | otherwise -> vs
      where
      v = (MkStr nm,lvl,fsk)

  gos vs = \case
    [] -> vs
    tt:tts -> check gos (go vs tt) tts

-----

fragEnv :: Frag.Env TestKind TestType TestType
fragEnv = Frag.MkEnv{
    Frag.envFunRoot_inn = funRoot_inn
  ,
    Frag.envFunRoot_out = funRoot_out
  ,
    Frag.envIsEQ = \x y -> (Equal == ) <$> compareTT x y
  ,
    Frag.envIsLT = \x y -> case compareTT x y of
      Just (Apart ineq) -> (Lesser ==) <$> ineq
      Just Equal -> Just False
      Nothing -> Nothing
  ,
    Frag.envIsNil = isNil
  ,
    Frag.envIsZBasis = \case
      OtherKind -> False
      UnitKind -> True
  ,
    Frag.envMultiplicity = \_ _ -> Nothing
  ,
    Frag.envNil = nilTT
  ,
    Frag.envRawFrag_inn = rawFrag_inn
  ,
    Frag.envRawFrag_out = rawFrag_out
  ,
    Frag.envUnit = unitTT
  ,
    Frag.envZBasis = UnitKind
  }

eqEnv :: Equivalence.Env TestKind TestType TestType
eqEnv = Equivalence.MkEnv{
    Equivalence.envEqR = eqTT
  ,
    Equivalence.envIsNil = isNil
  ,
    Equivalence.envNeedSwap = needSwap
  ,
    Equivalence.envNil = nilTT
  ,
    Equivalence.envNotApart = \x y -> case compareTT x y of
      Just Apart{} -> False
      Just Equal -> True
      Nothing -> True
  ,
    Equivalence.envMultiplicity = \r _ -> if isNil r then Just (MkCountInterval 0 0) else Nothing
  ,
    Equivalence.envPassThru = fragEnv
  }

apartnessEnv :: Apartness.Env TestType TestType
apartnessEnv = Apartness.MkEnv{
    Apartness.envTrivial = (falseTT,trueTT)
  ,
    Apartness.envTryUnify = \l r -> case unifyTT l r of
      Nothing -> Nothing
      Just ApartTT -> Just Apartness.UApart
      Just (UnifiableTT u)
        | Var s lvl fsk <- l
        , u == singletonFM (MkStr s,lvl,fsk) r -> Nothing
        | Var s lvl fsk <- r
        , u == singletonFM (MkStr s,lvl,fsk) l -> Nothing
        | otherwise -> Just $ Apartness.Unifiable [ (Var s lvl fsk,tt) | ((MkStr s,lvl,fsk),tt) <- toListFM u ]
  }

classEnv :: Class.Env TestKind TestType TestType
classEnv = Class.MkEnv{
    Class.envEq = \x y -> (Equal ==) <$> compareTT x y
  ,
    Class.envIsNil = isNil
  ,
    Class.envIsSet = isNil
  ,
    Class.envPassThru = fragEnv
  }

envTT :: InertSet.Env TestKind TestType
envTT = InertSet.MkEnv{
    InertSet.envApartness = apartnessEnv
  ,
    InertSet.envClass = classEnv
  ,
    InertSet.envEquivalence = eqEnv
  ,
    InertSet.envFrag = fragEnv
  }

type TestTypeSubst = FM V (Frag TestType TestType)

cacheEnvTT :: InertSet.CacheEnv TestTypeSubst TestType V
cacheEnvTT = InertSet.MkCacheEnv{
    InertSet.envEmptySubst = emptyFM
  ,
    InertSet.envExtendSubst = \v fr -> alterFM v (\_ -> Just fr)
  ,
    InertSet.envLookup = lookupFM
  ,
    InertSet.envNeedSwap = \(MkStr ls,llvl,lfsk) (MkStr rs,rlvl,rfsk) -> needSwap (Var ls llvl lfsk) (Var rs rlvl rfsk)
  ,
    InertSet.envRemoveFVs = removeFVsTT
  ,
    InertSet.envVar_out = \case
      Var s lvl fsk -> Just (MkStr s,lvl,fsk)
      _ -> Nothing
  }

-----

newtype TestTypes = MkTestTypes{unTestTypes :: [TestType]}

newtype instance FM TestType a = MkTestTypeFM{unTestTypeFM :: FM (Either (Bool,Str,TestTypes) V) a}

to_rep :: TestType -> Either (Bool,Str,TestTypes) V
to_rep = \case
  Con s tts -> Left (False,MkStr s,MkTestTypes tts)
  Fun s tts -> Left (True,MkStr s,MkTestTypes tts)
  Var s i b -> Right (MkStr s,i,b)

fr_rep :: Either (Bool,Str,TestTypes) V -> TestType
fr_rep = \case
  Left (False,MkStr s,MkTestTypes tts) -> Con s tts
  Left (True,MkStr s,MkTestTypes tts) -> Fun s tts
  Right (MkStr s,i,b) -> Var s i b

instance Key TestType where
  alterFM k f (MkTestTypeFM fm) = MkTestTypeFM $ alterFM (to_rep k) f fm
  emptyFM = MkTestTypeFM emptyFM
  foldMapFM f = foldMapFM (f . fr_rep) . unTestTypeFM
  lookupFM k = lookupFM (to_rep k) . unTestTypeFM
  mapFM f = fmap_ MkTestTypeFM . mapFM (f . fr_rep) . unTestTypeFM
  nullFM = nullFM . unTestTypeFM

newtype instance FM TestTypes a = MkTestTypesFM{unTestTypesFM :: FM (Maybe (TestType,TestTypes)) a}

to_reps :: TestTypes -> Maybe (TestType,TestTypes)
to_reps = (. unTestTypes) $ \case
  [] -> Nothing
  tt:tts -> Just (tt,MkTestTypes tts)

fr_reps :: Maybe (TestType,TestTypes) -> TestTypes
fr_reps = MkTestTypes . \case
  Nothing -> []
  Just (tt,MkTestTypes tts) -> tt:tts

instance Key TestTypes where
  alterFM k f (MkTestTypesFM fm) = MkTestTypesFM $ alterFM (to_reps k) f fm
  emptyFM = MkTestTypesFM emptyFM
  foldMapFM f = foldMapFM (f . fr_reps) . unTestTypesFM
  lookupFM k = lookupFM (to_reps k) . unTestTypesFM
  mapFM f = fmap_ MkTestTypesFM . mapFM (f . fr_reps) . unTestTypesFM
  nullFM = nullFM . unTestTypesFM
