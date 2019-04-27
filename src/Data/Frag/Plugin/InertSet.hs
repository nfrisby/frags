{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}

module Data.Frag.Plugin.InertSet (
  Cache,
  CacheEnv(..),
  Ct(..),
  Env(..),
  InertSet(..),
  WIP(..),
  emptyCache,
  extendInertSet,
  simplifyCt,

  -- * Lenses
  apartness_table,
  frag_subst,
  multiplicity_table,
  ) where

import Control.Monad (guard)
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NE
import qualified Outputable as O 

import qualified Data.Frag.Plugin.Apartness as Apartness
import qualified Data.Frag.Plugin.Class as Class
import qualified Data.Frag.Plugin.Equivalence as Equivalence
import qualified Data.Frag.Plugin.Frag as Frag
import Data.Frag.Plugin.Types

-- TODO Other than KnownFragCard, is there a need to track list of depended-upon evvars to force in evterm?
data Ct k t =
    ApartnessCt !(Apartness (t,t))
  |
    ClassCt !k !(FragClass t t)
  |
    EquivalenceCt !k !(FragEquivalence t t)
  deriving (Eq,Show)

instance (Key t,O.Outputable k,O.Outputable t) => O.Outputable (Ct k t) where
  pprPrec _ = \case
    ApartnessCt x -> O.ppr x
    ClassCt _ x -> O.ppr x
    EquivalenceCt _ x -> O.ppr x

data Env k t = MkEnv{   -- TODO flatten these fields
    envApartness :: !(Apartness.Env t t)
  ,
    envClass :: !(Class.Env k t t)
  ,
    envEquivalence :: !(Equivalence.Env k t t)
  ,
    envFrag :: !(Frag.Env k t t)
  }

simplifyCt :: (Key t,Monad m) => Env k t -> Ct k t -> AnyT m (Contra (Derived t t,NonEmpty (Ct k t)))
simplifyCt env = \case
  ApartnessCt x -> fmap (\y -> (emptyDerived,pure $ ApartnessCt y)) <$> Apartness.simplify (envApartness env) x
  ClassCt knd x -> fmap (fmap post) <$> Class.simplify (envClass env) knd x
    where
    post = \case
      Class.SimplClass kcts -> fmap (uncurry ClassCt) kcts
      Class.SimplFragEQ keq b sgn r -> ClassCt knd triv :| [EquivalenceCt knd eq]
        where
        fragEnv = envFrag env
        -- NB: knd is ()
        zero = Frag.envNil fragEnv knd
        triv = SetFrag $ MkFrag emptyExt zero
        eq = MkFragEquivalence r' zero $ (if sgn then insertExt (Frag.envUnit fragEnv) 1 else id) emptyExt
        r' = Frag.envFunRoot_inn fragEnv $ MkFunRoot keq (FragEQ b) r
  EquivalenceCt knd x -> fmap (fmap (pure . EquivalenceCt knd)) <$> Equivalence.simplify (envEquivalence env) knd x

-----

data Cache k subst t = MkCache {
    _apartness_table :: !(FM (t,t) ())
  ,
    _frag_subst :: !subst
  ,
    -- | INVARIANT: first component (i.e. root) of key is never nil
    --
    -- Use @<>@ of @(r,Just b)@ and @(r,Nothing)@.
    _multiplicity_table :: !(FM (t,Maybe t) CountInterval)
  }
  deriving (Eq,Show)

emptyCache :: Key t => subst -> Cache k subst t
emptyCache s = MkCache emptyFM s emptyFM

apartness_table :: Lens' (Cache k subst t) (FM (t,t) ())
apartness_table f cache = (\x -> cache{_apartness_table = x}) <$> f (_apartness_table cache)

frag_subst :: Lens' (Cache k subst t) subst
frag_subst f cache = (\x -> cache{_frag_subst = x}) <$> f (_frag_subst cache)

multiplicity_table :: Lens' (Cache k subst t) (FM (t,Maybe t) CountInterval)
multiplicity_table f cache = (\x -> cache{_multiplicity_table = x}) <$> f (_multiplicity_table cache)

-----

data CacheEnv k subst t v = MkCacheEnv{
    envEmptySubst :: !subst
  ,
    envExtendSubst :: !(v -> Frag t t -> subst -> subst)
  ,
    -- | INVARIANT: non-empty extension (TODO: or Fun root?)
    envLookup :: !(v -> subst -> Maybe (Frag t t))
  ,
    envNeedSwap :: !(v -> v -> Bool)
  ,
    -- | Remove free variables from the given set.
    envRemoveFVs :: !(FM v () -> t -> FM v ())
  ,
    envShow :: !(forall a. ((O.Outputable k,O.Outputable t,O.Outputable v) => a) -> a)
  ,
    envVar_out :: !(t -> Maybe v)
  }

-- | INVARIANT: the 'Ct' is the output of 'simplifyCt'.
extendCache :: (Key t,Key v) => CacheEnv k subst t v -> Env k t -> Cache k subst t -> Ct k t -> Cache k subst t
extendCache cacheEnv env = flip $ \case
  ApartnessCt (MkApartness pairsfm)
    | [(pair,())] <- toListFM pairsfm
    ->   -- Apart ('OneApart a b)
    over apartness_table $ alterFM pair $ \_ -> Just ()
    | otherwise -> id

  ClassCt _ (SetFrag fr)
    | Frag.envIsNil (envFrag env) r -> id
    | otherwise -> over multiplicity_table $ case Frag.envFunRoot_out (envFrag env) (fragRoot fr) of
    Just (MkFunRoot _ (FragEQ x) arg) ->
      insertFMS (arg,Just x) MkCountInterval{atLeast = shift,atMost = shift + 1}
      where
      shift = foldMap id $ unExt $ fragExt fr
    _ -> insertFMS (r,Nothing) MkCountInterval{atLeast = 0,atMost = 1}
    where
    r = Frag.envFrag_inn (envFrag env) fr
  ClassCt _ KnownFragZ{} -> id

  EquivalenceCt _ (MkFragEquivalence l r ext)
    | Frag.envIsNil (envFrag env) r
    , Just (MkFunRoot _ (FragEQ b) t) <- Frag.envFunRoot_out (envFrag env) l
    , not $ Frag.envIsNil (envFrag env) $   -- nothing to record if inner root is nil
        rawFragRoot $
          Frag.envRawFrag_out (envFrag env) t
    -> let  -- (FragEQ b t) 'Nil (:+ () :+ ())
      k = foldMap id (unExt ext)
      raw_fr = Frag.envRawFrag_out (envFrag env) t
      go pos neg = \case
        -- FragEQ a (p :- b) ~ 'Nil implies 0 <= p(a) and <= 1
        -- FragEQ a (q :- b :+ c) ~ 'Nil :+ '() :+ '() implies 1 <= q(a) <= 3
        NilRawExt -> MkCountInterval{
            atLeast = k - pos
          ,
            atMost = k + neg
          }
        ExtRawExt e Pos _ -> go (pos + 1) neg e
        ExtRawExt e Neg _ -> go pos (neg + 1) e
    in
    over multiplicity_table $ alterFM (rawFragRoot raw_fr,Just b) $ \_ ->
      Just $ go 0 0 (rawFragExt raw_fr)

    -- We skip this alternative if the extension is empty;
    -- we simply defer to GHC for such equivalences.
    | not (nullFM (unExt ext))
    , Just (v,swapped) <- getMapping_occursCheck
    ->
    over frag_subst $ envExtendSubst cacheEnv v $
      if swapped
      then MkFrag (invertSign ext) l
      else MkFrag ext r

    | otherwise -> id

    where
    getMapping_occursCheck = getMapping (vl >>= occursCheck r) (vr >>= occursCheck l)
      where
      vl = envVar_out cacheEnv l
      vr = envVar_out cacheEnv r

      passing0 = let add = maybe id (\v -> insertFMS v ()) in add vl $ add vr emptyFM
      removeFVs = envRemoveFVs cacheEnv
      passing_ext = foldlExt ext passing0 (\vs b count -> if 0 == count then vs else removeFVs vs b)

      -- it passes the occurs check if it is free in neither the extension nor the other root
      occursCheck other_root v = do
        guard $ Just () == lookupFM v (removeFVs passing_ext other_root)
        pure v

    -- x? ~ y? ...
    getMapping (Just vl) (Just vr) = Just $
      if envNeedSwap cacheEnv vl vr
      then (vr,True)
      else (vl,False)
    getMapping (Just vl) Nothing = Just (vl,False)
    getMapping Nothing (Just vr) = Just (vr,True)
    getMapping Nothing Nothing = Nothing

-----

-- | INVARIANT: 'True' if the 'Ct' has significantly changed from its @origin@.
--
-- /Significantly/ means
-- a class argument has been simplified,
-- a type family has been reduced,
-- a frag extension has been canonicalized,
-- a frag equivalence has been canonicalized,
-- or similar.
--
-- Notably, re-orienting an equivalence constraint is not itself significant,
-- because that would risk a loop
-- where GHC prefers one orientation and we prefer the other.
data WIP origin k t = MkWIP !(Maybe (origin,Bool)) !(Ct k t)
  deriving (Eq,Show)

instance (Key t,O.Outputable origin,O.Outputable k,O.Outputable t) => O.Outputable (WIP origin k t) where
  pprPrec _ (MkWIP prov ct) = O.text "MkWIP" O.<+> O.ppr prov O.<+> O.parens (O.ppr ct)

-- | INVARIANT: The 'Cache' reflects all of the 'WIP's.
data InertSet origin subst k t = MkInertSet
  ![WIP origin k t]
  !(Cache k subst t)
  deriving (Eq,Show)

extendInertSet ::
    (Key t,Key v,Monad m)
  =>
    CacheEnv k subst t v
  -> 
    Env k t
  -> 
    InertSet origin subst k t
  -> 
    [WIP origin k t]
  -> 
    AnyT m (Contra (Either (FM (t,t) (),[WIP origin k t]) (InertSet origin subst k t,Env k t)))
extendInertSet cacheEnv env0 (MkInertSet inerts0 cache0) = go inerts0 (toEnv cache0)
  where
  toEnv cache = let env = refineEnv cacheEnv env0 cache in cache `seq` env `seq` (cache,env)
  extend (cache,env) ct = toEnv (extendCache cacheEnv env cache ct)
  singleton ct = extend (toEnv cache0) ct

  go inerts (cache,env) = \case
    [] -> pure $ OK $ Right (MkInertSet inerts cache,env)
    new : worklist -> do
      -- apply the inert set to the new constraint
      let all_wips news' = inerts ++ NE.toList news' ++ worklist
      simplify_one cacheEnv env new all_wips $ \_ apartnesses (new'@(MkWIP _ ct') :| news') ->
        reevaluate_inerts (apartnesses ++ news' ++ worklist) [new'] (singleton ct') inerts

  reevaluate_inerts worklist inerts cache_env@(_,env) = \case
    [] -> go inerts cache_env worklist
    old : olds ->
      -- apply the new constraint to the previously inert item
      let all_wips olds' = inerts ++ NE.toList olds' ++ olds ++ worklist in
      simplify_one cacheEnv env old all_wips $ \changed' apartnesses (old'@(MkWIP _ ct') :| olds') ->
        let k x y z = reevaluate_inerts x y z olds in
        if changed' then
          -- since it changed, it might no longer be inert, so kickout onto the work list
          k (apartnesses ++ old':olds' ++ worklist) inerts cache_env
        else   -- NB not changed' implies olds' and apartnesses are both null
          k worklist (old:inerts) (extend cache_env ct')

simplify_one ::
    (Key t,Monad m)
  =>
    CacheEnv k subst t v
  ->
    Env k t
  ->
    WIP origin k t
  ->
    (NonEmpty (WIP origin k t) -> wips)
  ->
    (
      Bool
    ->
      [WIP origin k t]
    ->
      NonEmpty (WIP origin k t)
    ->
      AnyT m (Contra (Either (FM (t,t) (),wips) ans))
    )
  ->
    AnyT m (Contra (Either (FM (t,t) (),wips) ans))
simplify_one cacheEnv env (MkWIP origin ct) all_wips k = do
  printM $ O.text "simplify_one: " O.<+> show_ct cacheEnv ct
  (changed',x) <- listeningM $ simplifyCt env ct
  case x of
    Contradiction -> pure Contradiction   -- abort
    OK (derived,ct' :| cts')
      | not (nullFM eqs) -> do   -- yield new equivalence constraints to GHC
      printM $ O.text "new0: " O.<+> show_ct cacheEnv ct'
      flip mapM_ cts' $ \xxx -> printM $ O.text "new: " O.<+> show_ct cacheEnv xxx
      pure $ OK $ Left (eqs,all_wips wips')

      | otherwise -> do
        apartnesses <- mapM (fmap (MkWIP Nothing . ApartnessCt) . Apartness.interpret)
          [ MkRawApartness (pair :| []) | (pair,()) <- toListFM (dneqs derived) ]
        printM $ O.text "new0: " O.<+> show_ct cacheEnv ct'
        flip mapM_ cts' $ \xxx -> printM $ O.text "new: " O.<+> show_ct cacheEnv xxx
        k changed' apartnesses wips'
      where
      eqs = deqs derived
      wip' = MkWIP (fmap (|| changed') <$> origin) ct'
      wips' = wip' :| map (MkWIP Nothing) cts'

show_ct :: Key t => CacheEnv k subst t v -> Ct k t -> O.SDoc
show_ct cacheEnv = envShow cacheEnv O.ppr

-----

refineEnv :: Key t => CacheEnv k subst t v -> Env k t -> Cache k subst t -> Env k t
refineEnv cacheEnv env0 cache = MkEnv{
    envApartness = Apartness.MkEnv{
        Apartness.envTrivial = envTrivial
        ,
        Apartness.envTryUnify = envTryUnify
      }
  ,
    envClass = Class.MkEnv{
        Class.envEq = envIsEQ
      ,
        Class.envIsSet = envIsSet
      ,
        Class.envPassThru = fragEnv
      }
  ,
    envEquivalence = Equivalence.MkEnv{
        Equivalence.envEqR = envEqR
      ,
        Equivalence.envNeedSwap = envNeedSwapT
      ,
        Equivalence.envNotApart = envNotApart
      ,
        Equivalence.envMultiplicity = envMultiplicityF
      ,
        Equivalence.envPassThru = fragEnv
      }
  ,
    envFrag = fragEnv
  }
  where
  fragEnv = Frag.MkEnv{
      Frag.envFunRoot_inn = envFunRoot_inn
    ,
      Frag.envFunRoot_out = envFunRoot_out
    ,
      Frag.envIsEQ = envIsEQ
    ,
      Frag.envIsLT = envIsLT
    ,
      Frag.envIsNil = envIsNil
    ,
      Frag.envIsZBasis = envIsZBasis
    ,
      Frag.envMultiplicity = \x y -> envMultiplicityF x y >>= singletonInterval
    ,
      Frag.envNil = envNil
    ,
      Frag.envRawFrag_inn = envRawFrag_inn
    ,
      Frag.envRawFrag_out = envRawFrag_out
    ,
      Frag.envShow = \k -> Frag.envShow (envFrag env0) k
    ,
      Frag.envUnit = envUnit
    ,
      Frag.envZBasis = envZBasis
    ,
      Frag.debug = toListFM $ view multiplicity_table cache
    }

  -- unaffected by cache
  --
  -- they don't inspect @t@
  envRawFrag_inn = Frag.envRawFrag_inn (envFrag env0)
  envFunRoot_inn = Frag.envFunRoot_inn (envFrag env0)
  envNil = Frag.envNil (envFrag env0)
  envTrivial = Apartness.envTrivial (envApartness env0)
  envUnit = Frag.envUnit (envFrag env0)
  envZBasis = Frag.envZBasis (envFrag env0)

  -- unaffected by cache
  --
  -- GHC itself inlines @tv ~ 'Nil@ aggressively enough
  envIsNil = Frag.envIsNil (envFrag env0)

  -- unaffected by cache
  --
  -- Equivalence.simplify uses this function
  -- to recognize when an equivalence has one fun root and one nil root.
  -- So @FragEQ a b ~ t@ is only actionable if we also know that @t@ is nil-rooted.
  -- But in such a case, GHC or our plugin will have substituted for @t@.
  --
  -- Conclusion: we do not need to track @FragEQ a b ~ t@,
  -- because we track the other constraint needed to make that one actionable.
  envFunRoot_out = Frag.envFunRoot_out (envFrag env0)

  -- unaffected by cache
  --
  -- lower-level than everything in the cache
  envIsLT = Frag.envIsLT (envFrag env0)
  envIsZBasis = Frag.envIsZBasis (envFrag env0)
  envNeedSwapT = Equivalence.envNeedSwap (envEquivalence env0)

  envIsSet r =
      Class.envIsSet (envClass env0) r
    ||
      Just MkCountInterval{atLeast=0,atMost=1} == lookupFM (r,Nothing) (view multiplicity_table cache)

  -- unfold the root if it's in the frag_subst
  envRawFrag_out = go . Frag.envRawFrag_out (envFrag env0)
    where
    go raw_fr = maybe raw_fr go $ do
      v <- envVar_out cacheEnv (rawFragRoot raw_fr)
      fr <- envLookup cacheEnv v (view frag_subst cache)
      pure $ flattenRawFrag $ MkRawFrag (rawFragExt raw_fr) (forgetFrag fr)
  
  -- unify, checking smaller pairs against the apartness table
  --
  -- TODO should this handle frags specially?
  envTryUnify l r = case Apartness.envTryUnify (envApartness env0) l r of
    Nothing ->
      -- Apartness.envTryUnify env0 v1 v2 returns Nothing,
      -- but (v1,v2) might be in the apartness table.
      case lookupFM (f (l,r)) (view apartness_table cache) of
        Just () -> Just Apartness.UApart
        Nothing -> Nothing
    Just Apartness.UApart -> Just Apartness.UApart
    Just (Apartness.Unifiable pairs) -> go [] pairs
      where
      go acc = \case
        [] -> Just (Apartness.Unifiable acc)
        pair:pairs' -> case lookupFM (f pair) (view apartness_table cache) of
          Just () -> Just Apartness.UApart
          Nothing -> go (pair:acc) pairs'
    where
    f = snd . flip runAny mempty . uncurry Apartness.orientedPair

  -- call unify (a la tcUnifyTyWithTFs),
  -- then envRawFrag_out,
  -- and if the extension is non-empty, recur on both the elements and the roots
  envEqR l r = case envTryUnify l r of
    Just Apartness.UApart -> False
    Just (Apartness.Unifiable pairs) -> all (uncurry envEqR) pairs
    Nothing -> g lfr && g rfr && same (h lfr) (h rfr) && envEqR (fragRoot lfr) (fragRoot rfr)
      where
      lfr = f l
      rfr = f r
      f = snd . flip runAny mempty . Frag.interpret fragEnv
      g = not . nullFM . unExt . fragExt
      h = toListFM . unExt . fragExt
      same [] [] = True
      same ((x,xc):xs) ((y,yc):ys) = xc == yc && same xs ys && envEqR x y
      same _ _ = False

  envNotApart l r = case envTryUnify l r of
    Just Apartness.UApart -> False
    _ -> True

  envIsEQ l r = case envTryUnify l r of
    Just Apartness.UApart -> Just False
    Just (Apartness.Unifiable []) -> Just True
    Just (Apartness.Unifiable (_:_)) -> Nothing
    Nothing -> Nothing

  envMultiplicityF r b
    | envIsNil r = Just $ MkCountInterval 0 0
    | otherwise = case lookupFM r $ unTuple2FM $ view multiplicity_table cache of
    Nothing -> Nothing
    Just (MkMaybeFM mb fm) -> mb <> lookupFM b fm
