{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}

module Data.Frag.Simpl.InertSet (
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

import qualified Data.Frag.Simpl.Apartness as Apartness
import qualified Data.Frag.Simpl.Class as Class
import qualified Data.Frag.Simpl.Equivalence as Equivalence
import qualified Data.Frag.Simpl.Frag as Frag
import Data.Frag.Simpl.Types

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

simplifyCt :: (Key t,Monad m) => Env k t -> Ct k t -> WorkT m (Contra (Derived t t,NonEmpty (Ct k t)))
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
        r' = Frag.envFunRoot_inn fragEnv $ MkFunRoot (FragEQ keq b) r
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
    Just (MkFunRoot (FragEQ _ x) arg) ->
      -- SetFrag (FragEQ a q :+ shift)    0 <= q(a) + shift <= 1       -shift <= q(a) <= -shift+1
      insertFMS (arg,Just x) MkCountInterval{atLeast = ishift,atMost = ishift + 1}
      where
      ishift = invertSign $ foldMap id $ unExt $ fragExt fr
    _ -> insertFMS (r,Nothing) MkCountInterval{atLeast = 0,atMost = 1}
    where
    r = Frag.envFrag_inn (envFrag env) fr
  ClassCt _ KnownFragZ{} -> id

  EquivalenceCt _ (MkFragEquivalence l r ext)
    | Frag.envIsNil (envFrag env) r
    , Just (MkFunRoot (FragEQ _ b) t) <- Frag.envFunRoot_out (envFrag env) l
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
    | not (nullExt ext)
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
    WorkT m (Contra (Either (FM (t,t) (),[WIP origin k t]) (InertSet origin subst k t,Env k t)))
extendInertSet cacheEnv env0 (MkInertSet inerts0 cache0) =
  \wips -> do
    let
      iinerts0 = zip [0..] inerts0
      iwips = zip [length inerts0..] wips
    printM $ O.text "extendInertSet"
      O.$$ envShow cacheEnv (O.vcat [ O.ppr (MkI i,ct) | (i,MkWIP _ ct) <- iinerts0])
      O.$$ O.text "---"
      O.$$ envShow cacheEnv (O.vcat [ O.ppr (MkI i,ct) | (i,MkWIP _ ct) <- iwips])
    go (length inerts0 + length wips) iinerts0 (toEnv cache0) iwips
  where
  toEnv cache = let env = refineEnv cacheEnv env0 cache in cache `seq` env `seq` (cache,env)
  extend (cache,env) ct = toEnv (extendCache cacheEnv env cache ct)
  singleton ct = extend (toEnv cache0) ct

  go next inerts (cache,env) = \case
    [] -> do
      printM $ O.text "done:" O.<+> O.vcat [ show_ct cacheEnv ct | (_,MkWIP _ ct) <- inerts ]
      pure $ OK $ Right (MkInertSet (map snd inerts) cache,env)
    new : worklist -> do
      -- apply the inert set to the new constraint
      let all_wips news' = map snd inerts ++ NE.toList news' ++ map snd worklist
      simplify_one next cacheEnv env new all_wips $ \next' _ apartnesses (new'@(_,MkWIP _ ct') :| news') -> do
        printM $ O.text "restarting" O.<+> show_ct cacheEnv ct'
        reevaluate_inerts next' (apartnesses ++ news' ++ worklist) [new'] (singleton ct') inerts

  reevaluate_inerts next worklist inerts cache_env@(_,env) = \case
    [] -> go next inerts cache_env worklist
    old@(ident,_) : olds ->
      -- apply the new constraint to the previously inert item
      let all_wips olds' = map snd inerts ++ NE.toList olds' ++ map snd olds ++ map snd worklist in
      simplify_one next cacheEnv env old all_wips $ \next' changed' apartnesses (old'@(_,MkWIP _ ct') :| olds') ->
        let k x y z = reevaluate_inerts next' x y z olds in
        if changed' then do
          printM $ O.text "kickout" O.<+> O.ppr (MkI ident)
          -- since it changed, it might no longer be inert, so kickout onto the work list
          k (apartnesses ++ old':olds' ++ worklist) inerts cache_env
        else do   -- NB not changed' implies olds' and apartnesses are both null
          printM $ O.text "extended" O.<+> O.ppr (MkI ident)
          k worklist (old:inerts) (extend cache_env ct')

newtype I = MkI Int
instance Show I where show (MkI i) = "(" ++ show i ++ ")"
instance O.Outputable I where ppr = O.text . show

simplify_one ::
    (Key t,Monad m)
  =>
    Int
  ->
    CacheEnv k subst t v
  ->
    Env k t
  ->
    (Int,WIP origin k t)
  ->
    (NonEmpty (WIP origin k t) -> wips)
  ->
    (
      Int
    ->
      Bool
    ->
      [(Int,WIP origin k t)]
    ->
      NonEmpty (Int,WIP origin k t)
    ->
      WorkT m (Contra (Either (FM (t,t) (),wips) ans))
    )
  ->
    WorkT m (Contra (Either (FM (t,t) (),wips) ans))
simplify_one next cacheEnv env (ident,MkWIP origin ct) all_wips k = do
  printM $ O.text "=== simplify_one {" O.<+> O.ppr (MkI ident) O.<> O.text ":" O.<+> show_ct cacheEnv ct
  (changed',x) <- listeningM $ simplifyCt env ct
  case x of
    Contradiction -> do
      printM $ O.text "=== simplify_one contradiction" O.<+> O.ppr (MkI ident)
      pure Contradiction   -- abort
    OK (derived,ct' :| cts')
      | not (nullFM eqs) -> do   -- yield new equivalence constraints to GHC
      dump
      printM $ O.text "=== simplify_one yielding" O.<+> O.ppr (MkI ident)
      pure $ OK $ Left (eqs,all_wips $ fmap snd wips')

      | otherwise -> do
      dump
      apartnesses <- mapM (fmap (MkWIP Nothing . ApartnessCt) . Apartness.interpret)
        [ MkRawApartness (pair :| []) | (pair,()) <- toListFM (dneqs derived) ]
      k next' changed' (iaparts `zip` apartnesses) wips'
      where
      next' = if changed' then next + 1 + length (dneqs derived) + length cts' else next
      ident' = if changed' then next else ident
      iaparts = [(next + 1 + length cts')..]
      eqs = deqs derived
      wip' = MkWIP (fmap (|| changed') <$> origin) ct'
      wips' = (ident',wip') :| ([next+1..] `zip` map (MkWIP Nothing) cts')

      dump =  do
        printM $ O.text "=== simplify_one }" O.<+> O.ppr (MkI ident) O.<> O.text ":" O.<+> O.ppr changed' O.<+> O.text ("to " ++ show (map MkI [next..next'-1]))
          O.$$ show_ct cacheEnv ct
          O.$$ envShow cacheEnv (O.vcat [ O.ppr (MkI i,xxx) | (i,MkWIP _ xxx) <- NE.toList wips'])
          O.$$ envShow cacheEnv (O.vcat [ O.ppr (MkI i,l,r) | (i,((l,r),())) <- iaparts `zip` toListFM (dneqs derived)])

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
      Frag.envMappingBasis = envMappingBasis
    ,
      Frag.envMapsTo_out = envMapsTo_out
    ,
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
      Frag.envPush_out = envPush_out
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
  envMappingBasis = Frag.envMappingBasis (envFrag env0)
  envMapsTo_out = Frag.envMapsTo_out (envFrag env0)
  envRawFrag_inn = Frag.envRawFrag_inn (envFrag env0)
  envFunRoot_inn = Frag.envFunRoot_inn (envFrag env0)
  envPush_out = Frag.envPush_out (envFrag env0)
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
    f = snd . flip runWork mempty . uncurry Apartness.orientedPair

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
      f = snd . flip runWork mempty . Frag.interpret fragEnv
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

    | Just (dom,cod,key,_val) <- envMapsTo_out b = let
        intrval1 = generic r b
        intrval2 = generic (envFunRoot_inn $ MkFunRoot (FragDom dom cod) r) key
        in        
        case (intrval1,intrval2) of    -- p(k := v) <= (DomFrag p)(k)
          (Just i1,Just i2) -> Just $ i1{atMost = atMost (i1 <> i2)}
          (Nothing,Just i2) -> if atLeast i2 == atMost i2 then Just i2 else Nothing
          (Just i1,Nothing) -> Just i1
          (Nothing,Nothing) -> Nothing

    | otherwise = generic r b
    where
    generic r' b' = case lookupFM r' $ unTuple2FM $ view multiplicity_table cache of
      Nothing -> Nothing
      Just (MkMaybeFM mb fm) -> mb <> lookupFM b' fm
