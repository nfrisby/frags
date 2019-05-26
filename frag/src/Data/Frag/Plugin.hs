{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin (plugin,tcPlugin) where

import qualified Class as GhcPlugins
import Data.Either (partitionEithers)
import Data.Maybe (catMaybes)
import Data.Monoid (Any(..),Ap(..))
import Data.Traversable (forM)
import qualified GhcPlugins
import Outputable ((<+>),ppr,text)
import qualified Outputable as O
import TcEvidence (EvTerm(EvExpr))
import qualified TcMType as TcM
import TcPluginM (TcPluginM,newDerived,newGiven,newWanted,zonkTcType)
import TcRnMonad (unsafeTcPluginTcM)
import TcRnTypes (Ct(..),CtEvidence,CtLoc,TcPlugin(..),TcPluginResult(..),TcPluginSolver,ctEvExpr,ctEvidence,ctLoc,ctPred,mkNonCanonical)
import TcType (TcKind,TcTyVar,TcType)
import TcUnify (OccCheckResult(..),canSolveByUnification,occCheckForErrors)
import TyCoRep (Type(..))

import Data.Frag.Plugin.Evidence (Flavor(..),PluginResult(..),contraPR,discardGivenPR,fiatco,fiatcastev,newPR,pluginResult,solveWantedPR)
import qualified Data.Frag.Plugin.Fsk as Fsk
import qualified Data.Frag.Plugin.GHCType as GHCType
import qualified Data.Frag.Plugin.Lookups as Lookups
import Data.Frag.Plugin.Lookups (E,piTrace)
import qualified Data.Frag.Plugin.Parse as Parse
import qualified Data.Frag.Simpl.Frag as Frag
import qualified Data.Frag.Simpl.InertSet as InertSet
import qualified Data.Frag.Simpl.Types as Types

-- | A typechecker plugin that implements the special semantics for the "Data.Frag" module.
plugin :: GhcPlugins.Plugin
plugin = GhcPlugins.defaultPlugin{
    GhcPlugins.pluginRecompile = GhcPlugins.purePlugin
  ,
    GhcPlugins.tcPlugin = pure . tcPlugin
  }

-- | Perhaps other plugins can extend this one.
tcPlugin :: [String] -> TcPlugin
tcPlugin opts = TcPlugin{
    tcPluginInit = initialize opts
  ,
    tcPluginSolve = \env gs ds ws -> do
      lvl <- Lookups.getTcLevel
      solve env{Lookups.levelE = lvl} gs ds ws
  ,
    tcPluginStop = stop
  }

-----

initialize :: [String] -> TcPluginM E
initialize opts = Lookups.lookups
  ("trace" `elem` opts)

solve :: E -> TcPluginSolver
solve env givens derivs wanteds = do
  piTrace env $ text "FRAGPLUGIN"
  if null derivs && null wanteds
    then simplifyG env givens
    else simplifyW env givens derivs wanteds

stop :: E -> TcPluginM ()
stop _ = pure ()

runWork :: E -> Types.WorkT TcPluginM a -> TcPluginM (Any,a)
-- runWork _env m = Types.runWorkT m (\_ -> pure ()) mempty
runWork env m = Types.runWorkT m (piTrace env) mempty

simplifyG :: E -> [Ct] -> TcPluginM TcPluginResult
simplifyG env gs0 = do
  piTrace env $ text "-----------"

  let
    (unflat,_gs0',gs) = Fsk.collate_fsks env gs0

  piTrace env $ text "simplifyG Unflat" <+> ppr unflat
  piTrace env $ text "simplifyG gs" <+> ppr gs

  (gs1,wips) <- fmap partitionEithers $ forM gs $ \g ->
      maybe (Left g) Right
    <$>
      Parse.mkWIP (runWork env) env unflat g
  piTrace env $ text "simplifyG wips" <+> ppr wips

  (_,dgres) <- (runWork env) $ InertSet.extendInertSet GHCType.cacheEnv (GHCType.ghcTypeEnv env unflat) (InertSet.MkInertSet [] (InertSet.emptyCache Types.emptyFM)) wips
  x <- case dgres of
    Types.Contradiction -> do
      piTrace env $ text "simplifyG contradiction"
      pure $ foldMap contraPR gs 
    Types.OK (Left (deqs,wips')) -> do
      piTrace env $ text "simplifyG deqs" <+> ppr (Types.toListFM deqs,wips')
      pr1 <- okGivenWIPs env wips'
      pr2 <- getAp $ Types.foldMapFM (\(l,r) () -> Ap (deqGiven (ctLoc (head gs)) l r)) deqs   -- TODO fix ctLoc
      pure $ pr1 <> pr2
    Types.OK (Right (InertSet.MkInertSet wips' cache,isetEnv')) -> do
      piTrace env $
          (text "G given aparts" <+> ppr (Types.toListFM $ Types.view InertSet.apartness_table cache))
        O.$$
          (text "G given subst" <+> ppr (Types.toListFM $ Types.view InertSet.frag_subst cache))
        O.$$
          (text "G given mult" <+> ppr (Types.toListFM $ Types.view InertSet.multiplicity_table cache))

      pr1 <- okGivenWIPs env wips'
      pr2 <- normalizeOthers env updGiven unflat (InertSet.envFrag isetEnv') gs1
      pure $ pr1 <> pr2

  y <- pluginResult env Given x
  case y of
    TcPluginOk l r -> do
      piTrace env $ text "OUTPUT" <+> ppr (l,r)
    _ -> pure ()
  pure y

deqGiven :: CtLoc -> TcType -> TcType -> TcPluginM PluginResult
deqGiven loc l r =
    (newPR . mkNonCanonical)
  <$>
    newGiven loc (GhcPlugins.mkPrimEqPred l r) (GhcPlugins.Coercion (fiatco l r))

updGiven :: Ct -> TcType -> (CtEvidence -> Ct) -> TcPluginM PluginResult
updGiven ct r mk_ct' = do
  let
    l = ctPred ct
  ctev <- newGiven (ctLoc ct) (ctPred ct) $ fiatcastev l r (ctEvExpr (ctEvidence ct))
  pure $ newPR (mk_ct' ctev) <> discardGivenPR ct

okGivenWIPs :: E -> [InertSet.WIP Ct TcKind TcType] -> TcPluginM PluginResult
okGivenWIPs env wips = do
  let
    news = [ ct | InertSet.MkWIP Nothing ct <- wips ]
    olds = [ (o,ct) | InertSet.MkWIP (Just (o,True)) ct <- wips ]
  piTrace env $ text "okGivenWIPs new" <+> ppr news
  piTrace env $ text "okGivenWIPs olds" <+> ppr olds

  olds' <- fmap mconcat $ forM olds $ \(o,ct) -> do
    let
      (_massignment,predty,f) = GHCType.ct_inn env ct
    ctev <- newGiven (ctLoc o) predty $ f (GHCType.UpdGiven (ctPred o) (ctEvExpr (ctEvidence o)))   -- TODO fix ctLoc level
    pure $ newPR (mkNonCanonical ctev) <> discardGivenPR o

  news' <- fmap mconcat $ forM news $ \ct -> do
    let
      o = fst (head olds)   -- TODO fix ctLoc
      uty = GhcPlugins.mkTyConTy GhcPlugins.unitTyCon
      (ty,ev) = case ct of
        InertSet.ApartnessCt{} -> (uty,GhcPlugins.mkCoreVarTup [])
        InertSet.ClassCt k Types.KnownFragZ{} -> (
            Lookups.knownFragZTC env `GhcPlugins.mkTyConApp` [k,fr]
          ,
            to_class $ GhcPlugins.Var (Lookups.unsafeProxyIntId env) `GhcPlugins.mkCoreApps` [GhcPlugins.mkTyArg k]
          )
          where
          fr = GhcPlugins.promoteDataCon (Lookups.fragNilDC env) `GhcPlugins.mkTyConApp` [k]
          coax = Lookups.knownFragZCoax env
          to_class = flip GhcPlugins.Cast $ GhcPlugins.mkUnbranchedAxInstCo GhcPlugins.Representational coax [k,fr] []
        InertSet.ClassCt _ Types.SetFrag{} -> (GhcPlugins.mkPrimEqPred uty uty,GhcPlugins.Coercion $ GhcPlugins.mkNomReflCo uty)
        InertSet.EquivalenceCt{} -> (GhcPlugins.mkPrimEqPred uty uty,GhcPlugins.Coercion $ GhcPlugins.mkNomReflCo uty)
      (_massignment,predty,f) = GHCType.ct_inn env ct
    fmap (newPR . mkNonCanonical) $ newGiven (ctLoc o) predty $ f (GHCType.UpdGiven ty ev)   -- TODO fix ctLoc level

  pure $ olds' <> news'

simplifyW :: E -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
simplifyW env gs0 ds ws = do
  piTrace env $ text "-----------"
  piTrace env $ text "simplifyW {"

  let
    (unflat,_gs0',gs) = Fsk.collate_fsks env gs0

  piTrace env $ text "simplifyW Unflat" <+> ppr unflat
  piTrace env $ text "simplifyW gs" <+> ppr gs
  piTrace env $ text "simplifyW ds" <+> ppr ds
  piTrace env $ text "simplifyW ws" <+> ppr ws

  gwips <- catMaybes <$> mapM (Parse.mkWIP (runWork env) env unflat) gs
  piTrace env $ text "simplifyW gwips" <+> ppr gwips

  (_,dgres) <- (runWork env) $ InertSet.extendInertSet GHCType.cacheEnv (GHCType.ghcTypeEnv env unflat) (InertSet.MkInertSet [] (InertSet.emptyCache Types.emptyFM)) gwips
  mgres <- case dgres of
    Types.Contradiction -> do
      piTrace env $ text "given contradiction (UNEXPECTED)"
      pure Nothing
    Types.OK (Left (deqs,_gwips')) -> do
      piTrace env $ text "given deqs (UNEXPECTED)" <+> ppr (Types.toListFM deqs)
      pure Nothing
    Types.OK (Right (InertSet.MkInertSet _ cache,env')) -> do
      piTrace env $
          (text "W given aparts" <+> ppr (Types.toListFM $ Types.view InertSet.apartness_table cache))
        O.$$
          (text "W given subst" <+> ppr (Types.toListFM $ Types.view InertSet.frag_subst cache))
        O.$$
          (text "W given mult" <+> ppr (Types.toListFM $ Types.view InertSet.multiplicity_table cache))
      pure $ Just (cache,env')

  (ds1,dwips) <- fmap partitionEithers $ forM ds $ \d ->
      maybe (Left d) Right
    <$>
      Parse.mkWIP (runWork env) env unflat d
  piTrace env $ text "simplifyW ds" <+> ppr ds
  piTrace env $ text "simplifyW dwips" <+> ppr dwips

  dx <- case mgres of
    Just (cache,isetEnv) -> do
      (_,ddres) <- (runWork env) $ InertSet.extendInertSet GHCType.cacheEnv isetEnv (InertSet.MkInertSet [] cache) dwips
      case ddres of
        Types.Contradiction -> do
          piTrace env $ text "simplifyW ds contradiction"
          pure $ foldMap contraPR ds
        Types.OK (Left (deqs,dwips')) -> do
          -- TODO do need these "deriveds" really need to be treated differently?
          piTrace env $ text "simplifyW deqs" <+> ppr (Types.toListFM deqs) O.$$ ppr dwips'
          pr1 <- okDerivedWIPs env dwips'
          pr2 <- getAp $ Types.foldMapFM (\(l,r) () -> Ap (deqDerived (ctLoc (head ws)) l r)) deqs   -- TODO fix ctLoc
          pure $ pr1 <> pr2
        Types.OK (Right (InertSet.MkInertSet dwips' _,env')) -> do
          piTrace env $ text "simplifyW ds good" <+> ppr dwips' <+> ppr ds1
          pr1 <- okDerivedWIPs env dwips'
          pr2 <- normalizeOthers env updDerived unflat (InertSet.envFrag env') ds1
          pure $ pr1 <> pr2
    Nothing -> pure mempty -- the wwips will handle the gs

  (ws1,wwips) <- fmap partitionEithers $ forM ws $ \w ->
      maybe (Left w) Right
    <$>
      Parse.mkWIP (runWork env) env unflat w
  piTrace env $ text "simplifyW ws" <+> ppr ws
  piTrace env $ text "simplifyW wwips" <+> ppr wwips

  wx <- case mgres of
    Just (cache,isetEnv) -> do
      (_,dwres) <- (runWork env) $ InertSet.applyInertSet GHCType.cacheEnv isetEnv (InertSet.MkInertSet [] cache) wwips
      case dwres of
        Types.Contradiction -> do
          piTrace env $ text "simplifyW contradiction"
          pure $ foldMap contraPR ws
        Types.OK (Left (deqs,wwips')) -> do
          -- TODO do need these "deriveds" really need to be treated differently?
          piTrace env $ text "simplifyW deqs" <+> ppr (Types.toListFM deqs) O.$$ ppr wwips'
          pr1 <- okWantedWIPs env wwips'
          pr2 <- getAp $ Types.foldMapFM (\(l,r) () -> Ap (deqWanted (ctLoc (head ws)) l r)) deqs   -- TODO fix ctLoc
          pure $ pr1 <> pr2
        Types.OK (Right wwips') -> do
          piTrace env $ text "simplifyW good" <+> ppr wwips' <+> ppr ws1
          pr1 <- okWantedWIPs env wwips'
          pr2 <- normalizeOthers env updWanted unflat (InertSet.envFrag isetEnv) ws1
          pure $ pr1 <> pr2
    Nothing -> pure $ foldMap contraPR gs

  piTrace env $ text "simplifyW pluginResult {"

  x <- pluginResult env Wanted $ dx <> wx
  piTrace env $ text "} simplifyW pluginResult"
  case x of
    TcPluginOk l r -> do
      piTrace env $ O.hang (text "OUTPUT SOLVED") 4 $ O.vcat (map ppr l)
      piTrace env $ O.hang (text "OUTPUT NEW") 4 $ O.vcat (map ppr r)
    _ -> pure ()
  piTrace env $ text "} simplifyW"
  pure x

deqDerived :: CtLoc -> TcType -> TcType -> TcPluginM PluginResult
deqDerived loc l r = (newPR . mkNonCanonical) <$> newDerived loc (GhcPlugins.mkPrimEqPred l r)

updDerived :: Ct -> TcType -> (CtEvidence -> Ct) -> TcPluginM PluginResult
updDerived ct r mk_ct' = do
  ctev <- newDerived (ctLoc ct) r   -- TODO fix ctLoc level
  pure $ newPR (mk_ct' ctev) <> discardGivenPR ct

okDerivedWIPs :: E -> [InertSet.WIP Ct TcKind TcType] -> TcPluginM PluginResult
okDerivedWIPs env wips = do
  let
    news = [ ct | InertSet.MkWIP Nothing ct <- wips ]
    olds = [ (o,ct) | InertSet.MkWIP (Just (o,True)) ct <- wips ]
  piTrace env $ text "okDerivedWIPs new" <+> ppr news
  piTrace env $ text "okDerivedWIPs olds" <+> ppr olds

  let

  olds' <- fmap mconcat $ forM olds $ \(o,ct) -> do
    let
      (massignment,predty,_) = GHCType.ct_inn env ct
    mapM_ (doAssign env) massignment
    ctev <- newDerived (ctLoc o) predty   -- TODO fix ctLoc level
    pure $ newPR (mkNonCanonical ctev) <> discardGivenPR o

  news' <- fmap mconcat $ forM news $ \ct -> do
    let
      o = fst (head olds)
      (massignment,predty,_) = GHCType.ct_inn env ct
    mapM_ (doAssign env) massignment
    ctev <- newDerived (ctLoc o) predty   -- TODO fix ctLoc level
    pure $ newPR (mkNonCanonical ctev)

  pure $ olds' <> news'

deqWanted :: CtLoc -> TcType -> TcType -> TcPluginM PluginResult
deqWanted loc l r = (newPR . mkNonCanonical) <$> newDerived loc (GhcPlugins.mkPrimEqPred l r)

updWanted :: Ct -> TcType -> (CtEvidence -> Ct) -> TcPluginM PluginResult
updWanted ct r mk_ct' = do
  let
    l = ctPred ct
  ctev <- newWanted (ctLoc ct) r   -- TODO fix ctLoc level
  pure $ newPR (mk_ct' ctev) <> solveWantedPR ct (EvExpr (fiatcastev r l (ctEvExpr ctev)))

okWantedWIPs :: E -> [InertSet.WIP Ct TcKind TcType] -> TcPluginM PluginResult
okWantedWIPs env wips = do
  let
    news = [ ct | InertSet.MkWIP Nothing ct <- wips ]
    olds = [ (o,ct) | InertSet.MkWIP (Just (o,True)) ct <- wips ]
  piTrace env $ text "okWantedWIPs new" <+> ppr news
  piTrace env $ text "okWantedWIPs olds" <+> ppr olds

  olds' <- fmap mconcat $ forM olds $ \(o,ct) -> do
    let
      (massignment,predty,f) = GHCType.ct_inn env ct
    mapM_ (doAssign env) massignment
    ctev <- newWanted (ctLoc o) predty   -- TODO fix ctLoc level
    pure $ newPR (mkNonCanonical ctev) <> solveWantedPR o (EvExpr (f (GHCType.UpdWanted (ctPred o) (ctEvExpr ctev))))

  news' <- fmap mconcat $ forM news $ \ct -> do
    let
      o = fst (head olds)
      (massignment,predty,_) = GHCType.ct_inn env ct
    mapM_ (doAssign env) massignment
    ctev <- newWanted (ctLoc o) predty   -- TODO fix ctLoc level
    pure $ newPR (mkNonCanonical ctev)

  pure $ olds' <> news'

-----

-- | reduce frag-related types within a constraint
normalizeOthers ::
    Monoid m
  =>
    E
  ->
    (Ct -> TcType -> (CtEvidence -> Ct) -> TcPluginM m)
    -- ^ how to update a constraint if we change its type
  ->
    Fsk.Unflat
  ->
    Frag.Env TcKind TcType TcType
  ->
    [Ct]
  ->
    TcPluginM m
normalizeOthers env upd unflat fragEnv cts = fmap mconcat $ forM cts $ \ct -> case ct of
  CDictCan _ cls xis pending_sc -> do
    (Any hit,xis') <- runWork env $ mapM (reduce env unflat fragEnv) xis
    if not hit then pure mempty else do
    let
      r = GhcPlugins.classTyCon cls `GhcPlugins.mkTyConApp` xis'
    upd ct r $ \ev -> CDictCan ev cls xis' pending_sc

  _ -> pure mempty

-- | reduce a frag-related type in all subterms of a type
reduce ::
    E
  ->
    Fsk.Unflat
  ->
    Frag.Env TcKind TcType TcType
  ->
    TcType
  ->
    Types.WorkT TcPluginM TcType
reduce env unflat fragEnv = go
  where
  go xi0 = do  -- reduce
    xi1 <- reducePop env unflat fragEnv xi0

    -- reduce a frag on the way in (top-down)
    fr <- Types.forgetFrag <$> Frag.interpret fragEnv xi1
    (hit,xi2) <- Types.listeningM $ fmap (Frag.envRawFrag_inn fragEnv) $ Types.MkRawFrag <$>
        traverse go (Types.rawFragExt fr)
      <*>
        go_subterms (Types.rawFragRoot fr)
    -- reduce a frag on the way out (bottom-up)
    xi3 <- if not hit then pure xi2 else do
      Frag.envFrag_inn fragEnv <$> Frag.interpret fragEnv xi2

    let
      _ = fr :: Types.RawFrag TcType TcType
      _ = [xi0,xi1,xi2,xi3] :: [TcType]

    pure xi3

  go_subterms xi
    | Just xi' <- GhcPlugins.tcView xi = go_subterms xi'
    | otherwise = case xi of
   FunTy dom cod -> FunTy <$> go dom <*> go cod
   TyConApp tc xis -> TyConApp tc <$> mapM go xis
--   CastTy xi co -> undefined   -- TODO update coercion for changes in xi; also make (some?) changes in coercion?
   _ -> pure xi

-- | reduce an application of FragPop_NonDet
reducePop ::
    Monad m
  =>
    E
  ->
    Fsk.Unflat
  ->
    Frag.Env TcKind TcType TcType
  ->
    TcType
  ->
    Types.WorkT m TcType
reducePop env unflat fragEnv xi = case GhcPlugins.tcSplitTyConApp_maybe (Fsk.unflatten unflat xi) of
  Just (tc,[k,fr])
    | tc == Lookups.fragPopTC env -> go xi k fr
  _ -> pure xi
  where
  go ty k fr = Frag.reducePop fragEnv fr >>= \case
    Just ext -> let
      nil = GhcPlugins.promoteDataCon (Lookups.fragNothingPopDC env) `GhcPlugins.mkTyConApp` [k]
      ty' = Types.foldlExt ext nil $ \acc b count -> if 0 == count then acc else
        GhcPlugins.promoteDataCon (Lookups.fragJustPopDC env) `GhcPlugins.mkTyConApp` [
            k
          ,
            Lookups.fragPushTC env `GhcPlugins.mkTyConApp` [k,acc]
          ,
            b
          ,
            Frag.envFrag_inn fragEnv $
            flip Types.MkFrag (Frag.envNil fragEnv (Frag.envZBasis fragEnv)) $
            Types.insertExt (Frag.envUnit fragEnv) count Types.emptyExt
          ]
      in
      pure ty'
    _ -> pure ty

-----

-- | Variant of TcUnify.metaTyVarUpdateOK that doesn't avoid type families.
-- (It doesn't avoid them *at all*, but really it should just not avoid :+ and :-.)
metaTyVarUpdateOK :: GhcPlugins.DynFlags -> TcTyVar -> TcType -> Maybe TcType
metaTyVarUpdateOK dflags tv ty =
  case occCheckForErrors dflags tv ty of
    OC_OK{} -> Just ty
    OC_Bad -> Nothing
    OC_Occurs -> Nothing

doAssign :: E -> (TcTyVar,TcType) -> TcPluginM ()
doAssign env (tv,ty0) = do
  let
    touchable_etc = canSolveByUnification lvl tv ty0
  bounce "untouchable_etc" ty0 touchable_etc $ do
    unfilled <- unsafeTcPluginTcM $ TcM.isUnfilledMetaTyVar tv
    bounce "filled" ty0 unfilled $ do
      ty1 <- zonkTcType ty0
      case metaTyVarUpdateOK (Lookups.dynFlags0 env) tv ty1 of
        Just ty2 -> do
          piTrace env $ text "ASSIGNING " <+> ppr tv <+> ppr ty2
          unsafeTcPluginTcM $ TcM.writeMetaTyVar tv ty2
        Nothing -> nope "occCheck" ty1

  where
  lvl = Lookups.levelE env

  bounce s ty b m = if b then m else nope s ty

  nope s ty =
    piTrace env $ text "NOT ASSIGNING " <+> ppr lvl <+> text s <+> ppr tv <+> ppr ty
