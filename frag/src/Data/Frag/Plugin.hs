{-# LANGUAGE LambdaCase #-}

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
import TcPluginM (TcPluginM,newDerived,newGiven,newWanted)
import TcRnTypes (Ct(..),CtEvidence,CtLoc,TcPlugin(..),TcPluginResult(..),TcPluginSolver,ctEvExpr,ctEvidence,ctLoc,ctPred,mkNonCanonical)
import TcType (TcKind,TcType)

import qualified Data.Frag.Plugin.Frag as Frag
import qualified Data.Frag.Plugin.GHCType as GHCType
import qualified Data.Frag.Plugin.InertSet as InertSet
import Data.Frag.Plugin.GHCType.Evidence (Flavor(..),PluginResult(..),contraPR,discardGivenPR,fiatco,fiatcastev,newPR,pluginResult,solveWantedPR)
import qualified Data.Frag.Plugin.GHCType.Fsk as Fsk
import qualified Data.Frag.Plugin.GHCType.Parse as Parse
import qualified Data.Frag.Plugin.Lookups as Lookups
import Data.Frag.Plugin.Lookups (E,piTrace)
import qualified Data.Frag.Plugin.Types as Types

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
    tcPluginSolve = solve
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

runAny :: E -> Types.AnyT TcPluginM a -> TcPluginM (Any,a)
runAny _env m = Types.runAnyT m (\_ -> pure ()) mempty
-- runAny env m = Types.runAnyT m (piTrace env) mempty

simplifyG :: E -> [Ct] -> TcPluginM TcPluginResult
simplifyG env gs0 = do
  piTrace env $ text "-----------"

  let
    (unflat,gs) = Fsk.collate_fsks env gs0

  piTrace env $ text "simplifyG Unflat" <+> ppr unflat
  piTrace env $ text "simplifyG gs" <+> ppr gs

  (gs1,wips) <- fmap partitionEithers $ forM gs $ \g ->
      maybe (Left g) Right
    <$>
      Parse.mkWIP (runAny env) env unflat g
  piTrace env $ text "simplifyG wips" <+> ppr wips

  (_,dgres) <- (runAny env) $ InertSet.extendInertSet GHCType.cacheEnv (GHCType.ghcTypeEnv env unflat) (InertSet.MkInertSet [] (InertSet.emptyCache Types.emptyFM)) wips
  x <- case dgres of
    Types.Contradiction -> do
      piTrace env $ text "simplifyG contradiction"
      pure $ foldMap contraPR gs 
    Types.OK (Left (deqs,wips')) -> do
      piTrace env $ text "simplifyG deqs" <+> ppr (Types.toListFM deqs,wips')
      pr1 <- okGivenWIPs env wips'
      pr2 <- getAp $ Types.foldMapFM (\(l,r) () -> Ap (deqGiven (ctLoc (head gs)) l r)) deqs   -- TODO fix ctLoc
      pure $ pr1 <> pr2
    Types.OK (Right (InertSet.MkInertSet wips' _,isetEnv')) -> do
      pr1 <- okGivenWIPs env wips'
      pr2 <- popReductions env updGiven unflat (InertSet.envFrag isetEnv') gs1
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
      (predty,f) = GHCType.ct_inn env ct
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
        _ -> (GhcPlugins.mkPrimEqPred uty uty,GhcPlugins.Coercion $ GhcPlugins.mkNomReflCo uty)
      (predty,f) = GHCType.ct_inn env ct
    fmap (newPR . mkNonCanonical) $ newGiven (ctLoc o) predty $ f (GHCType.UpdGiven ty ev)   -- TODO fix ctLoc level

  pure $ olds' <> news'

simplifyW :: E -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
simplifyW env gs0 ds ws = do
  piTrace env $ text "-----------"

  let
    (unflat,gs) = Fsk.collate_fsks env gs0

  piTrace env $ text "simplifyW Unflat" <+> ppr unflat
  piTrace env $ text "simplifyW gs" <+> ppr gs
  piTrace env $ text "simplifyW ds" <+> ppr ds
  piTrace env $ text "simplifyW ws" <+> ppr ws

  gwips <- catMaybes <$> mapM (Parse.mkWIP (runAny env) env unflat) gs
  piTrace env $ text "simplifyW gwips" <+> ppr gwips

  (_,dgres) <- (runAny env) $ InertSet.extendInertSet GHCType.cacheEnv (GHCType.ghcTypeEnv env unflat) (InertSet.MkInertSet [] (InertSet.emptyCache Types.emptyFM)) gwips
  mgres <- case dgres of
    Types.Contradiction -> do
      piTrace env $ text "given contradiction"
      pure Nothing
    Types.OK (Left (deqs,_gwips')) -> do
      piTrace env $ text "given deqs" <+> ppr (Types.toListFM deqs)
      pure Nothing
    Types.OK (Right (InertSet.MkInertSet _ cache,env')) -> do
      piTrace env $
          (text "given aparts" <+> ppr (Types.toListFM $ Types.view InertSet.apartness_table cache))
        O.$$
          (text "given subst" <+> ppr (Types.toListFM $ Types.view InertSet.frag_subst cache))
        O.$$
          (text "given mult" <+> ppr (Types.toListFM $ Types.view InertSet.multiplicity_table cache))
      pure $ Just (cache,env')

  (ws1,wwips) <- fmap partitionEithers $ forM ws $ \w ->
      maybe (Left w) Right
    <$>
      Parse.mkWIP (runAny env) env unflat w
  piTrace env $ text "simplifyW ws" <+> ppr ws
  piTrace env $ text "simplifyW wwips" <+> ppr wwips

  x <- (>>= pluginResult env Wanted) $ case mgres of
    Just (cache,isetEnv) -> do
      (_,dwres) <- (runAny env) $ InertSet.extendInertSet GHCType.cacheEnv isetEnv (InertSet.MkInertSet [] cache) wwips
      case dwres of
        Types.Contradiction -> do
          piTrace env $ text "simplifyW contradiction"
          pure $ foldMap contraPR ws
        Types.OK (Left (deqs,wwips')) -> do
          piTrace env $ text "simplifyW deqs" <+> ppr (Types.toListFM deqs) O.$$ ppr wwips'
          pr1 <- okWantedWIPs env wwips'
          pr2 <- getAp $ Types.foldMapFM (\(l,r) () -> Ap (deqWanted (ctLoc (head ws)) l r)) deqs   -- TODO fix ctLoc
          pure $ pr1 <> pr2
        Types.OK (Right (InertSet.MkInertSet wwips' _,isetEnv')) -> do
          piTrace env $ text "simplifyW good" <+> ppr wwips' <+> ppr ws1
          pr1 <- okWantedWIPs env wwips'
          pr2 <- popReductions env updWanted unflat (InertSet.envFrag isetEnv') ws1
          pure $ pr1 <> pr2
    Nothing -> pure $ foldMap contraPR gs

  case x of
    TcPluginOk l r -> do
      piTrace env $ text "OUTPUT" <+> ppr (l,r)
    _ -> pure ()
  pure x

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
      (predty,f) = GHCType.ct_inn env ct
    ctev <- newWanted (ctLoc o) predty   -- TODO fix ctLoc level
    pure $ newPR (mkNonCanonical ctev) <> solveWantedPR o (EvExpr (f (GHCType.UpdWanted (ctPred o) (ctEvExpr ctev))))

  news' <- fmap mconcat $ forM news $ \ct -> do
    let
      o = fst (head olds)
      (predty,_) = GHCType.ct_inn env ct
    ctev <- newWanted (ctLoc o) predty   -- TODO fix ctLoc level
    pure $ newPR (mkNonCanonical ctev)

  pure $ olds' <> news'

-----

popReductions ::
    Monoid m
  =>
    E
  ->
    (Ct -> TcType -> (CtEvidence -> Ct) -> TcPluginM m)
  ->
    Fsk.Unflat
  ->
    Frag.Env TcKind TcType TcType
  ->
    [Ct]
  ->
    TcPluginM m
popReductions env upd unflat fragEnv cts = fmap mconcat $ forM cts $ \ct -> case ct of
  CDictCan _ cls xis pending_sc -> do
    (Any hit,xis') <- runAny env $ forM xis $ \xi -> case GhcPlugins.tcSplitTyConApp_maybe (Fsk.unflatten unflat xi) of
      Just (tc,[k,fr])
        | tc == Lookups.fragPopTC env -> go xi k fr
      _ -> pure xi
    if not hit then pure mempty else do   -- upd ct $ CDictCan ev cls xis' pending_sc
    let
      r = GhcPlugins.classTyCon cls `GhcPlugins.mkTyConApp` xis'
    upd ct r $ \ev -> CDictCan ev cls xis' pending_sc

  _ -> pure mempty
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
