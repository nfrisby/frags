{-# LANGUAGE LambdaCase #-}

module Data.Frag.Plugin (plugin,tcPlugin) where

import Control.Applicative ((<|>))
import Data.Maybe (mapMaybe)
import Data.Monoid (Any(..))
import qualified GhcPlugins
import Outputable ((<+>),ppr,text)
import TcPluginM (TcPluginM)
import TcRnTypes (Ct,TcPlugin(..),TcPluginResult(..),TcPluginSolver,isCFunEqCan)

import qualified Data.Frag.Plugin.Equivalence as Equivalence
import qualified Data.Frag.Plugin.Frag as Frag
import qualified Data.Frag.Plugin.GHCType as GHCType
import Data.Frag.Plugin.InertSet (WIP(..))
import qualified Data.Frag.Plugin.InertSet as InertSet
import Data.Frag.Plugin.GHCType.Fsk (collate_fsks)
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
solve env givens derivs wanteds =
  if null derivs && null wanteds
  then simplifyG env givens
  else simplifyW env givens derivs wanteds

stop :: E -> TcPluginM ()
stop _ = pure ()

simplifyG :: E -> [Ct] -> TcPluginM TcPluginResult
simplifyG _ _ = do
  pure $ TcPluginOk [] []

simplifyW :: E -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
simplifyW env gs0 ds ws = do
  piTrace env $ text "-----------"

  let
    (unflat,gs) = collate_fsks env gs0
    prj ty =
        (\r -> maybe (Left r) Right $ Frag.envFunRoot_out (GHCType.fragEnv env unflat) r)
      <$>
        Frag.envRawFrag_out (GHCType.fragEnv env unflat) ty

  piTrace env $ text "simplifyW Unflat" <+> ppr unflat
  piTrace env $ text "simplifyW gs" <+> ppr gs
  piTrace env $ text "simplifyW ds" <+> ppr ds
  piTrace env $ text "simplifyW ws" <+> ppr ws

  let
    fragEnv = GHCType.fragEnv env unflat
    run m = Types.runAnyT m (\_ -> pure ()) mempty

  let
    mkWIPs cs = do
      ccts <- mapM run $ flip mapMaybe cs $ \c -> let
        eqCt = flip fmap (GHCType.fragEquivalence_candidate_out env c) $ \(k,l,r) -> do
          lfr <- Frag.interpret fragEnv l
          rfr <- Frag.interpret fragEnv r
          eq <- Equivalence.interpret (GHCType.eqEnv env unflat) (Types.MkRawFragEquivalence lfr rfr)
          pure $ InertSet.EquivalenceCt k eq
        knownFragZCt = flip fmap (GHCType.knownFragZ_out env c) $ \(k,fr) -> do
          fr' <- Frag.interpret fragEnv fr
          pure $ InertSet.ClassCt k (Types.KnownFragZ fr' 0)
        setFragCt = flip fmap (GHCType.setFrag_out env unflat c) $ \(k,fr) -> do
          fr' <- Frag.interpret fragEnv fr
          pure $ InertSet.ClassCt k (Types.SetFrag fr')
        in
        fmap (fmap ((,) c)) $
            eqCt
          <|>
            knownFragZCt
          <|>
            setFragCt
      pure [MkWIP (Just (c `seq` (),hit)) ct | (Any hit,(c,ct)) <- ccts]

  gwips <- mkWIPs gs
  piTrace env $ text "simplifyW gwips" <+> ppr gwips

  wwips <- mkWIPs ws
  piTrace env $ text "simplifyW wwips" <+> ppr wwips

  let cs = gs ++ ds ++ ws
  piTrace env $ text "simplifyW ~ @Frag" <+> ppr [
    (k,prj l,prj r)
    | c <- cs
    , not (isCFunEqCan c)
    , Just (k,l,r) <- [GHCType.fragEquivalence_candidate_out env c]
    ]
  piTrace env $ text "simplifyW SetFrag" <+> ppr [
    (k,prj fr)
    | c <- cs
    , Just (k,fr) <- [GHCType.setFrag_out env unflat c]
    ]
  piTrace env $ text "simplifyW KnownFragZ" <+> ppr [
    (k,prj fr)
    | c <- cs
    , Just (k,fr) <- [GHCType.knownFragZ_out env c]
    ]

  pure $ TcPluginOk [] []
