{-# LANGUAGE LambdaCase #-}

module Data.Frag.Plugin (plugin,tcPlugin) where

import qualified GhcPlugins
import Outputable ((<+>),ppr,text)
import TcPluginM (TcPluginM)
import TcRnTypes (Ct,TcPlugin(..),TcPluginResult(..),TcPluginSolver,isCFunEqCan)

import qualified Data.Frag.Plugin.GHCType as GHCType
import Data.Frag.Plugin.GHCType.Fsk (collate_fsks)
import qualified Data.Frag.Plugin.Lookups as Lookups
import Data.Frag.Plugin.Lookups (E,piTrace)

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
        (\r -> maybe (Left r) Right $ GHCType.funRoot_out env unflat r)
      <$>
        GHCType.rawFrag_out env unflat ty

  piTrace env $ text "simplifyW Unflat" <+> ppr unflat
  piTrace env $ text "simplifyW gs" <+> ppr gs
  piTrace env $ text "simplifyW ds" <+> ppr ds
  piTrace env $ text "simplifyW ws" <+> ppr ws

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
