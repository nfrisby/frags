{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.Evidence (
  Flavor(..),
  PluginResult(..),
  fiatcastev,
  fiatco,
  contraPR,
  discardGivenPR,
  newPR,
  pluginResult,
  solveWantedPR,
  ) where

import Coercion (Coercion,downgradeRole,ltRole,mkNomReflCo,mkTransCo,mkUnivCo)
import CoreSyn (Expr(Cast,Coercion))
import Data.Maybe (listToMaybe)
import FastString (mkFastString)
import qualified Outputable as O
import TcEvidence (EvExpr,EvTerm(EvExpr),Role(..),evTermCoercion)
import TcPluginM (TcPluginM,newGiven,newWanted)
import TcRnTypes (Ct,TcPluginResult(..),ctEvExpr,ctEvTerm,ctEvidence,ctLoc,ctPred,mkNonCanonical)
import TcType (TcType)
import TyCoRep (UnivCoProvenance(PluginProv))
--import Type (PredTree(EqPred),classifyPredType,eqRelRole,eqType,mkPrimEqPred,mkStrLitTy,mkTyConApp,mkTyConTy)
import Type (PredTree(EqPred),classifyPredType,eqRelRole,eqType,mkPrimEqPred,mkStrLitTy)

import Data.Frag.Plugin.Lookups

fiatco :: TcType -> TcType -> Coercion
fiatco t1 t2
  | eqType t1 t2 = mkNomReflCo t1
  | otherwise = mkUnivCo (PluginProv "frag") Nominal t1 t2

fiatcastev :: TcType -> TcType -> EvExpr -> EvExpr
fiatcastev t0 t1 ev0
  | Just (eq0,l0,r0) <- maybeEq t0
  , Just (eq1,l1,r1) <- maybeEq t1
  , not (eq1 `ltRole` eq0)  -- can downgrade eq0 to eq1
  = Coercion $ downgradeRole eq1 eq0 $
                  downgradeRole eq0 Nominal (fiatco l1 l0)
      `mkTransCo`
                  evTermCoercion (EvExpr ev0)
      `mkTransCo`
                  downgradeRole eq0 Nominal (fiatco r0 r1)
  | otherwise = Cast ev0 $ downgradeRole Representational Nominal $ fiatco t0 t1
  where
  maybeEq t = case classifyPredType t of
    EqPred eq l r -> Just (eqRelRole eq,l,r)
    _ -> Nothing

-----

data PluginResult = MkPluginResult{
    pr_contra :: ![Ct]
  ,
    pr_new :: ![Ct]
  ,
    pr_solutions :: ![(EvTerm,Ct)]
  }

instance Semigroup PluginResult where (<>) = mappend
instance Monoid PluginResult where
  mempty = MkPluginResult mempty mempty mempty
  MkPluginResult l0 l1 l2 `mappend` MkPluginResult r0 r1 r2 =
    MkPluginResult (l0 <> r0) (l1 <> r1) (l2 <> r2)

contraPR :: Ct -> PluginResult
contraPR x = MkPluginResult{
    pr_contra = [x]
  ,
    pr_new = []
  ,
    pr_solutions = []
  }

discardGivenPR :: Ct -> PluginResult
discardGivenPR ct = MkPluginResult{
    pr_contra = []
  ,
    pr_new = []
  ,
    pr_solutions = [(ctEvTerm (ctEvidence ct),ct)]
  }

newPR :: Ct -> PluginResult
newPR x = MkPluginResult{
    pr_contra = []
  ,
    pr_new = [x]
  ,
    pr_solutions = []
  }

solveWantedPR :: Ct -> EvTerm -> PluginResult
solveWantedPR ct ev = MkPluginResult{
    pr_contra = []
  ,
    pr_new = []
  ,
    pr_solutions = [(ev,ct)]
  }

-----

data Flavor = Given | Wanted

pluginResult :: E -> Flavor -> PluginResult -> TcPluginM TcPluginResult
pluginResult env flav pr = let cs = pr_contra pr in case listToMaybe cs of
  Just c -> do   -- replace the contradictory constraints with an inarguable one
    let
      l = ctPred c
      r = mkPrimEqPred
        (mkStrLitTy (mkFastString "Data.Frag.Plugin found a contradiction in these constraints:"))
        (mkStrLitTy $ mkFastString $
         concatMap (\case '\n' -> "\n     "; ch -> [ch]) $
         O.showSDocDump (dynFlags0 env) $ O.ppr cs)
    new <- case flav of
      Given -> fmap mkNonCanonical $ newGiven (ctLoc c) r $ fiatcastev l r (ctEvExpr (ctEvidence c))
      Wanted -> fmap mkNonCanonical $ newWanted (ctLoc c) r
    let
      old = case flav of
        Given -> foldMap discardGivenPR cs
        Wanted -> flip foldMap cs $ \ct ->
          solveWantedPR ct (EvExpr (fiatcastev r (ctPred ct) (ctEvExpr (ctEvidence new))))
    pure $ TcPluginOk (pr_solutions old) [new]
  Nothing ->
    pure $ TcPluginOk (pr_solutions pr) (pr_new pr)
