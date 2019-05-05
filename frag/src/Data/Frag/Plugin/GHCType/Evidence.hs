{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.GHCType.Evidence (
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
import TcEvidence (EvExpr,EvTerm(EvExpr),Role(..),evTermCoercion)
import TcRnTypes (Ct,TcPluginResult(..),ctEvTerm,ctEvidence)
import TcType (TcType)
import TyCoRep (UnivCoProvenance(PluginProv))
import Type (PredTree(EqPred),classifyPredType,eqRelRole,eqType)

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

pluginResult :: PluginResult -> TcPluginResult
pluginResult pr
  | null c = TcPluginOk (pr_solutions pr) (pr_new pr)
  | otherwise = TcPluginContradiction c
  where
  c = pr_contra pr

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
