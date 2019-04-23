{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.GHCType (
  apartnessEnv,
  classEnv,
  eqEnv,
  fragEnv,
  ghcTypeEnv,
  fragEquivalence_candidate_out,
  knownFragZ_out,
  setFrag_out,
  ) where

import Class (classTyCon)
import DataCon (promoteDataCon)
import Panic (panic)
import TcType (TcKind,TcType,getTvSubstEnv,eqType,nonDetCmpType,tcSplitTyConApp_maybe,tyCoVarsOfTypes,typeKind)
import TcRnTypes (Ct(..),ctPred)
import TcUnify (swapOverTyVars)
import Type (EqRel(NomEq),PredTree(ClassPred,EqPred),classifyPredType,getTyVar_maybe,mkTyConApp,mkTyConTy,mkTyVarTy)
import TysWiredIn (falseDataCon,trueDataCon,unitDataCon,unitTyCon)
import Unify (BindFlag(BindMe),UnifyResultM(..),tcUnifyTysFG,typesCantMatch)
import UniqFM (nonDetUFMToList)
import Unique (getUnique)
import VarEnv (getInScopeVars,mkInScopeSet)
import VarSet (lookupVarSet_Directly)

import qualified Data.Frag.Plugin.Apartness as Apartness
import qualified Data.Frag.Plugin.Class as Class
import qualified Data.Frag.Plugin.Equivalence as Equivalence
import qualified Data.Frag.Plugin.Frag as Frag
import Data.Frag.Plugin.GHCType.DetCmpType (detCmpType)
import Data.Frag.Plugin.GHCType.Fsk (Unflat,unflatten)
import qualified Data.Frag.Plugin.InertSet as InertSet
import Data.Frag.Plugin.Lookups (E(..))
import Data.Frag.Plugin.Types

fragEnv :: E -> Unflat -> Frag.Env TcKind TcType TcType
fragEnv env unflat = Frag.MkEnv{
    Frag.envFunRoot_inn = funRoot_inn env
  ,
    Frag.envFunRoot_out = funRoot_out env unflat
  ,
    Frag.envIsEQ = \l r -> (EQ ==) <$> detCmpType l r
  ,
    Frag.envIsLT = \l r -> (LT ==) <$> detCmpType l r
  ,
    Frag.envIsNil = \ty -> case tcSplitTyConApp_maybe ty of
      Just (tc,[_k])
        | tc == promoteDataCon (fragNilDC env) -> True
      _ -> False
  ,
    Frag.envIsZBasis = \ty -> case tcSplitTyConApp_maybe ty of
      Just (tc,[]) | tc == unitTyCon -> True
      _ -> False
  ,
    Frag.envMultiplicity = \_ _ -> Nothing
  ,
    Frag.envNil = \k -> mkTyConApp (promoteDataCon (fragNilDC env)) [k]
  ,
    Frag.envRawFrag_inn = rawFrag_inn env
  ,
    Frag.envRawFrag_out = rawFrag_out env unflat
  ,
    Frag.envShow = \k -> k
  ,
    Frag.envUnit = mkTyConTy $ promoteDataCon unitDataCon
  ,
    Frag.envZBasis = mkTyConTy unitTyCon
  }

rawFrag_inn :: E -> RawFrag TcType TcType -> TcType
rawFrag_inn env fr = go root (rawFragExt fr)
  where
  root = rawFragRoot fr
  k = typeKind root

  go acc = \case
    ExtRawExt ext s b -> go (mkTyConApp (tc env) [k,acc,b]) ext
      where
      tc = case s of Neg -> fragMinusTC; Pos -> fragPlusTC
    NilRawExt -> acc

rawFrag_out :: E -> Unflat -> TcType -> RawFrag TcType TcType
rawFrag_out env unflat = go id
  where
  go acc = go2 acc . unflatten unflat

  go2 acc = \ty -> case tcSplitTyConApp_maybe ty of
    Just (tc,[_,fr,b])
      | tc == fragMinusTC env -> go (\x -> ExtRawExt (acc x) Neg b) fr
      | tc == fragPlusTC env -> go (\x -> ExtRawExt (acc x) Pos b) fr

    _ -> MkRawFrag (acc NilRawExt) ty

funRoot_inn :: E -> FunRoot TcKind TcType TcType -> TcType
funRoot_inn env (MkFunRoot k fun fr) = case fun of
  FragCard -> f fragCardTC id
  FragEQ b -> f fragEQTC (b:)
  FragLT b -> f fragLTTC (b:)
  FragNE b -> f fragNETC (b:)
  where
  f fun' args = mkTyConApp (fun' env) (k:args [fr])

funRoot_out :: E -> Unflat -> TcType -> Maybe (FunRoot TcKind TcType TcType)
funRoot_out env unflat = \ty -> case tcSplitTyConApp_maybe (unflatten unflat ty) of
  Just (tc,k:args) -> let
    mk l r = Just $ MkFunRoot k l r
    in case args of
    [fr]
      | tc == fragCardTC env -> mk FragCard fr
    [b,fr]
      | tc == fragEQTC env -> mk (FragEQ b) fr
      | tc == fragLTTC env -> mk (FragLT b) fr
      | tc == fragNETC env -> mk (FragNE b) fr
    _ -> Nothing
  _ -> Nothing

-----

classEnv :: E -> Unflat -> Class.Env TcKind TcType TcType
classEnv env unflat = Class.MkEnv{
    Class.envEq = \l r -> (EQ ==) <$> detCmpType l r
  ,
    Class.envIsSet = Frag.envIsNil passthru
  ,
    Class.envPassThru = passthru
  }
  where
  passthru = fragEnv env unflat

-----

apartnessEnv :: Apartness.Env TcType TcType
apartnessEnv = Apartness.MkEnv{
    Apartness.envTrivial = (mkTyConTy (promoteDataCon falseDataCon),mkTyConTy (promoteDataCon trueDataCon))
  ,
    Apartness.envTryUnify = unifyType
  }

unifyType :: TcType -> TcType -> Maybe (Apartness.UnificationResult (TcType,TcType))
unifyType l r = case tcUnifyTysFG (const BindMe) [l] [r] of
  -- TODO How do we want this to treat univars? Does it do that? (Inspect ambiguity checks, e.g.)
  MaybeApart _ -> Nothing
  SurelyApart -> Just Apartness.UApart
  Unifiable sigma -> case mappings of
    [(x,y)]
      | eqType x l && eqType y r || eqType y l && eqType x r -> Nothing   -- this is not progress
    _ -> Just $ Apartness.Unifiable mappings
  -- NB sigma is idempotent
  -- 
  -- See niFixTCvSubst, Note [Finding the substitution fixpoint] etc
  -- in GHC's Unify module.
    where
    mappings = [   -- the individual mappings that comprise the mgu
        case lookupVarSet_Directly varset u of
          Nothing -> panic "Data.Frag.Plugin.GHCType.unifyType out of scope unique"
          Just tv -> sort2 (mkTyVarTy tv) ty
      | (u,ty) <- nonDetUFMToList (getTvSubstEnv sigma)
      , case getTyVar_maybe ty of   -- filter out the reflexive subset
          Just tv -> getUnique tv /= u
          Nothing -> True
      ]
  where
  varset = getInScopeVars $ mkInScopeSet $ tyCoVarsOfTypes [l,r]

  sort2 :: TcType -> TcType -> (TcType,TcType)
  sort2 x y = case nonDetCmpType x y of
    LT -> (x,y)
    EQ -> (x,y)
    GT -> (y,x)

-----

eqEnv :: E -> Unflat -> Equivalence.Env TcKind TcType TcType
eqEnv env unflat = Equivalence.MkEnv{
    Equivalence.envEqR = eqType
  ,
    Equivalence.envNeedSwap = \l r -> case (getTyVar_maybe l,getTyVar_maybe r) of
      (Just tvL,Just tvR) -> swapOverTyVars tvL tvR
      (Nothing,Just _) -> True
      _ -> False
  ,
    Equivalence.envNotApart = \l r -> not $ typesCantMatch [(l,r)]
  ,
    Equivalence.envMultiplicity = \r _ ->
      if Frag.envIsNil passthru r
      then Just (MkCountInterval 0 0)
      else Nothing
  ,
    Equivalence.envPassThru = passthru
  }
  where
  passthru = fragEnv env unflat

-----

ghcTypeEnv :: E -> Unflat -> InertSet.Env TcKind TcType
ghcTypeEnv env unflat = InertSet.MkEnv{
    InertSet.envApartness = apartnessEnv
  ,
    InertSet.envClass = classEnv env unflat
  ,
    InertSet.envEquivalence = eqEnv env unflat
  ,
    InertSet.envFrag = fragEnv env unflat
  }

-----

-- | @(k,l,r)@ in @l ~ r :: Frag k@
fragEquivalence_candidate_out :: E -> Ct -> Maybe (TcKind,TcType,TcType)
fragEquivalence_candidate_out env ct = case classifyPredType (ctPred ct) of
  EqPred NomEq l r
    | Just (tc,[k]) <- tcSplitTyConApp_maybe (typeKind l)
    , tc == fragTC env -> Just (k,l,r)
  _ -> Nothing

-- | @(k,fr)@ in @SetFrag (fr :: Frag k) ~ '()@
setFrag_out :: E -> Unflat -> Ct -> Maybe (TcKind,TcType)
setFrag_out env unflat ct = case classifyPredType (ctPred ct) of
  EqPred NomEq l r
    | Just (tc,[]) <- tcSplitTyConApp_maybe r
    , tc == promoteDataCon unitDataCon
    , Just (tc2,[k,fr]) <- tcSplitTyConApp_maybe (unflatten unflat l)
    , tc2 == setFragTC env -> Just (k,fr)
  _ -> Nothing

-- | @(k,fr)@ in @KnownFragCard (fr :: Frag k)@
knownFragZ_out :: E -> Ct -> Maybe (TcKind,TcType)
knownFragZ_out env ct = case classifyPredType (ctPred ct) of
  ClassPred cls [k,fr]
    | classTyCon cls == knownFragZTC env -> Just (k,fr)
  _ -> Nothing
