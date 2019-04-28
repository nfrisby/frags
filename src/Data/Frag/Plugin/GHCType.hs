{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.GHCType (
  Upd(..),
  apartnessEnv,
  apartness_out,
  cacheEnv,
  classEnv,
  ct_inn,
  eqEnv,
  fragEnv,
  ghcTypeEnv,
  fragEquivalence_candidate_out,
  knownFragZ_out,
  setFrag_out,
  ) where

import Class (classTyCon)
import Coercion (mkSymCo,mkUnbranchedAxInstCo)
import CoreSyn (Expr(Cast,Var),mkIntLitInt,mkTyArg)
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty((:|)))
import DataCon (promoteDataCon)
import MkCore (mkCoreApps)
import Panic (panic)
import TcEvidence (EvExpr,Role(Representational))
import TcType (TcKind,TcTyVar,TcType,getTvSubstEnv,eqType,nonDetCmpType,tcSplitTyConApp_maybe,tyCoVarsOfType,tyCoVarsOfTypes,typeKind)
import TcRnTypes (Ct(..),ctPred)
import TcUnify (swapOverTyVars)
import Type (EqRel(NomEq),PredTree(ClassPred,EqPred),classifyPredType,getTyVar_maybe,mkPrimEqPred,mkTyConApp,mkTyConTy,mkTyVarTy)
import TysWiredIn (falseDataCon,trueDataCon,unitDataCon,unitTyCon)
import Unify (BindFlag(BindMe),UnifyResultM(..),tcUnifyTysFG,typesCantMatch)
import UniqFM (nonDetUFMToList)
import UniqSet (elementOfUniqSet)
import Unique (getUnique)
import VarEnv (getInScopeVars,mkInScopeSet)
import VarSet (lookupVarSet_Directly)

import qualified Data.Frag.Plugin.Apartness as Apartness
import qualified Data.Frag.Plugin.Class as Class
import qualified Data.Frag.Plugin.Equivalence as Equivalence
import qualified Data.Frag.Plugin.Frag as Frag
import Data.Frag.Plugin.GHCType.DetCmpType (detCmpType)
import Data.Frag.Plugin.GHCType.Evidence (fiatcastev) -- ,fiatco)
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
  ,
    Frag.debug = []
  }

rawFrag_inn :: E -> RawFrag TcType TcType -> TcType
rawFrag_inn env fr = go root (rawFragExt fr)
  where
  root = rawFragRoot fr

  go acc = \case
    ExtRawExt ext s b -> go (mkTyConApp (tc env) [typeKind b,acc,b]) ext
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

-- | @arg@ in @Apart arg ~ '()@
apartness_out :: E -> Unflat -> Ct -> Maybe (NonEmpty (TcType,TcType))
apartness_out env unflat ct = case classifyPredType (ctPred ct) of
  EqPred NomEq l r
    | Just (tc,[]) <- tcSplitTyConApp_maybe r
    , tc == promoteDataCon unitDataCon
    , Just (tc2,[arg]) <- tcSplitTyConApp_maybe (unflatten unflat l)
    , tc2 == apartTC env -> go arg
  _ -> Nothing
  where
  cons l r xs = (l,r) :| toList xs

  go ty
    | Just (tc,[_k,l,r,arg]) <- tcSplitTyConApp_maybe ty
    , tc == promoteDataCon (apartConsDC env) = cons l r <$> go arg
    
    | Just (tc,[_k,l,r]) <- tcSplitTyConApp_maybe ty
    , tc == promoteDataCon (apartOneDC env) = Just $ (l,r) :| []

    | otherwise = Nothing

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
knownFragZ_out env = knownFragZ_out_ env . ctPred

knownFragZ_out_ :: E -> TcType -> Maybe (TcKind,TcType)
knownFragZ_out_ env ty = case classifyPredType ty of
  ClassPred cls [k,fr]
    | classTyCon cls == knownFragZTC env -> Just (k,fr)
  _ -> Nothing

-----

cacheEnv :: InertSet.CacheEnv TcKind (FM TcTyVar (Frag TcType TcType)) TcType TcTyVar
cacheEnv = InertSet.MkCacheEnv{
    InertSet.envEmptySubst = emptyFM
  ,
    InertSet.envExtendSubst = \v fr -> alterFM v (const (Just fr))
  ,
    InertSet.envLookup = lookupFM
  ,
    InertSet.envNeedSwap = swapOverTyVars
  ,
    InertSet.envRemoveFVs = \fm t -> filterFM (\v _ -> not $ elementOfUniqSet v (tyCoVarsOfType t)) fm
  ,
    InertSet.envShow = \k -> k
  ,
    InertSet.envVar_out = getTyVar_maybe
  }

-----

data Upd =
    -- old type, old evidence
    UpdGiven !TcType !EvExpr
  |
    -- old type, new evidence
    UpdWanted !TcType !EvExpr

ct_inn :: E -> InertSet.Ct TcKind TcType -> (TcType,Upd -> EvExpr)
ct_inn env = \case
  InertSet.ApartnessCt (MkApartness pairs) -> case toListFM pairs of
    [] -> panic "Data.Frag.Plugin.GHCTypes.ct_inn MkApartness []"
    ((l0,r0),()):ps0 -> castev $ 
      mkPrimEqPred (mkTyConTy (promoteDataCon unitDataCon)) $
      apartTC env `mkTyConApp` [go ps0]
      where
      go = \case
        [] -> promoteDataCon (apartOneDC env) `mkTyConApp` [typeKind l0,l0,r0]
        ((l,r),()):ps' -> promoteDataCon (apartConsDC env) `mkTyConApp` [typeKind l,l,r,go ps']
  InertSet.ClassCt k cls -> case cls of
    KnownFragZ fr count -> (knownFragZTC env `mkTyConApp` [k,new_arg],adjust)
      where
      new_arg = frag_inn fr

      coax = knownFragZCoax env
      from_class a = flip Cast $ mkUnbranchedAxInstCo Representational coax [k,a] []
      to_class a = flip Cast $ mkSymCo $ mkUnbranchedAxInstCo Representational coax [k,a] []

      lit isG = mkIntLitInt (dynFlags0 env) $ (if isG then negate else id) (getCount count)

      adjust = \case
        UpdGiven old_ty old_ev -> to_class new_arg $ Var (unsafeConvertProxyIntId env) `mkCoreApps`
          [mkTyArg k,mkTyArg old_arg,mkTyArg new_arg,from_class old_arg old_ev,lit True]
          where
          old_arg = case knownFragZ_out_ env old_ty of
            Just (_,t) -> t
            Nothing -> panic "Data.Frag.Plugin.GHCTypes.ct_inn KnownFragZ Nothing"
        UpdWanted old_ty new_ev -> to_class old_arg $ Var (unsafeConvertProxyIntId env) `mkCoreApps`
          [mkTyArg k,mkTyArg new_arg,mkTyArg old_arg,from_class new_arg new_ev,lit False]
          where
          old_arg = case knownFragZ_out_ env old_ty of
            Just (_,t) -> t
            Nothing -> panic "Data.Frag.Plugin.GHCTypes.ct_inn KnownFragZ Nothing"
    SetFrag fr -> castev $ mkPrimEqPred (mkTyConTy (promoteDataCon unitDataCon)) $ setFragTC env `mkTyConApp` [k,frag_inn fr]
  InertSet.EquivalenceCt _ (MkFragEquivalence l r ext) ->
    castev $ mkPrimEqPred l (frag_inn (MkFrag ext r))
  where
  frag_inn = rawFrag_inn env . forgetFrag

  castev :: TcType -> (TcType,Upd -> EvExpr)
  castev predty = (
      predty
    ,
      \case
        UpdGiven old_ty old_ev -> fiatcastev old_ty predty old_ev
        UpdWanted old_ty new_ev -> fiatcastev predty old_ty new_ev
    )
