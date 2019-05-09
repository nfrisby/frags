{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}

-- | An adaptation of Type.nonDetCmpTypeX to be deterministic.
module Data.Frag.Plugin.DetCmpType (
  detCmpType,
  ) where

import Module (moduleStableString)
import Name (getOccString,nameModule)
import Outputable (ppr,pprPanic)
import TcType
import TyCoRep (Type(..))
import TyCon
import Type (repSplitAppTy_maybe)
import VarEnv (RnEnv2,VarEnv,emptyInScopeSet,emptyVarEnv,extendVarEnv,lookupVarEnv,mkRnEnv2,rnBndr2_var,rnOccL_maybe,rnOccR_maybe)
import Var (TyVarBndr(..),Var,tyVarKind)

import Control.Applicative (liftA2)
import GHC.Fingerprint

detCmpType :: Type -> Type -> Maybe Ordering
detCmpType = detCmpTypeX (mkRnEnv2 emptyInScopeSet)

data E = E {-# UNPACK #-} !Int !(VarEnv Int) !RnEnv2

eRnEnv2 :: E -> RnEnv2
eRnEnv2 (E _ _ re) = re

emptyE :: RnEnv2 -> E
emptyE = E 0 emptyVarEnv

lookupE :: E -> Var -> Maybe Int
lookupE (E _ ve _) v = lookupVarEnv ve v

bndrE :: E -> Var -> Var -> E
bndrE (E i ve re) v1 v2 = E (i+1) (extendVarEnv ve v i) re'
  where
  (re',v) = rnBndr2_var re v1 v2

detCmpTypeX :: RnEnv2 -> Type -> Type -> Maybe Ordering
detCmpTypeX = go . emptyE
  where
    liftOrdering :: Ordering -> Maybe Ordering
    liftOrdering = Just

    thenCmpTy :: Maybe Ordering -> Maybe Ordering -> Maybe Ordering
    thenCmpTy = liftA2 f
      where
      f EQ rel = rel
      f rel _ = rel

    giveUpUnlessEqual :: Maybe Ordering -> Maybe Ordering
    giveUpUnlessEqual = \case
      Just EQ -> Just EQ
      _ -> Nothing

    go :: E -> Type -> Type -> Maybe Ordering
    go env t1 t2
      | Just t1' <- coreView t1 = go env t1' t2
      | Just t2' <- coreView t2 = go env t1 t2'

    go env (TyVarTy tv1) (TyVarTy tv2)
      | tv1 == tv2 = liftOrdering EQ
      | otherwise =
          compare  -- de Bruijn indices
      <$> (rnOccL_maybe (eRnEnv2 env) tv1 >>= lookupE env)
      <*> (rnOccR_maybe (eRnEnv2 env) tv2 >>= lookupE env)
    go env (ForAllTy (TvBndr tv1 _) t1) (ForAllTy (TvBndr tv2 _) t2)
      = go env (tyVarKind tv1) (tyVarKind tv2)
        `thenCmpTy` go (bndrE env tv1 tv2) t1 t2
    go env (AppTy s1 t1) ty2
      | Just (s2, t2) <- repSplitAppTy_maybe ty2
      = go env s1 s2 `thenCmpTy` go env t1 t2
    go env ty1 (AppTy s2 t2)
      | Just (s1, t1) <- repSplitAppTy_maybe ty1
      = go env s1 s2 `thenCmpTy` go env t1 t2
    go env (FunTy s1 t1) (FunTy s2 t2)
      = go env s1 s2 `thenCmpTy` go env t1 t2
    go env (TyConApp tc1 tys1) (TyConApp tc2 tys2)
      = (if isFamilyTyCon tc1 || isFamilyTyCon tc2 then giveUpUnlessEqual else id)   -- TODO Use 'FamInstEnv.apartnessCheck'
      $ liftOrdering (tc1 `detCmpTc` tc2) `thenCmpTy` gos env tys1 tys2
    go _   (LitTy l1)          (LitTy l2)          = liftOrdering (compare l1 l2)
    go env (CastTy t1 _)       t2                  = go env t1 t2
    go env t1                  (CastTy t2 _)       = go env t1 t2

    go _   (CoercionTy {})     (CoercionTy {})     = liftOrdering EQ

    go env (TyVarTy tv) _ | Nothing <- lookupE env tv = Nothing   -- free tyvars might match later
    go env _ (TyVarTy tv) | Nothing <- lookupE env tv = Nothing   -- free tyvars might match later

    go _ ty1 ty2
      = liftOrdering $ (get_rank ty1) `compare` (get_rank ty2)
      where get_rank :: Type -> Int
            get_rank (CastTy {})
              = pprPanic "Coxswain.GHCAPI.detCmpType.get_rank" (ppr [ty1,ty2])
            get_rank (TyVarTy {})    = 0
            get_rank (CoercionTy {}) = 1
            get_rank (AppTy {})      = 3
            get_rank (LitTy {})      = 4
            get_rank (TyConApp {})   = 5
            get_rank (FunTy {})      = 6
            get_rank (ForAllTy {})   = 7

    gos :: E -> [Type] -> [Type] -> Maybe Ordering
    gos _   []         []         = liftOrdering EQ
    gos _   []         _          = liftOrdering LT
    gos _   _          []         = liftOrdering GT
    gos env (ty1:tys1) (ty2:tys2) = go env ty1 ty2 `thenCmpTy` gos env tys1 tys2

detCmpTc :: TyCon -> TyCon -> Ordering
detCmpTc tc1 tc2 = mkTyConFingerprint tc1 `compare` mkTyConFingerprint tc2

mkTyConFingerprint :: TyCon -> Fingerprint
mkTyConFingerprint tc =
  fingerprintFingerprints
  [ fingerprintString (moduleStableString modu)
  , fingerprintString (getOccString nm)
  ]
  where
  nm = tyConName tc
  modu = nameModule nm
