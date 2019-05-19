{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}

module Data.Frag.Simpl.Frag (
  Env(..),
  envFrag_inn,
  envFrag_out,
  envFragNE_out,
  interpret,
  reducePop,
  reinterpret,
  ) where

import Control.Applicative ((<|>))
import Outputable (Outputable)
import qualified Outputable as O

import Data.Maybe (isJust)
import Data.Monoid (All(..),Any(..),Endo(..),Sum(..))

import Data.Frag.Simpl.Types

interpret :: (Key b,Monad m) => Env k b r -> r -> WorkT m (Frag b r)
interpret env r = do
  (hit,fr') <- let ?env = env in listeningM $ interpret_ r
  printM $ O.text "interpreted" O.<+> O.ppr hit
    O.$$ envShow env (O.ppr r)
    O.$$ envShow env (O.ppr fr')
  pure fr'

reinterpret :: (Key b,Monad m) => Env k b r -> Frag b r -> WorkT m (Frag b r)
reinterpret env fr = do
  (hit,fr') <- listeningM $ interpret env (envFrag_inn env fr)
  printM $ O.text "reinterpreted" O.<+> O.ppr hit
    O.$$ envShow env (O.ppr fr)
    O.$$ envShow env (O.ppr fr')
  pure fr'

prntM :: Monad m => O.SDoc -> WorkT m ()
-- prntM = const $ pure ()
prntM = printM

envFrag_out :: Key b => Env k b r -> r -> Frag b r
envFrag_out env r
  | getAny hit = error "non-canonical argument to envFrag_out"
  | otherwise = a
  where
  (hit,a) = runWork (interpret env r) mempty

envFrag_inn :: Key b => Env k b r -> Frag b r -> r
envFrag_inn env = envRawFrag_inn env . forgetFrag

-----

data Env k b r = MkEnv{
    envMappingBasis :: !(k -> k -> k)
  ,
    envMapsTo_out :: !(b -> Maybe (k,k,b,b))
  ,
    -- | Not expected to un-unflatten.
    envFunRoot_inn :: !(FunRoot k b r -> r)
  ,
    -- |
    envFunRoot_out :: !(r -> Maybe (FunRoot k b r))
  ,
    envIsEQ :: !(b -> b -> Maybe Bool)
  ,
    -- | Returns @Just@ if and only if the order is deterministic.
    -- (e.g. independent of variable substitutions).
    envIsLT :: !(b -> b -> Maybe Bool)
  ,
    envIsNil :: !(r -> Bool)
  ,
    envIsZBasis :: !(k -> Bool)
  ,
    envMultiplicity :: !(r -> b -> Maybe Count)
  ,
    envNil :: !(k -> r)
  ,
    -- | Expected: @(Push (Pop fr)) --> Just fr@
    envPush_out :: !(r -> Maybe (k,r,Maybe (b,r)))
  ,
    -- |
    envRawFrag_inn :: !(RawFrag b r -> r)
  ,
    -- | INVARIANT: Yields the longest extension possible.
    envRawFrag_out :: !(r -> RawFrag b r)
  ,
    envShow :: !(forall a. ((Outputable k,Outputable b,Outputable r) => a) -> a)
  ,
    -- |
    envUnit :: !b
  ,
    envZBasis :: !k
  ,
    debug :: ![((r,Maybe b),CountInterval)]
  }

-----

interpretRawExt_ :: (Key b,Monad m) => RawExt b -> WorkT m (Ext b)
interpretRawExt_ = go 0 emptyFM
  where
  go !i !fm = \case
    ExtRawExt raw_ext s b -> go (i + 1) fm' raw_ext
      where
      fm' = insertFMS b (applySign s 1,mkPos i) fm
    NilRawExt -> do
      let
        changed = isChanged $ (`appEndo` ExpectingFirst 0) $ flip foldMap fm $ \(count,pos) ->
          Endo $ \check -> case (pos,check) of
            (Contiguous frst next,ExpectingFirst expected)
              | frst == expected    -- collated-but-not-sorted: +b +a +a   to   +a +a +b
              , next - frst == abs (getSum (unCount count))   -- cancelable: +a -a +b   to   +b
              -> ExpectingFirst next
            _ -> Changed    -- uncollated: +a +b +a   to   +a +a +b

      setM changed
      pure $ (`appEndo` emptyExt) $ flip foldMapFM fm $ \b (count,_) ->
        Endo $ \acc -> if 0 == count then acc else insertExt b count acc

data Pos =
    Contiguous !Int !Int
  |
    Incontiguous

instance Semigroup Pos where
  Contiguous first1 next1 <> Contiguous first2 next2
    | next1 == first2 = Contiguous first1 next2
    | next2 == first1 = Contiguous first2 next1
  _ <> _ = Incontiguous

mkPos :: Int -> Pos
mkPos = \p -> Contiguous p (p+1)

-----

show_r :: (?env :: Env k b r) => r -> O.SDoc
show_r = envShow ?env O.ppr

show_c :: (Key b,?env :: Env k b r) => Context k b -> O.SDoc
show_c = envShow ?env O.ppr

interpret_ :: (Key b,Monad m,?env :: Env k b r) => r -> WorkT m (Frag b r)
interpret_ = \r -> do
  before <- alreadyM
  prntM $ O.text "interpret_:" O.<+> O.ppr (getAny before) O.<+> show_r r O.<+> O.text "{"
  prntM $ O.text "outer {"
  x <- contextualize OtherC r >>= uncurry outer
  prntM $ O.text "} outer"
  after <- alreadyM
  prntM $ O.text "interpret_:" O.<+> O.ppr (getAny after) O.<+> show_r r O.<+> O.text "}"
  pure x
  where
  outer ctxt r = do
    (ctxt',r') <- inner ctxt r
    case ctxt' of
      ExtC ext OtherC -> pure $ MkFrag ext r'
      ExtC ext c -> outer c $ envFrag_inn ?env $ MkFrag ext r'
      FunC fun neqs c -> do
        let
          mk k f = envFunRoot_inn ?env $ MkFunRoot f (arg k)
          arg k = foldMapFM (neq k) neqs `appEndo` r'

          r2 = case fun of
            FragDomC dom cod -> mk dom (FragDom dom cod)
            FragCardC k -> mk k (FragCard k)
            FragEQC k b -> mk k (FragEQ k b)
            FragLTC k b -> mk k (FragLT k b)
            FragNEC k -> arg k
        case envFunRoot_out ?env r' of
          Just (MkFunRoot inner_fun _) -> case inner_fun of
            FragDom{} -> do
              prntM $ O.text "up 1"
              outer c r2
            _ -> case envFunRoot_out ?env r2 of
              Nothing -> panic "Data.Frag.Simpl.Frag.interpret_: FunC rebuilt incorrectly"
              Just new_froot -> do
                prntM (O.text "up 2")
                contextualize1FunRoot c new_froot >>= uncurry outer
          Nothing -> do
            prntM $ O.text "up 3"
            outer c r2
      OtherC -> pure $ MkFrag emptyExt r'

  inner ctxt r = do
    prntM $ O.text "======================= inner {" O.$$ show_c ctxt O.$$ show_r r
    (hit,(ctxt',r')) <- listeningM $ interpretC ctxt r
    prntM $ O.text "} inner" O.<+> O.ppr hit O.$$ show_c ctxt' O.$$ show_r r'
    if hit then inner ctxt' r' else pure (ctxt',r')

  neq k b () = Endo $ envFunRoot_inn ?env . MkFunRoot (FragNE k b)

contextualize :: (Key b,Monad m,?env :: Env k b r) => Context k b -> r -> WorkT m (Context k b,r)
contextualize ctxt r = let
  raw_fr = envRawFrag_out ?env r
  stop = pure (ctxt,r)
  in case rawFragExt raw_fr of
    ExtRawExt{} -> contextualizeRawFrag ctxt raw_fr
    NilRawExt -> case envFunRoot_out ?env r of
      Just froot -> do
        (ctxt',r') <- contextualize1FunRoot ctxt froot
        contextualize ctxt' r'
      Nothing -> case envPush_out ?env r of
        Just (_,r',pop) -> do
          case pop of
            Just (b,count_r) -> do
              count_fr <- interpret_ count_r
              if not (envIsNil ?env (fragRoot count_fr)) then stop else do
                let
                  count = foldMap id $ unExt $ fragExt count_fr
                setM True
                contextualizeRawFrag ctxt $ forgetFrag $ MkFrag (insertExt b count emptyExt) r'
            Nothing -> do
              setM True
              contextualize ctxt r'
        Nothing -> stop

contextualizeRawFrag :: (Key b,Monad m,?env :: Env k b r) => Context k b -> RawFrag b r -> WorkT m (Context k b,r)
contextualizeRawFrag ctxt raw_fr = do
  ext <- interpretRawExt_ $ rawFragExt raw_fr
  contextualize (mkExtC ext ctxt) (rawFragRoot raw_fr)

contextualize1FunRoot :: (Key b,Monad m,?env :: Env k b r) => Context k b -> FunRoot k b r -> WorkT m (Context k b,r)
contextualize1FunRoot ctxt froot@(MkFunRoot fun r)
  -- check during top-down in case we can replace a big frag with 'Nil
  | Just r' <- checkFunRootZ froot = do
  setM True
  pure (ctxt,r')

  | otherwise = do
    (neqs,rNE) <- peelFragNE os r
    prntM $ O.text "peelFragNE" O.<+> envShow ?env (O.ppr fun) O.<+> show_r r O.<+> envShow ?env (O.ppr (toListFM neqs)) O.<+> show_r rNE

    let
      (_,MkNEQs _ chkr) = contextFunC ctxt
      (Any reduction,Endo fneqs) = flip foldMapFM neqs $ \b () ->
        if getAny $ neqchk_any_match (chkr b)
        then (Any True,Endo $ deleteFM b)
        else mempty
      neqs' = fneqs neqs
    setM reduction   -- reduced:
    --   FragNE a (FragEQ x (FragNE a fr ...) ...)   to   FragNE a (FragEQ x (fr ...) ...)

    -- check during top-down in case we can replace a big frag with 'Nil
    (fneqs',r') <- case checkFunFun fun' neqs' rNE of
      Just (f,r') -> do setM True; pure (f,r')
      Nothing -> pure (id,rNE)

    pure (mkFunC fun' (fneqs' neqs') ctxt,r')

  where
  (os,fun') = case fun of
    FragDom dom cod -> (emptyOrdSet,FragDomC dom cod)
    FragCard k -> (emptyOrdSet,FragCardC k)
    FragEQ k b -> (emptyOrdSet,FragEQC k b)
    FragLT k b -> (emptyOrdSet,FragLTC k b)
    FragNE k b -> (insertOrdSet b emptyOrdSet,FragNEC k)

checkFunRootZ :: (?env :: Env k b r) => FunRoot k b r -> Maybe r
checkFunRootZ (MkFunRoot fun r) = case fun of
  -- reduced: FragCard fr   to   fr
  --          FragEQ b fr   to   fr
  --          FragLT b fr   to   'Nil
  --          FragNE b fr   to   'Nil
  FragDom{} -> Nothing   -- FragDom _ :: Frag '() is not determined
  FragCard k -> ifZ k r
  FragEQ k _ -> ifZ k r
  FragLT k _ -> ifZ k $ envNil ?env (envZBasis ?env)
  FragNE k _ -> ifZ k $ envNil ?env k
  where
  ifZ k r' = if envIsZBasis ?env k then Just r' else Nothing

envFragNE_out :: (Key b,Monad m) => Env k b r -> r -> WorkT m (FM b (),r)
envFragNE_out env = let ?env = env in peelFragNE emptyOrdSet

peelFragNE :: (Key b,Monad m,?env :: Env k b r) => OrdSet b -> r -> WorkT m (FM b (),r)
peelFragNE = go
  where
  go acc r = case envFunRoot_out ?env r of
    Just (MkFunRoot (FragNE _ b) r') -> go (insertOrdSet b acc) r'
    _ -> do
    -- collated:
    --   FragNE a (FragNE a rNE ...)   to   FragNE a (rNE ...)
    -- unsorted:
    --   FragNE a (FragNE b rNE)   to   FragNE b (FragNE a rNE)   if b NONDET< a
    setM $ not $ canonicalOrdSet acc
    pure (() <$ ordSetFM acc,r)

checkFunFun :: (Key b,?env :: Env k b r) => FunC k b -> FM b () -> r -> Maybe (FM b () -> FM b (),r)
checkFunFun fun neqs r = case fun of
  FragEQC k a -> let
    each b () = case envIsEQ ?env a b of
      Just True -> (Any True,Any True,mempty)
      Just False -> (Any True,mempty,Endo $ deleteFM b)
      Nothing -> (mempty,mempty,mempty)
    (Any reduced,Any eq,Endo f) = foldMapFM each neqs
    in if not reduced then Nothing else Just $ (,) f $ if eq then envNil ?env k else r
    -- reduced:
    --   FragEQ a (FragNE a r ...)   to   FragEQ a ('Nil ...)
    --   FragEQ a (FragNE x (FragNE a r) ...)   to   FragEQ a ('Nil ...)
    --   FragEQ a (FragNE b r ...)   to   FragEQ a (r ...)   if a ~/ b
    --   FragEQ a (FragNE x (FragNE b r) ...)   to   FragEQ a (FragNE x r ...)   if a ~/ b

  FragLTC _ a -> let
    each b () = case envIsLT ?env a b of
      Just False -> (Any True,Endo $ deleteFM b)
      _ -> (mempty,mempty)
    (Any reduced,Endo f) = foldMapFM each neqs
    in if not reduced then Nothing else Just (f,r)
    -- reduced:
    --   FragLT a (FragNE b r ...)   to   FragLT a (r ...)   if b DET>= a
    --   FragLT a (FragNE x (FragNE b r) ...)   to   FragLT a (FragNE x r ...)   if b DET>= a

  -- NB: all FragNE-FragNE rules are handled in contextualize1FunRoot and peelFragNE
  _ -> Nothing

-----

interpretC :: (Key b,Monad m,?env :: Env k b r) => Context k b -> r -> WorkT m (Context k b,r)
interpretC ctxt r
  | envIsNil ?env r
  , FunC fun _ ctxt' <- ctxt = do
  prntM $ O.text "interpretC nil"
  setM True     -- reduced:
  --  DomFrag 'Nil   to   'Nil
  --  FragCard 'Nil   to   'Nil
  --  FragEQ b 'Nil   to   'Nil
  --  FragLT b 'Nil   to   'Nil
  --  FragNE b 'Nil   to   'Nil
  pair ctxt' $ envNil ?env $ case fun of
    FragDomC dom _cod -> dom
    FragCardC _ -> envZBasis ?env
    FragEQC _ _ -> envZBasis ?env
    FragLTC _ _ -> envZBasis ?env
    FragNEC k -> k

  | FunC fun neqs ctxt' <- ctxt
  , let    -- if FragEQ a q ~ 'Nil then FragNE a q   to   q
      (Any reduced,Endo fneqs) = flip foldMapFM neqs $ \b () ->
        case envMultiplicity ?env r b of
          Just 0 -> (Any True,Endo $ deleteFM b)
          _ -> mempty
  , reduced = do
    prntM $ O.text "interpretC envMultiplicity"
    setM True   -- reduced:
    --  FragNE b fr   to   fr   if 'Nil ~ FragEQ b fr
    interpretC (mkFunC fun (fneqs neqs) ctxt') r
    
  | FunC fun neqs ctxt' <- ctxt
  , Just (fneqs,r') <- checkFunFun fun neqs r = do
    prntM $ O.text "interpretC checkFunFun"
    setM True
    interpretC (mkFunC fun (fneqs neqs) ctxt') r'

  -- indirect and direct fun application
  | FunC fun neqs ctxt' <- ctxtE = do
    prntM $ O.text "interpretC direct"
    let (_,ctxt_neqs) = contextFunC ctxt'
    (hit,(ext',fr)) <- listeningM $ interpretFunC (Just (mkNEQs neqs)) fun ctxt_neqs extE r
    (if hit then interpretC else pair) (mkExtC (fragExt fr) $ mkFunC fun neqs $ mkExtC ext' ctxt') (fragRoot fr)

  -- indirect fun application only
  | (Just fun,ctxt_neqs) <- contextFunC ctxt = do
    prntM $ O.text "interpretC indirect"
    (hit,(_ext,fr)) <- listeningM $ interpretFunC Nothing fun ctxt_neqs extE r
    -- assert: _ext is empty
    (if hit then interpretC else pair) (mkExtC (fragExt fr) ctxtE) (fragRoot fr)

  | otherwise = pair ctxt r
  where
  (extE,ctxtE) = contextExtC ctxt

  pair x y = pure (x,y)

interpretFunC :: (Key b,Monad m,?env :: Env k b r) => Maybe (NEQs b) -> FunC k b -> NEQs b -> Ext b -> r -> WorkT m (Ext b,Frag b r)
interpretFunC direct fun ctxt_neqs inner_ext inner_root = do
  -- reduced:   FragEQ a (0 +a +b)   to   '() :+ FragEQ a (0 :+ b)
  --          or
  --            FragEQ C (0 +a +D)   to   FragEQ C (0 :+ a)
  --
  --          and/or
  --            FragEQ C (x ...)   to   FragEQ C (0 ...) :+ k    if FragEQ C x ~ k in environment
  envShow ?env $ prntM $ O.text "interpretFunC:"
    O.<+> O.ppr ({- toListFM <$> direct, -}fun,{- toListFM ctxt_neqs,-} inner_ext,inner_root)
    O.$$ O.ppr red'
    O.<+> pretty
    O.$$ O.ppr (units_root + units')
    O.$$ O.ppr (ext',MkFrag inner_ext' inner_root')
  setM reduction
  pure $ if reduction
    then (ext',MkFrag inner_ext' inner_root')
    else (emptyExt,MkFrag inner_ext inner_root)

  where
  reduction = red_root || red'
  ext' = insertExt (envUnit ?env) (units_root + units') pop'

  pretty = case fun of
    FragEQC _ b -> envShow ?env $ O.ppr (inner_root,b,envMultiplicity ?env inner_root b,debug ?env)
    _ -> O.empty

  -- check root
  (inner_root',red_root,units_root)
    | FragEQC knd b <- fun
    , Just k <- envMultiplicity ?env inner_root b
    , isJust direct || 0 == k
    = (envNil ?env knd,not (envIsNil ?env inner_root),k)

    | otherwise = (inner_root,False,0)

  inner_ext' = keep'
  (pop',units',keep',red') = foldlExt inner_ext (emptyExt,0,emptyExt,False) $ \parts@(pop,units,keep,red) b count ->
    if 0 == count then parts else case predicate b of
      Count -> let x = units + count in x `seq` (pop,x,keep,True)
      Drop -> (pop,units,keep,True)
      Keep -> let x = insertExt b count keep in x `seq` (pop,units,x,red)
      Pop popped_b -> let x = insertExt popped_b count pop in x `seq` (x,units,keep,True)

  -- check direct_neqs
  predicate b' = case predicate2 b' of
    Keep | Just direct_neqs <- direct -> check_neqs True direct_neqs b'
    pr -> pr

  -- check ctxt_neqs
  predicate2 b' = case predicate1 b' of
    Keep -> check_neqs False ctxt_neqs b'
    pr -> pr

  -- check direct (fun)
  predicate1 b' = case predicate0 b' of
    Count -> if isJust direct then Count else Keep
    Drop -> Drop
    Keep -> Keep
    Pop popped_b -> if isJust direct then Pop popped_b else Keep

  -- check fun
  predicate0 b' = case fun of
    FragDomC{} -> case envMapsTo_out ?env b' of
      Just (_dom,_cod,key,_val) -> Pop key
      Nothing -> Keep
    FragCardC _ -> Count
    FragEQC _ b -> case envIsEQ ?env b' b of
      Nothing -> Keep
      Just False -> Drop
      Just True -> Count
    FragLTC _ b -> case envIsLT ?env b' b of
      Nothing -> Keep
      Just False -> Drop
      Just True -> Count
    FragNEC _ -> Keep

  check_neqs neqs_are_direct (MkNEQs any_neqs neqchk) b'
    | neqs_are_direct && getAny any_neqs && getAll (neqchk_all_apart chk) = Pop b'
    | getAny (neqchk_any_match chk) = Drop
    | otherwise = Keep
    where
    chk = neqchk b'

data NEQs b = MkNEQs
  !Any
  !(b -> NEQCheck)

instance Semigroup (NEQs b) where
  MkNEQs l1 l2 <> MkNEQs r1 r2 = MkNEQs (l1 <> r1) (l2 <> r2)
instance Monoid (NEQs b) where mempty = MkNEQs mempty mempty

data NEQCheck = MkNEQCheck{
    neqchk_all_apart :: !All
  ,
    neqchk_any_match :: !Any
  }
instance Semigroup NEQCheck where MkNEQCheck l1 l2 <> MkNEQCheck r1 r2 = MkNEQCheck (l1 <> r1) (l2 <> r2)
instance Monoid NEQCheck where mempty = MkNEQCheck mempty mempty

data PredicateResult b =
    Count
  |
    Drop
  |
    Keep
  |
    Pop b

-----

mkExtC :: Key b => Ext b -> Context k b -> Context k b
mkExtC ext ctxt
  | nullFM (unExt ext) = ctxt
  | otherwise = case ctxt of
  ExtC ext' ctxt' -> ExtC (addExt ext ext') ctxt'
  _ -> ExtC ext ctxt

mkFunC :: Key b => FunC k b -> FM b () -> Context k b -> Context k b
mkFunC fun neqs = case fun of
  FragNEC _ | nullFM neqs -> id
  _ -> FunC fun neqs

contextExtC :: Key b => Context k b -> (Ext b,Context k b)
contextExtC = \case
  ExtC ext ctxt -> (ext,ctxt)
  ctxt -> (emptyExt,ctxt)

contextFunC :: (Key b,?env :: Env k b r) => Context k b -> (Maybe (FunC k b),NEQs b)
contextFunC = \case
  ExtC _ c -> contextFunC c
  FunC fun neqs c -> let
    (fun',neqs') = contextFunC c
    mfun = case fun of
      FragNEC _ -> fun' <|> Just fun
      _ -> Just fun
    in
    (mfun,neqs' <> mkNEQs neqs)
  OtherC -> (Nothing,mempty)

mkNEQs :: (Key b,?env :: Env k b r) => FM b () -> NEQs b
mkNEQs neqs = let
  chkr = \b' -> flip foldMapFM neqs $ \b () -> let
    isEq = envIsEQ ?env b' b
    in MkNEQCheck{
      neqchk_all_apart = All $ Just False == isEq
    ,
      neqchk_any_match = Any $ Just True == isEq
    }
  in
  MkNEQs (Any (not (nullFM neqs))) chkr

-----

reducePop :: (Key b,Monad m) => Env k b r -> r -> WorkT m (Maybe (Ext b))
reducePop env r = do
  fr <- interpret env r
  let
    ext = fragExt fr
  if not (envIsNil env (fragRoot fr)) then pure Nothing else do
  let
    All separate =
      foldMapExt ext $ \b count ->
      foldMapExt (insertExt b (invertSign count) ext) $ \b' _ ->
        All $ Just False == envIsEQ env b b'
  envShow env $ printM $ O.text "separate" O.<+> O.ppr separate O.<+> O.ppr (toListFM (unExt ext))
  if not separate then pure Nothing else do
  setM True
  pure (Just ext)
