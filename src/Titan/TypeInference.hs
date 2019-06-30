module Titan.TypeInference
  ( ti
  ) where

import Data.Data.Lens (biplate)
import qualified Data.List as List
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map
import qualified Data.Set as Set
import Titan.Prelude
import Titan.Error
import Titan.TT
import Titan.Scope
import Titan.Substitution
import Titan.Row
import Titan.FunctionalDependency
import Titan.DependencyAnalyzer (depGroups)
import qualified Titan.PatternChecker as PC

data TIState = TIState
  { _subst :: Subst Type
  , _remainingCtx :: [Constraint]
  , _typeIds :: [Id Type]
  , _parameterIds :: [Id Parameter]
  }

data Premise = Premise
  { _constraint :: Constraint
  , _ensures :: [Constraint]
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data Entailment = Entailment
  { _constraint :: Constraint
  , _resolvedInstance :: Maybe ResolvedInstance
  , _wantVars :: Set (Id Type)
  , _complete :: Bool
  }
  deriving (Eq, Ord, Show, Data, Typeable)

data ResolvedInstance
  = ResolvedInstanceByPremise Premise
  | ResolvedInstanceByEnv Instance [Type] [Entailment]
  deriving (Eq, Ord, Show, Data, Typeable)

makeFieldsNoPrefix ''TIState
makeFieldsNoPrefix ''Premise
makeFieldsNoPrefix ''Entailment

instance Plated Entailment

emptyTIState :: Global -> TIState
emptyTIState g = TIState emptySubst mempty ids (filter (`Set.notMember` usedParams) ids)
 where
  usedParams = Set.fromList [id | Parameter id _ <- g^..biplate]

ti :: MonadError Error m => Global -> m Global
ti g = evalStateT ?? emptyTIState g $ runReaderT ?? emptyScope g $ do
  verifyClasses
  verifyInstances
  tiAll g

type TI m = (MonadReader Scope m, MonadState TIState m, MonadError Error m)

verifyClasses :: TI m => m ()
verifyClasses = do
  classes <- view (global.classes)

  forM_ (depGroups $ Map.assocs (fmap fst classes)) $ \case
    [cls] -> do
      superFundeps <- inducedFundeps @Parameter (cls^.superclasses)
      forM_ superFundeps $ \superFundep@(x' :~> y') -> do
        let isStricter (x :~> y) = all (`elem` x') x && all (`elem` y) y'
        unless (any isStricter (cls^.fundeps)) $
          throwError $ FundepsAreWeakerThanSuperclasses cls superFundep
    classes ->
      throwError $ CyclicClasses $ classes^..each.ident.name

verifyInstances :: TI m => m ()
verifyInstances = do
  instances <- view (global.instances)

  forM_ (Map.assocs instances) $ \(classId, insts) -> do
    cls <- resolveUse' classId
    forM_ insts $ \inst -> do
      -- Covering:
      -- To ensure that instance P => C t is valid, we must check that
      -- TV(t_Y) \subseteq (TV(t_X))^+_{F_P} for each (X \leadsto Y) \in F_C .
      let t = indexParams (cls^.parameters) (inst^.arguments)
      let tv' = Set.fromList . tv
      -- We don't need to expand inst^.context by superclasses since
      -- Titan disallows classes whose fundeps are weaker than its superclasses.
      instFundeps <- inducedFundeps @Parameter (inst^.context)
      forM_ (cls^.fundeps) $ \fundep@(x :~> y) ->
        unless (tv' (t y) `Set.isSubsetOf` closure (tv' (t x)) instFundeps) $
          throwError $ CoverageConditionUnsatisfied inst fundep

    forM_ [(a, b) | a:bs <- List.tails insts, b <- bs] $ \(a, b) -> do
      (_, a') <- instantiate a
      (_, b') <- instantiate b

      -- Consistency:
      -- Given a second instance Q => C s, and a dependency (X \leadsto Y) \in F_C ,
      -- then we must ensure that t_Y = s_Y whenever t_X = s_X .
      let t = indexParams (cls^.parameters) (a'^.arguments)
      let s = indexParams (cls^.parameters) (b'^.arguments)
      forM_ (cls^.fundeps) $ \fundep@(x :~> y) -> do
        u <- runExceptT $ mgu (t x) (s x)
        forMOf_ _Right u $ \u ->
          when (apply u (t y) /= apply u (s y)) $
            throwError $ ConsistencyConditionUnsatisfied a b fundep

      -- Eager overlapping check:
      u <- runExceptT $ mgu (a'^.arguments) (b'^.arguments)
      case u of
        Right _ -> throwError $ OverlappingInstances a b
        Left (CannotUnifyType _ _ _) -> return ()
        Left e -> throwError e

  forM_ (Map.assocs instances) $ \(classId, insts) -> do
    cls <- resolveUse' classId
    forM_ insts $ \inst -> do
      (_, inst') <- instantiate inst
      premises <- mapM buildPremise (inst'^.context)
      cls' <- substitute (inst'^.arguments) cls
      mapM_ (verifyEntailment premises) (cls'^.superclasses)

tiAll :: TI m => Global -> m Global
tiAll g = do
  defs' <- tiBindGroup (g^.defs)
  classes' <- scoped defs' $ mapM tiClass (g^.classes)
  constCtx <- use remainingCtx
  mapM_ (verifyEntailment []) constCtx
  return $ g & defs .~ defs' & classes .~ classes'

tiLiteral :: TI m => Type -> Literal -> m Literal
tiLiteral ty l = pure l <* case l of
  LInteger _ -> remainingCtx <>= [CNum ty]
  LChar _ -> unify ty TChar
  LFloat _ -> remainingCtx <>= [CFractional ty]
  LString _ -> unify ty (TListCon :@@ TChar)

tiPattern :: TI m => Type -> Pattern -> m Pattern
tiPattern ty = \case
  PVar def mp ->
    PVar <$> tiUse ty def <*> mapM (tiPattern ty) mp
  PWildcard ->
    return PWildcard
  PDecon vc ps -> do
    cty <- newTVar KType
    ptys <- mapM (\_ -> newTVar KType) ps
    unify (foldr (:-->) ty ptys) cty
    PDecon <$> tiValueCon (length ps) cty vc <*> zipWithM tiPattern ptys ps
  PLit l -> do
    PLit <$> tiLiteral ty l

tiExpr :: TI m => Type -> Expr -> m Expr
tiExpr ty = \case
  EVar id ->
    EVar <$> tiUse ty id
  ECon vc -> do
    ECon <$> tiUse ty vc
  EApp a b -> do
    ta <- newTVar KType
    tb <- newTVar KType
    unify (tb :--> ty) ta
    EApp <$> tiExpr ta a <*> tiExpr tb b
  ELit l ->
    ELit <$> tiLiteral ty l
  ELet binds e -> do
    binds <- scopedLevel $ tiBindGroup binds
    e <- scoped binds $ tiExpr ty e
    return $ ELet binds e
  ELam alts -> do
    let arity = alts^.to NonEmpty.head.patterns.to length
    alts <- mapM (tiAlt arity ty) alts
    rows <- mapM (mapM simplifyPattern) $ toList (fmap (^..patterns.each) alts)
    case PC.check rows of
      PC.Useless ps -> throwError $ UselessPattern $ show ps
      PC.NonExhaustive rows -> throwError $ NonExhaustivePattern $ map show rows
      PC.Complete -> return $ ELam alts

simplifyPattern :: (MonadReader Scope m, MonadError Error m) => Pattern -> m PC.Pat
simplifyPattern = \case
  PVar _ (Just p) -> simplifyPattern p
  PVar _ Nothing -> return PC.Wildcard
  PWildcard -> return PC.Wildcard
  PDecon vc ps -> case vc of
    ValueConData id -> do
      v <- resolveUse' id
      ty <- resolveUse @_ @DataTypeCon (identity v)
      vs <- resolveUse @_ @(Map (Id DataValueCon) DataValueCon) (identity ty)
      ps <- mapM simplifyPattern ps
      let tag v = (v^.ident.name, length (v^.fields))
      return $ PC.Constructor (PC.TagClosed (tag v) (vs^..each.to tag)) ps
    _ ->
      throwError $ InternalError "TI" "Record destructing is not yet implemented"
  PLit l -> return $ PC.Constructor (PC.TagLit l) []

tiAlt :: TI m => Arity -> Type -> Alt -> m Alt
tiAlt arity ty (ps :-> e) = do
  when (length ps /= arity) $ throwError $ ArityMismatch arity (length ps)
  defs <- forM (ps^..biplate) $ \(def :: PatternDef) -> do
    ty <- newTVar KType
    return (def, ty)
  scoped defs $ do
    ety <- newTVar KType
    ptys <- mapM (\_ -> newTVar KType) ps
    unify (foldr (:-->) ety ptys) ty
    (:->) <$> sequence (NonEmpty.zipWith tiPattern ptys ps) <*> tiExpr ety e

tiValueCon :: TI m => Arity -> Type -> ValueCon -> m ValueCon
tiValueCon arity ty = \case
  ValueConData id -> do
    id <- tiUse ty id
    v <- resolveUse' id
    when (length (v^.fields) /= arity) $ throwError $ ArityMismatch (length (v^.fields)) arity
    return $ ValueConData id
  _ ->
    throwError $ InternalError "TI" "Record destructing is not yet implemented"

tiExpl :: TI m => (Scheme, Maybe Expr) -> m (Maybe Expr)
tiExpl (scheme, e) = case e of
  Nothing ->
    return Nothing
  Just e -> inferBlock $ \produce -> do
    scheme <- captureScopedTypeVariables scheme
    ps <- params scheme
    (ptys, scheme) <- instantiate scheme
    e <- scoped (zip ps ptys) $ tiExpr (scheme^.body) e

    produce (scheme^.context) $ do
      s <- use subst
      _ <- consumeDefaultedCtx $ vars topLevel $ apply s (scheme^.body)
      (scheme^.body) <: apply s (scheme^.body)
      return $ Just $ apply s e

tiImpls :: TI m => [(Type, Maybe Expr)] -> m [(Scheme, Maybe Expr)]
tiImpls impls = inferBlock $ \produce -> do
  impls <- forM impls $ \(ty, e) -> case e of
    Nothing ->
      return (ty, Nothing)
    Just e -> do
      e <- tiExpr ty e
      return (ty, Just e)

  produce [] $ do
    s <- use subst
    let impls' = map (first (apply s)) impls
    -- We can determine the ambiguity of type variables from every use-site only if
    -- the ambiguous variables appear in all type signatures.
    defaultedCtx <- consumeDefaultedCtx $ foldr1 Set.intersection $ map (vars topLevel . fst) impls'
    retainedCtx <- consumeRemainingCtx
    forM impls' $ \(ty, e) -> do
      let relates p = not $ Set.disjoint (vars @Type topLevel ty) (vars topLevel p)
      let ctx = retainedCtx <> filter relates defaultedCtx
      (params, s') <- quantify (ty, ctx)
      return $ apply (extend s' s) (Scheme (Typed Explicit params) ty ctx, e) & _1.context %~ List.sort

class (Data a, Scoped a, Identified a) => BindItem a where
  bindItem :: Lens' a (Typing Scheme, Maybe Expr)

instance BindItem LocalDef where
  bindItem = lens load store
   where
    load def = (def^.scheme, def^.body)
    store def (s, e) = def & scheme .~ s & body .~ e

instance BindItem Def where
  bindItem = lens load store
   where
    load def = (def^.scheme, def^.body)
    store def (s, e) = def & scheme .~ s & body .~ e

instance BindItem ClassMethod where
  bindItem = lens load store
   where
    load cm = (Typed Explicit (cm^.scheme), cm^.defaultBody)
    store cm (s, e) = cm & scheme .~ s^?!typed & defaultBody .~ e

-- TODO: Refactor this
tiBindGroup :: (BindItem a, Traversable f, TI m) => f a -> m (f a)
tiBindGroup binds = do
  let dest = Map.fromList [(identity bind, bind) | bind <- toList binds]
  let items = [(identity bind, bind^.bindItem) | bind <- toList binds]
  dest <- foldM tiImpls' dest $ depGroups [(id, (id, e)) | (id, (Untyped, e)) <- items]
  dest <- foldM tiExpl' dest [(id, (scheme, e)) | (id, (Typed _ scheme, e)) <- items]
  return $ fmap (\bind -> dest^?!ix (identity bind)) binds
 where
  tiImpls' map ides = scoped map $ do
    let (ids, es) = unzip ides
    tys <- mapM (\_ -> newTVar KType) es
    let tmpMap = [map^?!ix id & bindItem .~ (Typed Inferred (Scheme (Typed Explicit []) ty []), e) | (id, ty, e) <- zip3 ids tys es]
    impls <- scoped tmpMap $ tiImpls $ zip tys es
    return $ foldr ($) map [ix id.bindItem .~ (Typed Inferred s, e) | (id, (s, e)) <- zip ids impls]
  tiExpl' map (id, expl) = scoped map $ do
    e <- tiExpl expl
    return $ map & ix id.bindItem._2 .~ e

tiClass :: TI m => Class -> m Class
tiClass (cls, cms) = inferBlock $ \produce -> do
  ps <- params cls
  (ptys, _) <- instantiate cls
  cms <- scoped (zip ps ptys) $ scopedLevel $ tiBindGroup cms

  produce [CClass (identity cls) ptys] $ do
    s <- use subst
    _ <- consumeDefaultedCtx $ vars topLevel (apply s ptys)
    return (cls, cms)

tiUse :: (TypeOf a, TI m) => Type -> a -> m a
tiUse ty a = do
  scheme <- typeOf a
  (_, scheme) <- instantiate scheme
  remainingCtx <>= scheme^.context
  unify ty (scheme^.body)
  return a

inferBlock :: TI m => (([Constraint] -> m a -> m a) -> m a) -> m a
inferBlock body = stashCtx (const True) (body produce)
 where
  produce premises m = do
    s <- use subst
    ctx <- use remainingCtx
    ctx <- reduceContext (apply s premises) (apply s ctx)
    remainingCtx .= ctx
    lv <- view level
    stashCtx (null . vars @Type lv) (m <* verifyNoRemainingCtx premises)
  stashCtx cond m = do
    deferredCtx <- remainingCtx %%= List.partition cond
    result <- m
    remainingCtx <>= deferredCtx
    return result

consumeDefaultedCtx :: TI m => Set (Id Type) -> m [Constraint]
consumeDefaultedCtx excludedVars = do
  ctx <- use remainingCtx
  defaultedCtx <- resolveAmbiguities excludedVars ctx
  remainingCtx .= ctx List.\\ defaultedCtx
  return defaultedCtx

consumeRemainingCtx :: TI m => m [Constraint]
consumeRemainingCtx = remainingCtx %%= \ctx -> (ctx, [])

verifyNoRemainingCtx :: TI m => [Constraint] -> m ()
verifyNoRemainingCtx premises = do
  ctx <- use remainingCtx
  forM_ ctx $ \p -> do
    s <- use subst
    throwError $ NoMatchingInstances (apply s premises) p

resolveAmbiguities :: TI m => Set (Id Type) -> [Constraint] -> m [Constraint]
resolveAmbiguities excludedVars context = do
  contextFundeps <- inducedFundeps @Type context
  let excludedVars' = closure excludedVars contextFundeps

  dflt <- view (global.defaultTypes)
  let candidateTys = dflt^..each.candidates.each

  lv <- view level
  let ambiguousVars = vars @Type lv context Set.\\ excludedVars'
  defaults <- forM (toList ambiguousVars) $ \var -> do
    let relatedCtx = [p | p <- context, Set.member var (vars @Type lv p)]
    acceptedTys <- filterM (accept var relatedCtx) candidateTys
    case acceptedTys of
      ty:_ -> return (ty, relatedCtx)
      _ -> throwError $ CannotResolveAmbiguity var relatedCtx

  return (defaults^..each._2.each)
 where
  accept var ctx ty = do
    k <- kindOf ty
    tests <- forM ctx $ \case
      CClass cls [TVar var' k' _] | var == var' && k == k' -> do
        entail <- buildEntailment [] (CClass cls [ty])
        return (entail^.complete)
      _ -> return False
    return $ and tests

reduceContext :: TI m => [Constraint] -> [Constraint] -> m [Constraint]
reduceContext ps es = do
  premises <- mapM buildPremise ps
  entails <- mapM (buildEntailment premises) es
  cache <- foldlMOf (each.ensures.each) improveByPredicates mempty premises
  reduce premises entails cache entails
 where
  reduce premises entails cache = \case
    [] -> return $ nubOrd [p | entail <- entails, p <- expand entail]
    diff -> do
      mapMOf_ (each.cosmos.constraint) improveByInstances diff
      cache <- foldlMOf (each.cosmos.constraint) improveByPredicates cache diff
      s <- use subst
      (entails, diff) <- runWriterT $ mapM (updateEntailment premises s) entails
      reduce premises entails cache diff
  expand entail = if
    | entail^.complete -> []
    | otherwise -> case entail^.resolvedInstance of
        Just (ResolvedInstanceByEnv _ _ es) -> es >>= expand
        _ -> [entail^.constraint]

verifyEntailment :: TI m => [Premise] -> Constraint -> m ()
verifyEntailment premises p = do
  entail <- buildEntailment premises p
  unless (entail^.complete) $ throwError $ NoMatchingInstances (map (^.constraint) premises) p

buildEntailment :: TI m => [Premise] -> Constraint -> m Entailment
buildEntailment premises p = build 0 p
 where
  build recur p = produceEntailment p <$> if
    | recur > 200 ->
        throwError $ InstanceResolutionExhausted p
    | otherwise ->
        case [premise | premise <- premises, q <- premise^.ensures, q == p] of
          premise:_ ->
            return $ Just $ ResolvedInstanceByPremise premise
          [] ->
            matchingInstances p >>= \case
              [(inst, args)] -> do
                inst' <- substitute args inst
                es <- mapM (build (succ recur)) (inst'^.context)
                return $ Just $ ResolvedInstanceByEnv inst args es
              [] ->
                return Nothing
              _ ->
                throwError $ InternalError "TI" "There exists overlapping instances"

updateEntailment :: (TI m, MonadWriter [Entailment] m) => [Premise] -> Subst Type -> Entailment -> m Entailment
updateEntailment premises s entail = update entail
 where
  update entail = if
    | worthApply s (entail^.wantVars) -> do
        let p = apply s (entail^.constraint)
        entail' <- case entail^.resolvedInstance of
          Just (ResolvedInstanceByEnv inst args es) -> do
            es <- mapM update es
            return $ produceEntailment p $ Just $ ResolvedInstanceByEnv inst args es
          Just (ResolvedInstanceByPremise _) ->
            return entail
          Nothing ->
            buildEntailment premises p
        tell [entail']
        return entail'
    | otherwise ->
        return entail

produceEntailment :: Constraint -> Maybe ResolvedInstance -> Entailment
produceEntailment p ri = Entailment p ri allVars allComplete
 where
  (allVars, allComplete) = case ri of
    Just (ResolvedInstanceByEnv _ _ es) ->
      (Set.unions [e^.wantVars | e <- es], all (^.complete) es)
    Just (ResolvedInstanceByPremise _) ->
      (mempty, True)
    Nothing ->
      (vars @Type topLevel p, False)

matchingInstances :: TI m => Constraint -> m [(Instance, [Type])]
matchingInstances = \case
  CClass id args -> do
    insts <- resolveUse @_ @[Instance] id
    insts <- forM insts $ \inst -> do
      (vs, inst') <- instantiate inst
      s <- runExceptT $ match (inst'^.arguments) args
      case s of
        Right s -> return $ Just (inst, apply s vs)
        Left MatchFailed -> return Nothing
        Left e -> throwError e
    return $ catMaybes insts

improveByInstances :: TI m => Constraint -> m ()
improveByInstances = \case
  CClass id args -> do
    cls <- resolveUse' id
    insts <- resolveUse @_ @[Instance] id
    insts' <- forM insts $ \inst -> do
      (_, inst') <- instantiate inst
      return inst'
    forM_ (cls^.fundeps) $ \(x :~> y) ->
      forM_ insts' $ \inst' -> do
        let t' = indexParams (cls^.parameters) (inst'^.arguments)
        let t = indexParams (cls^.parameters) args
        s <- runExceptT $ match (t' x) (t x)
        -- TODO: Once we found an instance, we don't need to search further instance anymore.
        case s of
          Right s -> zipWithM_ unify (apply s (t' y)) (t y)
          Left _ -> return ()

type PredicateCache = Map (Id ClassCon, Fundep Parameter, [Type]) [Type]

improveByPredicates :: TI m => PredicateCache -> Constraint -> m PredicateCache
improveByPredicates cache = \case
  CClass id args -> do
    cls <- resolveUse' id
    let t = indexParams (cls^.parameters) args
    foldM merge cache [((id, fundep, t x), t y) | fundep@(x :~> y) <- cls^.fundeps]
 where
  merge cache (k, v) = cache & at k %%~ \case
    Just v' -> do
      zipWithM_ unify v v'
      return $ Just v'
    Nothing -> return $ Just v

buildPremise :: TI m => Constraint -> m Premise
buildPremise p = Premise p <$> expand p
 where
  expand p = do
    supers <- supers p
    ps <- mapM expand supers
    return (p : concat ps)
  supers = \case
    CClass id args -> do
      cls <- resolveUse' id
      cls <- substitute args cls
      return (cls^.superclasses)

quantify :: (Data a, TI m) => a -> m ([Parameter], Subst Type)
quantify a = do
  lv <- view level
  let vs = nubOrd [(id, k) | TVar id k lv' <- universeOn biplate a, isOnLevel lv lv']
  params <- sequence [(,) id <$> newParameter k | (id, k) <- vs]
  let s = Subst $ Map.fromList [(id, TGen (identity p)) | (id, p) <- params]
  return (map snd params, s)

instantiate :: (Parameterized a, TI m) => a -> m ([Type], a)
instantiate a = do
  ps <- params a
  vs <- mapM (kindOf >=> newTVar) ps
  a <- substitute vs a
  return (vs, a)

class Parameterized a where
  params :: MonadError Error m => a -> m [Parameter]
  substitute :: MonadError Error m => [Type] -> a -> m a

  default substitute :: (Data a, MonadError Error m) => [Type] -> a -> m a
  substitute args a = do
    ps <- params a
    let map = Map.fromList [(identity p, ty) | (p, ty) <- zip ps args]
    return $ transformOn biplate ?? a $ \case
      TGen id | Just t <- map^.at id -> t
      t -> t

instance Parameterized Scheme where
  params scheme = return $ scheme^..quantification.typed.each

instance Parameterized ClassCon where
  params cls = return $ cls^.parameters

instance Parameterized Instance where
  params inst = case inst^?quantification.typed of
    Just params -> pure params
    Nothing -> throwError $ InternalError "Resolver" "Escaped untyped parameters"

unify :: TI m => Type -> Type -> m ()
unify t1 t2 = do
  s <- use subst
  s' <- mgu (apply s t1) (apply s t2)
  subst %= extend s'

(<:) :: TI m => Type -> Type -> m ()
l <: r = void $ match r l `catchError` \case
  MatchFailed -> throwError $ CannotUnifyType l r SignatureTooGeneral
  err -> throwError err

newTVar :: (MonadReader Scope m, MonadState TIState m) => Kind -> m Type
newTVar k = do
  lv <- view level
  newTVarOnLevel lv k

newTVarOnLevel :: MonadState TIState m => Level -> Kind -> m Type
newTVarOnLevel lv k = typeIds %%= \ids -> (TVar (head ids) k lv, tail ids)

newParameter :: MonadState TIState m => Kind -> m Parameter
newParameter k = parameterIds %%= \ids -> (Parameter (head ids) (Typed Inferred k), tail ids)

-- Compute the most general unifier.
mgu :: (Data t, TI m) => t -> t -> m (Subst Type)
mgu a b = mguElems emptySubst (a^..biplate) (b^..biplate)
 where
  mguElems s (a:as) (b:bs) = do
    s' <- mgu' (apply s a) (apply s b)
    mguElems (extend s' s) as bs
  mguElems s [] [] = return s
  mguElems _ _ _ = throwError $ InternalError "KI" "Structure mismatch"
  mgu' a b = case (a, b) of
    (Row fa a, Row fb b) | not (null fa) && not (null fb) -> do
      let (u, fa', fb') = unifyLabels fa fb
      let (as, bs) = unzip (toList u)
      if null fa' || null fb' then
        mgu (as ++ [Row fa' a]) (bs ++ [Row fb' b])
      else do
        s <- mgu as bs

        (a, fb') <- pure $ apply s (a, fb')
        tv <- case a of
          TVar _ k lv -> newTVarOnLevel lv k
          _ -> newTVar (KRow KType) -- dummy

        s' <- mgu' a (Row fb' tv)

        when (worthApply s' (vars topLevel b)) $ throwError $ CannotUnifyType a (Row fb' tv) OccursCheckFailed
        (b, fa') <- pure $ apply (extend s' s) (b, fa')

        s'' <- mgu' b (Row fa' tv)

        return $ extend s'' $ extend s' s
    (TApp l r, TApp l' r') -> mgu [l, r] [l', r']
    (TVar id k lv, t) -> varBind (id, k, lv) t
    (t, TVar id k lv) -> varBind (id, k, lv) t
    (a, b) -> do
      when (a /= b) $ throwError $ CannotUnifyType a b Mismatch
      return emptySubst
  varBind (id, k, lv) t = if
    | t == TVar id k lv ->
        return emptySubst
    | occurs id t ->
        throwError $ CannotUnifyType (TVar id k lv) t OccursCheckFailed
    | otherwise -> do
        tk <- kindOf t
        when (k /= tk) $ throwError $ InternalError "KI" "Kind mismatch"
        adjustedVars <- sequence [(,) id' <$> newTVarOnLevel lv k' | TVar id' k' lv' <- universe t, isOnLevel (upLevel lv) lv']
        return $ Subst $ Map.fromList $ (id, t) : adjustedVars

-- Compute a substitution from lhs to rhs.
-- If there are no suitable substitution, MatchFailed is thrown.
match :: (Data t, TI m) => t -> t -> m (Subst Type)
match a b = matchElems emptySubst (a^..biplate) (b^..biplate)
 where
  matchElems (Subst s) (a:as) (b:bs) = do
    Subst s' <- match' a b
    if and [s'^.at id == s^.at id | id <- Map.keys $ Map.intersection s' s]
      then matchElems (Subst (Map.union s' s)) as bs
      else throwError MatchFailed
  matchElems s [] [] = return s
  matchElems _ _ _ = throwError MatchFailed
  match' a b = case (a, b) of
    (TVar id k lv, t) -> do
      k' <- kindOf t
      when (k /= k') $ throwError MatchFailed
      let adjustRequiredVars = [id' | TVar id' _ lv' <- universe t, isOnLevel (upLevel lv) lv']
      unless (null adjustRequiredVars) $ throwError MatchFailed
      return $ id +-> t
    (Row fa a, Row fb b) | not (null fa) && not (null fb) -> do
      let (u, fa', fb') = unifyLabels fa fb
      unless (null fa') $ throwError MatchFailed
      let (as, bs) = unzip (toList u)
      match (as ++ [a]) (bs ++ [Row fb' b])
    (TApp l r, TApp l' r') -> match [l, r] [l', r']
    (a, b) -> do
      when (a /= b) $ throwError MatchFailed
      return emptySubst
