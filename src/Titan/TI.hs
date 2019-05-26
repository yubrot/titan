module Titan.TI
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
import Titan.Subst
import Titan.DependencyAnalyzer (depGroups)

data TIState = TIState
  { _subst :: Subst Type
  , _currentCtx :: [Constraint]
  , _typeIds :: [Id Type]
  , _parameterIds :: [Id Parameter]
  }

emptyTIState :: Global -> TIState
emptyTIState g = TIState emptySubst mempty ids (filter (`Set.notMember` usedParams) ids)
 where
  usedParams = Set.fromList [id | Parameter id _ <- g^..biplate]

makeFieldsNoPrefix ''TIState

ti :: MonadError Error m => Global -> m Global
ti g = evalStateT ?? emptyTIState g $ runReaderT ?? emptyScope g $ do
  verifyClasses
  verifyInstances
  tiAll g

type TI m = (MonadReader Scope m, MonadState TIState m, MonadError Error m)

verifyClasses :: TI m => m ()
verifyClasses = do
  classes <- view (global.classes)
  let classDepGroups = depGroups $ Map.assocs (classes & traverse._2 .~ mempty)
  forM_ (classDepGroups :: [[Class]]) $ \case
    [_] -> return ()
    classes -> throwError $ CyclicClasses $ classes^..each._1.ident.name

verifyInstances :: TI m => m ()
verifyInstances = do
  instances <- view (global.instances)
  forM_ [(a, b) | insts <- instances^..traverse, a:bs <- List.tails insts, b <- bs] $ \(a, b) -> do
    (_, a') <- instantiate a
    (_, b') <- instantiate b
    s <- runExceptT $ mgu @Type (a'^.arguments) (b'^.arguments)
    case s of
      Right _ -> throwError $ OverlappingInstances a b
      Left (CannotUnifyType _ _ _) -> return ()
      Left e -> throwError e

tiAll :: TI m => Global -> m Global
tiAll g = do
  defs' <- tiBindGroup (g^.defs)
  classes' <- scoped defs' $ mapM tiClass (g^.classes)
  ctx <- use currentCtx
  mapM_ (entail []) ctx
  return $ g & defs .~ defs' & classes .~ classes'

tiLiteral :: TI m => Type -> Literal -> m Literal
tiLiteral ty l = pure l <* case l of
  LInteger _ -> currentCtx <>= [CNum ty]
  LChar _ -> unify ty TChar
  LFloat _ -> currentCtx <>= [CFractional ty]
  LString _ -> unify ty (TListCon @@ TChar)

tiPattern :: TI m => Type -> Pattern -> m Pattern
tiPattern ty = \case
  PVar def mp ->
    PVar <$> tiUse ty def <*> mapM (tiPattern ty) mp
  PWildcard ->
    return PWildcard
  PDecon vc ps -> do
    -- FIXME: arity check required (partial application is diallowed)
    cty <- newTVar KType
    ptys <- mapM (\_ -> newTVar KType) ps
    unify (foldr (-->) ty ptys) cty
    PDecon <$> tiUse cty vc <*> zipWithM tiPattern ptys ps
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
    unify (tb --> ty) ta
    EApp <$> tiExpr ta a <*> tiExpr tb b
  ELit l ->
    ELit <$> tiLiteral ty l
  ELet binds e -> do
    binds <- scopedLevel $ tiBindGroup binds
    e <- scoped binds $ tiExpr ty e
    return $ ELet binds e
  ELam alts ->
    ELam <$> mapM (tiAlt ty) alts

tiAlt :: TI m => Type -> Alt -> m Alt
tiAlt ty (ps :-> e) = do
  defs <- forM (ps^..biplate) $ \(def :: PatternDef) -> do
    ty <- newTVar KType
    return (def, ty)
  scoped defs $ do
    ety <- newTVar KType
    ptys <- mapM (\_ -> newTVar KType) ps
    unify (foldr (-->) ety ptys) ty
    (:->) <$> sequence (NonEmpty.zipWith tiPattern ptys ps) <*> tiExpr ety e

tiExpl :: TI m => (Scheme, Maybe Expr) -> m (Maybe Expr)
tiExpl (scheme, e) = splitInferCtx $ case e of
  Nothing ->
    return Nothing
  Just e -> do
    scheme <- captureScopedTypeVariables scheme
    ps <- params scheme
    (ptys, scheme) <- instantiate scheme
    e <- scoped (zip ps ptys) $ tiExpr (scheme^.body) e
    s <- use subst

    -- schemeTy <: inferredTy'
    let inferredTy' = apply s (scheme^.body)
    let schemeTy = scheme^.body
    void $ match @Type inferredTy' schemeTy `catchError` \case
      MatchFailed -> throwError $ CannotUnifyType schemeTy inferredTy' SignatureTooGeneral
      err -> throwError err

    -- entail schemeCtx' inferredCtx'
    inferredCtx' <- apply s <$> use currentCtx
    let schemeCtx' = apply s (scheme^.context)
    unEntailedCtx <- filterM (fmap not . canEntail schemeCtx') inferredCtx'
    let excludedVars = vars topLevel inferredTy'
    SplitCtx { deferredCtx, retainedCtx } <- splitCtx excludedVars unEntailedCtx
    currentCtx .= deferredCtx

    case retainedCtx of
      [] -> return $ Just $ apply s e
      p:_ -> throwError $ NoMatchingInstances schemeCtx' p

tiImpls :: TI m => [(Type, Maybe Expr)] -> m [(Scheme, Maybe Expr)]
tiImpls impls = splitInferCtx $ do
  impls <- forM impls $ \(ty, e) -> case e of
    Nothing ->
      return (ty, Nothing)
    Just e -> do
      e <- tiExpr ty e
      return (ty, Just e)
  s <- use subst

  inferredCtx' <- apply s <$> use currentCtx
  let impls' = map (first (apply s)) impls
  -- We can determine the ambiguity of type variables from every use-site only if
  -- the ambiguous variables appear in all type signatures.
  let excludedVars = foldr1 Set.intersection $ map (vars topLevel . fst) impls'
  SplitCtx { deferredCtx, retainedCtx, defaultedCtx } <- splitCtx excludedVars inferredCtx'
  currentCtx .= deferredCtx

  impls <- forM impls' $ \(ty, e) -> do
    let relates p = not $ Set.disjoint (vars @Type topLevel ty) (vars topLevel p)
    let ctx = retainedCtx <> filter relates defaultedCtx
    (params, s') <- quantify (ctx, ty)
    return $ apply (extend s' s) (Scheme (Typed Explicit params) ty ctx, e)
  return impls

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
tiClass (cls, cms) = splitInferCtx $ do
  ps <- params cls
  (ptys, _) <- instantiate cls
  cms <- scoped (zip ps ptys) $ scopedLevel $ tiBindGroup cms
  s <- use subst

  let ptys' = apply s ptys
  inferredCtx' <- apply s <$> use currentCtx
  let classCtx = [CClass (identity cls) ptys']
  unEntailedCtx <- filterM (fmap not . canEntail classCtx) inferredCtx'
  let excludedVars = vars topLevel ptys'
  SplitCtx { deferredCtx, retainedCtx } <- splitCtx excludedVars unEntailedCtx
  currentCtx .= deferredCtx

  case retainedCtx of
    [] -> return (cls, cms)
    p:_ -> throwError $ NoMatchingInstances classCtx p

tiUse :: (TypeOf a, TI m) => Type -> a -> m a
tiUse ty a = do
  scheme <- typeOf a
  (_, scheme) <- instantiate scheme
  currentCtx <>= scheme^.context
  unify ty (scheme^.body)
  return a

data SplitCtx = SplitCtx
  { deferredCtx :: [Constraint]
  , retainedCtx :: [Constraint]
  , defaultedCtx :: [Constraint]
  }

splitCtx :: TI m => Set (Id Type) -> [Constraint] -> m SplitCtx
splitCtx excludedVars ctx = do
  lv <- view level
  let (deferredCtx, retainedCtx) = List.partition (null . vars @Type lv) ctx
  (_, defaultedCtx) <- defaults excludedVars retainedCtx
  return $ SplitCtx { deferredCtx, retainedCtx = retainedCtx List.\\ defaultedCtx, defaultedCtx }

defaults :: TI m => Set (Id Type) -> [Constraint] -> m (Subst Type, [Constraint])
defaults excludedVars ctx = do
  dflt <- view (global.defaultTypes)
  lv <- view level
  let candidateTys = dflt^..each.candidates.each
  let ambiguousVars = vars lv ctx Set.\\ excludedVars
  defaults <- sequence $ Map.fromSet ?? ambiguousVars $ \var -> do
    let relatedCtx = [p | p <- ctx, Set.member var (vars lv p)]
    acceptedTys <- filterM (accept var relatedCtx) candidateTys
    case acceptedTys of
      ty:_ -> return (ty, relatedCtx)
      [] -> throwError $ CannotResolveAmbiguity ("_" ++ var^.name) relatedCtx
  return (Subst $ fmap (^._1) defaults, defaults^..each._2.each)
 where
  accept var ctx ty = do
    k <- kindOf ty
    tests <- forM ctx $ \case
      CClass cls [TVar var' k' _] | var == var' && k == k' -> canEntail [] (CClass cls [ty])
      _ -> return False
    return $ and tests

data ResolvedInstance
  = ResolvedInstanceByPremise Constraint
  | ResolvedInstanceByEnv Instance [Type] [ResolvedInstance]
  deriving (Eq, Ord, Show, Data, Typeable)

canEntail :: TI m => [Constraint] -> Constraint -> m Bool
canEntail ps p = do
  resolvedInst <- runExceptT $ entail ps p
  case resolvedInst of
    Right _ -> return True
    Left (NoMatchingInstances _ _) -> return False
    Left e -> throwError e

entail :: TI m => [Constraint] -> Constraint -> m ResolvedInstance
entail ps p = do
  qss <- mapM expandPremises ps
  let
    premises = Map.fromList [(q, p) | (p, qs) <- zip ps qss, q <- qs]
    entail' [] p = throwError $ NoMatchingInstances ps p
    entail' (_:cap) p = case premises^.at p of
      Just p ->
        return $ ResolvedInstanceByPremise p
      Nothing ->
        resolveInstances p >>= \case
          [(inst, tys)] -> do
            inst' <- substitute tys inst
            contextInsts <- mapM (entail' cap) (inst'^.context)
            return $ ResolvedInstanceByEnv inst tys contextInsts
          [] ->
            throwError $ NoMatchingInstances ps p
          _ ->
            throwError $ InternalError "TI" "There exists overlapping instances"
  entail' (replicate 200 ()) p
 where

expandPremises :: TI m => Constraint -> m [Constraint]
expandPremises p = do
  supers <- expandSupers p
  ps <- mapM expandPremises supers
  return (p : concat ps)

expandSupers :: TI m => Constraint -> m [Constraint]
expandSupers = \case
  CClass id tys -> do
    cls <- resolveUse' id
    cls <- substitute tys cls
    return (cls^.superclasses)

resolveInstances :: TI m => Constraint -> m [(Instance, [Type])]
resolveInstances = \case
  CClass id tys -> do
    insts <- resolveUse @_ @[Instance] id
    insts <- forM insts $ \inst -> runExceptT $ do
      (vs, inst') <- instantiate inst
      s <- match @Type (inst'^.arguments) tys
      return (inst, apply s vs)
    return $ rights insts

instantiate :: (Parameterized a, TI m) => a -> m ([Type], a)
instantiate a = do
  ps <- params a
  vs <- mapM (kindOf >=> newTVar) ps
  a <- substitute vs a
  return (vs, a)

quantify :: (Data a, TI m) => a -> m ([Parameter], Subst Type)
quantify a = do
  lv <- view level
  let vs = nubOrd [(id, k) | TVar id k lv' <- universeOn biplate a, isOnLevel lv lv']
  params <- sequence [(,) id <$> newParameter k | (id, k) <- vs]
  let s = Subst $ Map.fromList [(id, TGen (identity p)) | (id, p) <- params]
  return (map snd params, s)

class Parameterized a where
  params :: MonadError Error m => a -> m [Parameter]
  substitute :: MonadError Error m => [Type] -> a -> m a

  default substitute :: (Data a, MonadError Error m) => [Type] -> a -> m a
  substitute tys a = do
    ps <- params a
    let map = Map.fromList [(identity p, ty) | (p, ty) <- zip ps tys]
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

splitInferCtx :: TI m => m a -> m a
splitInferCtx m = do
  stashedCtx <- currentCtx %%= \ctx -> (ctx, [])
  r <- m
  currentCtx %= \ctx -> ctx <> stashedCtx
  return r

unify :: TI m => Type -> Type -> m ()
unify t1 t2 = do
  s <- use subst
  s' <- mgu (apply s t1) (apply s t2)
  subst %= extend s'

newTVar :: (MonadReader Scope m, MonadState TIState m) => Kind -> m Type
newTVar k = do
  lv <- view level
  typeIds %%= \ids -> (TVar (head ids) k lv, tail ids)

newParameter :: (MonadState TIState m) => Kind -> m Parameter
newParameter k = parameterIds %%= \ids -> (Parameter (head ids) (Typed Inferred k), tail ids)
