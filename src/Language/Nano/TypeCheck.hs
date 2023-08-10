{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars TInt             = []
  freeTVars TBool            = [] 
  freeTVars (TList t)        = freeTVars t
  freeTVars (TVar t)         = [t]
  freeTVars (TList (TVar t)) = [t]
  freeTVars (t1 :=> t2)     = (L.nub ((freeTVars t1) ++ (freeTVars t2)))


-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars (Mono t)      = freeTVars t
  freeTVars (Forall as t) = freeTVars t L.\\ [as]
-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar a [] = TVar a
lookupTVar a ((v, t):xs)
  | v == a = t
  | otherwise = lookupTVar a xs
-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar _ [] = []
removeTVar a (x: xs)
  | (a == fst(x)) = xs
  | otherwise = [x] ++ (removeTVar a xs)
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply _ (TInt)          = TInt
  apply _ (TBool)         = TBool
  apply sub (TVar ttvar)  = (lookupTVar ttvar sub)
  apply sub (t1 :=> t2)   = (apply sub t1) :=> (apply sub t2)
  apply sub (TList tlist) = TList (apply sub tlist)
  apply _ t               = t
-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply sub (Mono t) = Mono (apply sub t)
  apply sub (Forall t p) = Forall t (apply sub' p)
    where
      sub' = (removeTVar t sub)

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst sub a t = returnedSubst
  where
    extendHelper(a', t') = (a', (apply([(a, (apply sub t))]) t'))
    mappedExtend = mapHelper extendHelper sub (a, t)
    returnedSubst = [(a, (apply sub t))] ++ mappedExtend

mapHelper func subList x = if (subList == [])
                          then [x]
                          else (map func subList)
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
--unifyTVar :: InferState -> TVar -> Type -> InferState
--unifyTVar st a t
--  | (TVar a == t)                           = st
--  | ((lookupTVar a (stSub st)) /= (TVar a)) = (unify st (lookupTVar a (stSub st)) t)
--  | (a `elem` (freeTVars t))                = throw(Error("type error: cannot uniify " ++ a ++ " and " ++ (show t) ++ " (occurs check)"))
--  | otherwise                               = extendState st a t
unifyTVar :: InferState -> TVar -> Type -> InferState
--unifyTVar st a t = error "TBD: unifyTVar"
unifyTVar st a t 
  | (TVar a == t)                           = st
  | ((lookupTVar a (stSub st)) /= (TVar a)) = (unify st (lookupTVar a (stSub st)) t)
  | (a `elem` (freeTVars t))                = throw(Error("type error: cannot unify "++a++" and "++(show t)++" (occurs check)"))
  | otherwise                               = extendState st a t
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
--unify :: InferState -> Type -> Type -> InferState
--unify st TInt TInt             = st
--unify st TBool TBool           = st
--unify st t1 (TVar t)           = unifyTVar st t t1
--unify st (TVar t) t1           = unifyTVar st t t1
--unify st (TList t1) (TList t2) = unify st t1 t2
--unify st (t1:=>t2) (t3:=>t4)   = (unify (unify st t2 t4) t1 t3)
--unify st a b                   = throw (Error ("type error: cannot unify " ++ (typeString a) ++ " and " ++ (typeString b) ++ " here"))
unify :: InferState -> Type -> Type -> InferState
--unify st t1 t2 = error "TBD: unify"
unify st TInt TInt              = st
unify st TBool TBool            = st
unify st t1 (TVar t)            = unifyTVar st t t1
unify st (TVar t) t1            = unifyTVar st t t1
unify st (TList t1) (TList t2)  = unify st t1 t2
unify st (t1:=>t2) (t3:=>t4)    = (unify (unify st t2 t4) t1 t3) --trace ("t1") (unify (unify st t1 t3) t2 t4)
unify st a b                    = throw (Error ("type error: cannot unify " ++ (show a) ++ " and " ++ (show b) ++ " (occurs check)"))

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _   (EInt _)          = (st, TInt)
infer st _   (EBool _)         = (st, TBool)

infer st gamma (EVar x)        = (newInferState, instantiateType)
  where 
    (instantiateInt, instantiateType)        = (instantiate (stCnt st) (lookupVarType x gamma))
    newInferState = InferState (stSub st) instantiateInt

-- The class slides helped me get this solution
infer st gamma (ELam x body)   = (st', var' :=> tBody)
  where 
    newInferState  = InferState (stSub st) ((stCnt st)+ 1)
    fresh          = freshTV (stCnt st)
    gamma'         = extendTypeEnv x (Mono fresh) gamma
    (st', tBody)   = infer newInferState gamma' body
    var'           = apply (stSub st') fresh

infer st gamma (EApp e1 e2) = (newState3, var)
  where
    newInferState         = InferState (stSub st) ((stCnt st)+1) --Lucas (MSI Tutor) told me about this
    (TVar fresh)          = freshTV (stCnt st)
    (newState1, fType)    = infer newInferState gamma e1
    (newState2, aType)    = infer newState1 gamma e2
    argType               = (aType :=> (TVar fresh))
    newState3             = unify newState2 fType argType
    var                   = lookupTVar fresh (stSub newState3)

infer st gamma (ELet x e1 e2)  = (infSt2, infType2)
  where
    (infSt1, infType1)     = (infer newInferState newGamma e1)
    (infSt2, infType2)     = (infer unificationInferState newEnv e2)
    newPolyType            = (generalize newGamma infType1) 
    newEnv                 = (extendTypeEnv x newPolyType newGamma)
    newGamma               = (extendTypeEnv x (Mono fresh) gamma)
    fresh                  = (freshTV (stCnt st))
    TVar freshTVar         = fresh
    newInferState          = InferState (stSub st) ((stCnt st)+1)
    unificationInferState  = unify infSt1 (fresh) infType1

{--  --- Non-Recursive Let ---
infer st gamma (ELet x e1 e2)  = (infSt2, infType2)
  where
    inferState1     = (infer st gamma e1)
    infSt1          = (fst inferState1)
    infType1        = (snd inferState1)
    inferState2     = (infer infSt1 newEnv e2)
    infSt2          = (fst inferState2)
    infType2        = (snd inferState2)
    newPolyType     = (generalize gamma infType1) 
    newEnv          = (extendTypeEnv x newPolyType gamma)
--}

infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
--generalize :: TypeEnv -> Type -> Poly
--generalize [] t = (Mono t)
--generalize gamma t = generalizeHelp base args
--  where
--    generalizeHelp [] t     = (Mono t)
--    generalizeHelp (x:xs) t = (Forall x (generalizeHelp xs t))
--    base                    = L.nub ((freeTVars t) L.\\ (freeTVars gamma))
--    args                    = t
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = generalizeFold t xs
  where
    ft = freeTVars t
    fg = freeTVars gamma
    xs = (ft L.\\ fg)

generalizeFold :: Type -> [TVar] -> Poly
generalizeFold t [] = Mono t
generalizeFold t (x:xs)
  | xs == [] = Forall x (Mono t)
  | otherwise = Forall x (generalizeFold t xs)
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n (Mono t) = (n, t)
instantiate n (Forall id p) = instantiate (n+1) (apply [(id, freshTV n)] p)
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    Mono $ TInt :=> TInt :=> TInt)
  , ("*",    Mono $ TInt :=> TInt :=> TInt)
  , ("/",    Mono $ TInt :=> TInt :=> TInt)
  , ("==",   Forall "t" (Mono $ ("t") :=> ("t") :=> TBool))
  , ("!=",   Forall "t" (Mono $ ("t") :=> ("t") :=> TBool))
  , ("<",    Mono $ TInt :=> TInt :=> TBool)
  , ("<=",   Mono $ TInt :=> TInt :=> TBool)
  , ("&&",   Mono $ TBool :=> TBool :=> TBool)
  , ("||",   Mono $ TBool :=> TBool :=> TBool)
  , ("if",   Forall "t" (Mono $ TBool :=> ("t") :=> ("t") :=> ("t")))
  -- lists: 
  , ("[]",   Forall "t" (Mono $ TList ("t")))
  , (":",    Forall "t" (Mono $ ("t") :=> TList ("t") :=> TList ("t")))
  , ("head", Forall "t" (Mono $ (TList("t")) :=> ("t")))
  , ("tail", Forall "t" (Mono $ (TList("t")) :=> (TList("t"))))
  ]
