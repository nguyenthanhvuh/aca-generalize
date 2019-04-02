import qualified Data.Map as M
import Data.List (sort, nub)
import Data.Maybe (catMaybes)
import Data.SBV
import Data.SBV.Internals hiding (LessEq)
import Data.SBV.Control

{- A port of Vu's 'generalize' Python script -}

main :: IO ()
main = do
  let x = Variable "x"
      y = Variable "y"
      f1 = GreatEq x (Constant (-13))
      f2 = LessEq x (Constant 100)
      f3 = LessEq (Addition x y) (Constant 72)
      f = (Conjunction (Expression f1)
            (Conjunction (Expression f2) (Expression f3)))
  ps <- generalize f 100 (-100)
  putStrLn "Upper bounds:"
  mapM_ (\p-> (putStrLn . show) p) ps
  return ()

generalize :: Pred -> Int -> Int -> IO [Pred]
generalize p up low = do
  let ss = nub $ variables p
  putStrLn "Generalizing the formula:"
  putStrLn (show p)
  let os = getOctForms ss
  let ubs = map (mkUbExpr up) os
  rs <- mapM (\ub -> check p (Expression ub)) ubs
  let rs' = zip os rs
  let rs'' = filter (\(_,r) -> (not . disproved) r) rs'
  ubVs <- mapM ((_f p low up) . fst) rs''
  let ubVs' = zip (map fst rs'') ubVs 
  let ubVs'' = catMaybes $ map dropTuplesWithoutBound ubVs'
  let ps = map (\(o,i)-> Expression $ mkUbExpr i o) ubVs''
  return ps

dropTuplesWithoutBound :: (OctForm, Maybe Int) -> Maybe (OctForm, Int)
dropTuplesWithoutBound (_, Nothing) = Nothing
dropTuplesWithoutBound (o, Just v) = Just (o,v)

data SolverResult = SolverProved | SolverDisproved | SolverUnknown deriving (Show, Eq)

_f :: Pred -> Int -> Int -> OctForm -> IO (Maybe Int)
_f p minV maxV o = do
  let statsd = M.singleton maxV SolverProved
  (maybeBoundV, statsd') <- gc p o minV maxV statsd
  case maybeBoundV of
    Just boundV -> do
      case M.lookup boundV statsd' of
        Nothing -> do
          return (Just boundV)
        Just entry ->
          if entry /= SolverDisproved
            then do
              return (Just boundV)
            else return Nothing
    Nothing -> return Nothing

gc :: Pred -> OctForm -> Int -> Int -> M.Map Int SolverResult -> IO (Maybe Int, M.Map Int SolverResult)
gc p o minV maxV statsd = do
  if minV == maxV
    then return (Just minV, statsd)
    else do
      if ((maxV - minV) == 1)
        then do
          let v = M.lookup minV statsd
          if (existsAndIsDisproved v)
            then return (Just maxV, statsd)
            else do
              {- lines 49--60 of generalize.py -}
              let inv = mkUbExpr minV o
              stat <- check p (Expression inv)
              let statRes = extractSolverRes stat
              let statsd' = M.insert minV statRes statsd
    
              if statRes == SolverDisproved
                then return (Just maxV, statsd')
                else return (Just minV, statsd')
        else do
          {- lines 62--76 of generalize.py -}
          let v = ceiling ((fromIntegral (maxV + minV)) / 2.0)
          let inv = mkUbExpr v o
          stat <- check p (Expression inv)
          let statRes = extractSolverRes stat
          let statsd' = M.insert minV statRes statsd
          if statRes == SolverDisproved
            then do
              let tcs = meval o stat
              gc p o tcs maxV statsd'
            else do
              let maxV' = v
              gc p o minV maxV' statsd'

{- This is only called if there are counter examples -}
meval :: OctForm -> ThmResult -> Int
meval o (ThmResult (Satisfiable _ (SMTModel _ vals))) =
  let m = M.fromList vals
  in produceMeval o m
meval _ _ = error "Expecting a model to be given."

produceMeval :: OctForm -> CExMap -> Int
produceMeval (OctOneVar (i, v)) m = 
  let (Just val) = M.lookup v m
  in (fromIntegral ((toInteger i)*(fromCW val)::Integer))
produceMeval (OctTwoVar (i1, v1) (i2, v2)) m =
  let (Just val1) = M.lookup v1 m
      (Just val2) = M.lookup v2 m
  in (fromIntegral (((toInteger i1)*(fromCW val1)) + ((toInteger i2)*(fromCW val2))))

type CExMap = M.Map Var CW

extractSolverRes :: ThmResult -> SolverResult
extractSolverRes (ThmResult (Unsatisfiable _)) = SolverProved
extractSolverRes (ThmResult (Satisfiable _ _)) = SolverDisproved
extractSolverRes _ = SolverUnknown
  
existsAndIsDisproved :: Maybe SolverResult -> Bool
existsAndIsDisproved Nothing = False
existsAndIsDisproved (Just SolverDisproved) = True
existsAndIsDisproved _ = False

interpret :: Pred -> Env -> Predicate
interpret (Negation p) env = do
  p' <- interpret p env
  return $ bnot p'
interpret (Conjunction c1 c2) env = do
  c1' <- interpret c1 env
  c2' <- interpret c2 env
  return $ c1' &&& c2'
interpret (Disjunction d1 d2) env = do
  d1' <- interpret d1 env
  d2' <- interpret d2 env
  return $ d1' ||| d2'
interpret (Expression expr) env = do
  case expr of
    LessEq l r -> do
      return $ (interpExpr l env) .<= (interpExpr r env)
    GreatEq l r -> do
      return $ (interpExpr l env) .>= (interpExpr r env)

getOctForms :: [Var] -> [OctForm]
getOctForms vs =
  let oneVars = concat $ map (\v->map (\i->OctOneVar (i,v)) [1,-1]) vs
      twoVarPairs = [[(i1,v1), (i2,v2)] | i1<-[-1,1], i2<-[-1,1], v1<-vs, v2<-vs, v1 /= v2]
      twoVarPairs' = nub $ map sort twoVarPairs
      twoVars = map (\[vt1, vt2]->OctTwoVar vt1 vt2) twoVarPairs'
  in oneVars++twoVars

disproved :: ThmResult -> Bool
disproved (ThmResult (Satisfiable _ _)) = True
disproved _ = False

check :: Pred -> Pred -> IO ThmResult
check f g = prove $ implication f g
  where
    vs :: [String]
    vs = nub $ (variables f)++(variables g)

    implication :: Pred -> Pred -> Predicate
    implication p1 p2 = do
      syms <- mapM forall vs
      let env = M.fromList (zip vs syms)
      antecedent <- interpret p1 env
      consequent <- interpret p2 env
      return $ antecedent ==> consequent

interpExpr :: Expr -> Env -> SInteger
interpExpr (Variable v) e = envLookup v e
interpExpr (Constant c) _ = (literal (fromIntegral c))::SInteger
interpExpr (Addition o1 o2) e = (interpExpr o1 e)+(interpExpr o2 e)
interpExpr (Mult o1 o2) e = (interpExpr o1 e)*(interpExpr o2 e)

data Expr = Variable Var
          | Constant Int
          | Addition Expr Expr
          | Mult     Expr Expr
          | LessEq   Expr Expr
          | GreatEq  Expr Expr
          deriving (Eq)

variables :: Pred -> [Var]
variables (Expression e) = exprVars e
variables (Negation p) = variables p
variables (Conjunction c1 c2) = (variables c1)++(variables c2)
variables (Disjunction d1 d2) = (variables d1)++(variables d2)

exprVars :: Expr -> [Var]
exprVars (Variable v) = [v]
exprVars (Constant _) = []
exprVars (Addition e1 e2) = (exprVars e1)++(exprVars e2)
exprVars (Mult e1 e2) = (exprVars e1)++(exprVars e2)
exprVars (LessEq e1 e2) = (exprVars e1)++(exprVars e2)
exprVars (GreatEq e1 e2) = (exprVars e1)++(exprVars e2)

{- Modified from Tom DuBuisson's answer on SO -}
type Env = M.Map String SInteger

envLookup :: Var -> Env -> SInteger
envLookup v e = maybe (error $ "Var not found: " ++ show v) id
                            (M.lookup v e)    

mkUbExpr :: Int -> OctForm -> Expr
mkUbExpr up (OctOneVar t) = LessEq (mkExpr t) (Constant up)
mkUbExpr up (OctTwoVar t1 t2) = LessEq (Addition (mkExpr t1) (mkExpr t2)) (Constant up)

mkExpr :: OctTuple -> Expr
mkExpr (-1,v) = (Mult (Constant (-1)) (Variable v))
mkExpr (1,v) = Variable v
  
type OctTuple = (Int, Var)

data OctForm = OctOneVar OctTuple
             | OctTwoVar OctTuple OctTuple
             deriving (Show, Eq)
  
data Pred = Expression  Expr
          | Negation    Pred
          | Conjunction Pred Pred
          | Disjunction Pred Pred
          deriving (Eq)
instance Show Pred where
  show (Expression e) = show e
  show (Negation p) = "¬("++(show p)++")"
  show (Conjunction c1 c2) = "("++(show c1)++") ^ ("++(show c2)++")"
  show (Disjunction d1 d2) = "("++(show d1)++") v ("++(show d2)++")"

type Var = String

instance Show Expr where
  show (Variable n) = n
  show (Constant c) = show c
  show (Addition e1 e2) = (show e1)++" + "++(show e2)
  show (Mult e1 e2) = (show e1)++"*"++(show e2)
  show (LessEq lhs rhs) = (show lhs)++" <= "++(show rhs)
  show (GreatEq lhs rhs) = (show lhs)++" >= "++(show rhs)
