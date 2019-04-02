module DiffBoundMatrix where

import Data.List
import Data.List.Split (splitOn)
import Data.Maybe (isJust)
import Data.Matrix

data DBM = DBM {
  variables :: [Variable],
  dbmMatrix :: Matrix IntPlusInf
  } deriving (Eq, Show)

data PotentialConstraint = PotentialConstraint {
  v_i :: Variable,
  v_j :: Variable,
  constraint :: Integer
  } deriving (Eq, Show)

{- Based of the DBM definition of:
     c      if (v_j - v_i <= c) in C
     +\inf  elsewhere. 
-}
getDbmEntry :: [PotentialConstraint] -> Variable -> Variable -> IntPlusInf
getDbmEntry cs v1 v2  =
  let maybeConstraint = lookupConstraint (v1, v2) cs
  in
    if (isJust maybeConstraint)
      then
        let (Just constraint) = maybeConstraint
        in Number constraint
      else Infinity

lookupConstraint :: (Variable, Variable) -> [PotentialConstraint] -> Maybe Integer
lookupConstraint (v1, v2) cs =
  let maybeC = find (\(PotentialConstraint i j c)->((v1==i)&&(v2==j))) cs
  in
    if (isJust maybeC)
      then
        let (Just (PotentialConstraint i j c)) = maybeC
        in (Just c)
      else Nothing

data Sign = Pos | Neg deriving (Eq)
instance Show Sign where
  show Pos = "+"
  show Neg = "-"

data Variable = Var String Sign | Zero deriving (Eq)
instance Show Variable where
  show Zero = "v0"
  show (Var name sign) = (show sign)++name

data IntPlusInf = Number Integer | Infinity deriving (Eq)
instance Show IntPlusInf where
  show (Number i) = (show i)
  show Infinity = "+∞"
instance Ord IntPlusInf where
  Infinity `compare` Infinity = EQ
  (Number _) `compare` Infinity = LT
  Infinity `compare` (Number _) = GT
  (Number a) `compare` (Number b) = a `compare` b

{- A Constraint given by DIG is always of the form of either
    "x + y < bound" or "x < bound" -}
data DigConstraint = DigConstraint {
  leftVar :: Variable,
  maybeRightVar :: Maybe Variable,
  bound :: Integer
  } deriving (Eq, Show)

{- We subtract one from the bound to turn the '<' relation to '<='
   And we follow the translation of Fig. 5 from translating
   between constraints over V+ and their coherent form in V.-}
toPotentialForm :: DigConstraint -> [PotentialConstraint]
toPotentialForm (DigConstraint lVar Nothing b) = [makeCoherentPotentialConstraint lVar b]
toPotentialForm (DigConstraint lVar (Just rVar) b) = makeTwoCoherentPotentialConstraints lVar rVar (b-1)

makeCoherentPotentialConstraint :: Variable -> Integer -> PotentialConstraint
{-  v_i < c <=> v_i <= (c-1) maps to
    v_i+ - v_i- <= 2*(c-1)
-}
makeCoherentPotentialConstraint (Var v Pos) c = PotentialConstraint (Var v Pos) (Var v Neg) (2*(c-1))
{-  -v_i < c <=> v_i >=c  maps to
    v_i- - v_i+ <= -2c -}
makeCoherentPotentialConstraint (Var v Neg) c = PotentialConstraint (Var v Neg) (Var v Pos) ((-2)*c)

makeTwoCoherentPotentialConstraints :: Variable -> Variable -> Integer -> [PotentialConstraint]
makeTwoCoherentPotentialConstraints (Var vi Pos) (Var vj Neg) c =
  [ PotentialConstraint (Var vi Pos) (Var vj Pos) c,
    PotentialConstraint (Var vj Neg) (Var vi Neg) c ]
makeTwoCoherentPotentialConstraints (Var vi Pos) (Var vj Pos) c =
  [ PotentialConstraint (Var vi Pos) (Var vj Neg) c,
    PotentialConstraint (Var vj Pos) (Var vi Neg) c ]
makeTwoCoherentPotentialConstraints (Var vi Neg) (Var vj Neg) c =
  [ PotentialConstraint (Var vj Neg) (Var vi Pos) c,
    PotentialConstraint (Var vi Neg) (Var vj Pos) c ]
makeTwoCoherentPotentialConstraints vi@(Var _ Neg) vj@(Var _ Pos) c = makeTwoCoherentPotentialConstraints vj vi c

makeDigConstraint :: String -> DigConstraint
makeDigConstraint s =
  {- split on ' ' -}
  let tokens = splitOn " " s
  in
    if (length tokens) == 5
      then DigConstraint (makeVar (tokens !! 0)) (Just (makeVar (tokens !! 2))) (read (tokens !! 4)::Integer)
      else DigConstraint (makeVar (tokens !! 0)) Nothing (read (tokens !! 2)::Integer)

makeVar :: String -> Variable
makeVar s =
  if "-" `isPrefixOf` s
    then Var (tail s) Neg
    else Var (s) Pos

octagonEqs1 :: [String]
octagonEqs1 = ["-y + x < 5",
               "-y + -x < -6",
               "y + x < 13",
               "-y < -2",
               "y < 7",
               "y + -x < 4",
               "-x < -2",
               "x < 8"]

octagonEqs2 :: [String]
octagonEqs2 = ["-y + x < 5",
               "-y + -x < -6",
               "y + x < 13",
               "-y < -2",
               "y < 8", {- this side should be widened -}
               "y + -x < 4",
               "-x < -2",
               "x < 8"]

{-
  Miné 2009: We consider that each variable v_i in V+
  comes in two flavors: a positive form v_i+ and a
  negative form v_i-. We introduce the set
    V = { v_0+, v_0-,...,v_{N-1}+, v_{N-1}- }
-}
variableDomain :: [Variable]
variableDomain = [(makeVar "x"), (makeVar "-x"),
                  (makeVar "y"), (makeVar "-y")]
                  
display :: DBM -> IO ()
display dbm@(DBM vars mat) = do
  putStrLn (prettyMatrix mat)
  putStrLn ""

{- Widening is just a transformation on DBM -}

widen :: DBM -> DBM -> DBM
widen dbm1@(DBM v1 m1) dbm2@(DBM _ m2) =
  let size = length v1
      dbmW = matrix size size $ \(i,j) -> (getElem i j m1) `widenElem` (getElem i j m2)
  in (DBM v1 dbmW)

widenElem :: IntPlusInf -> IntPlusInf -> IntPlusInf
widenElem m_ij n_ij =
  if n_ij <= m_ij
    then m_ij
    else Infinity

makeDbm :: [Variable] -> [PotentialConstraint] -> DBM
makeDbm vars ps = 
  let arrayMatrix = map (\v1-> (map (\v2-> getDbmEntry ps v1 v2) vars)) vars
      mat = fromLists arrayMatrix
  in (DBM vars mat)
      
main :: IO ()
main = do
      {- DBM 1 -}
  let cs1 = map makeDigConstraint octagonEqs1
      potentials1 = concat $ map toPotentialForm cs1
      dbm1 = makeDbm variableDomain potentials1
      {- DBM 2 -}
      cs2 = map makeDigConstraint octagonEqs2
      potentials2 = concat $ map toPotentialForm cs2
      dbm2 = makeDbm variableDomain potentials2
  {- Show the DBMs -}
  putStrLn "Octagon constraints for iter 1"
  putStrLn (show octagonEqs1)
  putStrLn ""
  putStrLn "DBM m+"
  display dbm1
  
  putStrLn "Octagon constraints for iter 2"
  putStrLn (show octagonEqs2)
  putStrLn ""
  putStrLn "DBM n+"
  display dbm2
  {- Now apply widening -}
  let dbmW = widen dbm1 dbm2
  putStrLn "m+ ∇ n+"
  display dbmW
  return ()
