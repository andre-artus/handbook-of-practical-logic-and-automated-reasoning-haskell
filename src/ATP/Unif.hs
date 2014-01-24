
module ATP.Unif
  ( unify
  , solve
  , fullunify
  , unifyAndApply
  )
where

import Prelude 
import qualified ATP.Fol as Fol
import ATP.FormulaSyn
import ATP.Util.Lib((↦))
import qualified Data.Map as Map

istriv :: Env -> Var -> Term -> Maybe Bool
istriv env x t = case t of 
  Var y -> if x == y then Just True else
    case Map.lookup y env of
      Nothing -> Just False
      Just t' -> istriv env x t'
  Num _ -> Just False
  Fn _ args ->  
    if any triv args then Nothing else Just False
 where triv t' = case istriv env x t' of -- occurs check
                  Just False -> False
                  _ -> True

unify :: Env -> [(Term, Term)] -> Maybe Env
unify env eqs = case eqs of 
  [] -> Just env 
  (Num n, Num m) : rest 
   | n == m -> unify env rest
  (Fn f fargs, Fn g gargs):rest -> 
    if f == g && length fargs == length gargs then 
       unify env (zip fargs gargs ++ rest)
    else Nothing
  (Var x, t) : rest -> unifyVar x t rest
  (t, Var x) : rest -> unifyVar x t rest
  _ -> Nothing
  where unifyVar x t rest = 
          case Map.lookup x env of
            Just t' -> unify env ((t', t) : rest)
            Nothing -> case istriv env x t of
                         Just True -> unify env rest
                         Just False -> unify ((x ↦ t) env) rest
                         Nothing -> Nothing

solve :: Env -> Maybe Env
solve env = solve' env (Map.toList env)

solve' :: Env -> [(Var, Term)] -> Maybe Env
solve' env fs = 
  if any (\(x,t) -> elem x (Fol.fv t)) fs
  then Nothing else 
  let env' = foldr (\(x,t) -> Map.insert x (Fol.apply env t)) Map.empty fs
      fs' = Map.toList env' in
  if fs == fs' then Just env else solve' env' fs'

fullunify :: [(Term, Term)] -> Maybe Env
fullunify eqs = do env <- unify Map.empty eqs 
                   solve env

unifyAndApply :: [(Term, Term)] -> Maybe [(Term, Term)] 
unifyAndApply eqs = 
  do env <- fullunify eqs 
     let apply (t1, t2) = (Fol.apply env t1, Fol.apply env t2) in
       return $ map apply eqs
       
