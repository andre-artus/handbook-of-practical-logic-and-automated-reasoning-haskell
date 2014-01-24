
module ATP.Tableaux
  ( unifyLiterals
  , deepen
  , prawitz
  , tab
  , splittab
  )
where

import ATP.Util.Prelude 
import qualified ATP.Fol as Fol
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Unif as Unif
import ATP.Util.Lib((⟾))
import qualified ATP.Util.List as List
import qualified ATP.Util.ListSet as Set
import qualified ATP.Util.Log as Log
import ATP.Util.Log(Log)
import qualified ATP.Util.Monad as M
import qualified Data.Map as Map

-- * Tableaux

unifyLiterals :: Env -> (Formula, Formula) -> Maybe Env
unifyLiterals env pq = case pq of
  (Atom(R p1 a1), Atom(R p2 a2)) -> Unif.unify env [(Fn p1 a1, Fn p2 a2)]
  (Not p, Not q) -> unifyLiterals env (p, q)
  (Bot, Bot) -> Just env
  _ -> Nothing 

unifyComplements :: Env -> (Formula, Formula) -> Maybe Env
unifyComplements env (p, q) = unifyLiterals env (p, F.opp q)

unifyRefute :: [[Formula]] -> Env -> Maybe Env
unifyRefute [] env = Just env
unifyRefute (d:odjs) env = 
  let (pos, neg) = List.partition F.positive d 
      pairs = List.allPairs (,) pos neg 
      findFn pq = do env' <- unifyComplements env pq 
                     unifyRefute odjs env'
  in List.findFirst findFn pairs

prawitzLoop :: [[Formula]] -> Vars -> [[Formula]] 
            -> Int -> Maybe (Env, Int)
prawitzLoop djs0 fvs djs n = 
  let l = length fvs
      newvars = map (\k -> Var ("_" ++ show (n * l + k))) [1 .. l]
      inst = Map.fromList (zip fvs newvars)
      djs1 = Prop.distrib (Set.image (Set.image (Fol.apply inst)) djs0) djs in
  case unifyRefute djs1 Map.empty of
    Just env -> Just (env, n+1)
    Nothing -> prawitzLoop djs0 fvs djs1 (n+1)

prawitz :: Formula -> Maybe Int
prawitz fm = 
  let fm0 = Skolem.skolemize $ Not $ Fol.generalize fm in
  case prawitzLoop (Prop.simpdnf fm0) (Fol.fv fm0) [[]] 0 of
    Nothing -> Nothing
    Just (_, n) -> Just n

tableau :: ([Formula], [Formula], Int) 
        -> ((Env, Int) -> Maybe a) -> (Env, Int) -> Maybe a
tableau (fms, lits, n) cont (env, k) = 
  if n < 0 then Nothing else
  case fms of 
    [] -> Nothing
    And p q : unexp -> tableau (p:q:unexp, lits, n) cont (env, k)
    Or p q : unexp -> tableau (p:unexp, lits, n) (tableau (q:unexp, lits, n) cont) (env, k)
    fm @ (All x p) : unexp -> 
           let y = Var("_" ++ show k) 
               p' = Fol.apply (x ⟾ y)  p in
                    tableau (p':unexp ++ [fm], lits, n-1) cont (env, k+1)
    fm:unexp -> 
      let findFn l = do env' <- unifyComplements env (fm,l) 
                        cont(env', k) in
      case List.findFirst findFn lits of
        Just x -> Just x
        Nothing -> tableau (unexp, fm:lits, n) cont (env,k)

deepen :: Log m => (Int -> Maybe a) -> Int -> m a
deepen f n = do 
  Log.infoM "deepen" $ "Searching with depth limit " ++ show n
  case f n of
    Just x -> return x
    Nothing -> deepen f (n+1)

tabrefute :: Log m => [Formula] -> m Int
tabrefute fms =
  let tabFn n = do M.ignore $ tableau (fms, [], n) Just (Map.empty, 0) 
                   return n in
  deepen tabFn 0

tab :: Log m => Formula -> m Int
tab fm = 
  let sfm = Skolem.askolemize $ Not $ Fol.generalize fm in
  if sfm == Bot then return 0 else tabrefute [sfm]

splittab :: Log m => Formula -> m [Int]
splittab = mapM tabrefute . Prop.simpdnf . Skolem.askolemize . Not . Fol.generalize
