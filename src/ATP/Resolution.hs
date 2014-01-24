
module ATP.Resolution 
  ( rename
  , termMatch
  , resolveClauses
  , incorporate
  , basicResolution
  , resolution
  , positiveResolution
  , sosResolution
  ) 
where

import ATP.Util.Prelude 
import qualified ATP.Fol as Fol
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Tableaux as Tableaux
import qualified ATP.Unif as Unif
import ATP.Util.Lib((↦))
import qualified ATP.Util.List as List
import qualified ATP.Util.Log as Log
import ATP.Util.Log(Log)
import qualified ATP.Util.ListSet as Set
import ATP.Util.ListSet ((\\), (∪))
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

mgu :: Clause -> Env -> Maybe Env
mgu (a:b:rest) env = case Tableaux.unifyLiterals env (a,b) of
                       Nothing -> Nothing
                       Just env' -> mgu (b:rest) env'
mgu _ env = Unif.solve env

unifiable :: Formula -> Formula -> Bool
unifiable p q = Maybe.isJust (Tableaux.unifyLiterals Map.empty (p, q))

rename :: String -> Clause -> Clause
rename pfx cls =
  let fvs = Fol.fv(F.listDisj cls)
      vvs = map (Var . (pfx ++)) fvs in
            map (Fol.apply (Map.fromList (zip fvs vvs))) cls

resolvents :: Clause -> Clause -> Formula -> [Clause] -> [Clause]
resolvents cl1 cl2 p acc = 
  case filter (unifiable (F.opp p)) cl2 of
    [] -> acc 
    ps2 -> foldr foldFn acc pairs
      where ps1 = filter (\q -> q /= p && unifiable p q) cl1
            pairs = List.allPairs (,) (map (p:) (Set.allSubsets ps1))
                                               (Set.allNonemptySubsets ps2) 
            foldFn (s1, s2) sof = 
              case mgu (s1 ++ map F.opp s2) Map.empty of
                Just env' -> 
                  let cs = (cl1 \\ s1) ∪ (cl2 \\ s2) in
                  Set.image (Fol.apply env') cs : sof
                Nothing -> sof 

resolveClauses :: Clause -> Clause -> [Clause]
resolveClauses cls1 cls2 = 
  let cls1' = rename "x" cls1 
      cls2' = rename "y" cls2 in
  foldr (resolvents cls1' cls2') [] cls1' 

basicResloop :: Log m => ([Clause], [Clause]) -> m ()
basicResloop (used, unused) = case unused of 
  [] -> Log.infoM "basicResloop" "No proof found"
  cl:ros -> do 
    Log.infoM "basicResloop" $ show (length used) ++ " used; " ++ show (length unused) ++ " unused."
    let used' = Set.insert cl used 
        news = List.concat (map (resolveClauses cl) used') 
    if elem [] news then return () else basicResloop (used', ros++news)

pureBasicResolution :: Log m => Formula -> m ()
pureBasicResolution fm = basicResloop ([], Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm)

basicResolution :: (Monad m, Log m) => Formula -> m ()
basicResolution fm = 
  let fm1 = Skolem.askolemize $ Not $ Fol.generalize fm in
  do mapM_ (pureBasicResolution . F.listConj) (Prop.simpdnf fm1)
     Log.infoM "basicResolution" "Solution found!"

termMatch :: Env -> [(Term, Term)] -> Maybe Env
termMatch env [] = Just env
termMatch env (h:oth) = 
  case h of
    (Fn f fargs, Fn g gargs) | (f == g && length fargs == length gargs) ->
           termMatch env (zip fargs gargs ++ oth)
    (Var x, t) -> case Map.lookup x env of 
                    Nothing -> termMatch ((x ↦ t) env) oth
                    Just t' | t == t' -> termMatch env oth
                    _ -> Nothing
    _ -> Nothing

matchLiterals :: Env -> (Formula, Formula) -> Maybe Env
matchLiterals env pq = case pq of
  (Atom(R p a1), Atom(R q a2)) -> termMatch env [(Fn p a1, Fn q a2)] 
  (Not(Atom(R p a1)), Not(Atom(R q a2))) -> termMatch env [(Fn p a1, Fn q a2)] 
  _ -> Nothing

subsumesClause :: Clause -> Clause -> Bool
subsumesClause cls1 cls2 = Maybe.isJust $ subsume Map.empty cls1
 where 
  subsume env [] = Just env
  subsume env (l1:clt) = List.findFirst
    (\l2 -> case matchLiterals env (l1, l2) of
             Nothing -> Nothing
             Just env' -> subsume env' clt) cls2

replace :: Clause -> Clauses -> Clauses
replace cl [] = [cl]
replace cl (c:cls) = if subsumesClause cl c then cl:cls 
                     else c:replace cl cls

incorporate :: Clause -> Clause -> Clauses -> Clauses
incorporate gcl cl unused = 
  if Prop.trivial cl || any (\c -> subsumesClause c cl) (gcl:unused)
  then unused else replace cl unused

resloop :: Log m => ([Clause], [Clause]) -> m ()
resloop (used, unused) = case unused of 
  [] -> Log.infoM "resloop" "No proof found"
  cl:ros -> do 
    Log.infoM "resloop" $ show (length used) ++ " used; " ++ show (length unused) ++ " unused."
    let used' = Set.insert cl used 
        news = List.concat (map (resolveClauses cl) used') 
    if elem [] news then return () 
     else resloop (used',foldr (incorporate cl) ros news)

pureResolution :: Log m => Formula -> m ()
pureResolution fm = resloop ([], Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm)

resolution :: Log m => Formula -> m ()
resolution fm = 
  let fm1 = Skolem.askolemize $ Not $ Fol.generalize fm in
  do mapM_ (pureResolution . F.listConj) (Prop.simpdnf fm1)
     Log.infoM "resolution" "Solution found!"

presolveClauses :: Clause -> Clause -> [Clause]
presolveClauses cls1 cls2 = 
  if all F.positive cls1 || all F.positive cls2 
  then resolveClauses cls1 cls2 else []

positiveResloop :: Log m => ([Clause], [Clause]) -> m ()
positiveResloop (used, unused) = case unused of 
  [] -> Log.infoM "positiveResloop" "No proof found"
  cl:ros -> do 
    Log.infoM "positiveResloop" $ show (length used) ++ " used; " ++ show (length unused) ++ " unused."
    let used' = Set.insert cl used 
        news = List.concat (map (presolveClauses cl) used') 
    if elem [] news then return () 
     else positiveResloop (used',foldr (incorporate cl) ros news)

purePositiveResolution :: Log m => Formula -> m ()
purePositiveResolution fm = 
  positiveResloop ([], Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm)

positiveResolution :: Log m => Formula -> m ()
positiveResolution fm = 
  let fm1 = Skolem.askolemize $ Not $ Fol.generalize fm in
  do mapM_ (purePositiveResolution . F.listConj) (Prop.simpdnf fm1)
     Log.infoM "positiveResolution" "Solution found!"

pureSosResolution :: Log m => Formula -> m ()
pureSosResolution fm =
  resloop (List.partition (any F.positive) 
                       (Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm))

sosResolution :: Log m => Formula -> m ()
sosResolution fm = 
  let fm1 = Skolem.askolemize $ Not $ Fol.generalize fm in
  do mapM_ (pureSosResolution . F.listConj) (Prop.simpdnf fm1)
     Log.infoM "sosResolution" "Solution found!"
