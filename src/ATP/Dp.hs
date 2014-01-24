
-- The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.

module ATP.Dp
  ( dp
  , dptaut
  , dpll
  , dplltaut
  ) 
where

#include "undefined.h" 

import ATP.Util.Prelude 
import qualified ATP.DefCnf as Cnf
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Prop as Prop
import qualified ATP.Util.List as List
import qualified ATP.Util.ListSet as Set
import ATP.Util.ListSet((\\), (∪))

-- * Davis-Putnam

oneLiteralRule :: Clauses -> Maybe Clauses
oneLiteralRule clauses = 
  case List.find (\cl -> length cl == 1) clauses of
    Nothing -> Nothing
    Just [u] -> Just (Set.image (\\ [u']) clauses1) 
      where u' = F.opp u
            clauses1 = filter (not . elem u) clauses 
    _ -> __IMPOSSIBLE__ 

affirmativeNegativeRule :: Clauses -> Maybe Clauses
affirmativeNegativeRule clauses = 
  let (neg', pos) = List.partition F.negative (Set.unions clauses)
      neg = map F.opp neg'
      posOnly = pos \\ neg
      negOnly = neg \\ pos
      pure = posOnly ∪ map F.opp negOnly in
  case pure of
    [] -> Nothing
    _ -> Just (filter (\cl -> null $ Set.intersect cl pure) clauses)

findBlowup :: Clauses -> Formula -> (Int, Formula)
findBlowup cls l = 
  let m = length(filter (elem l) cls)
      n = length(filter (elem (F.opp l)) cls) in
  (m * n - m - n, l)

resolutionRule :: Clauses -> Clauses
resolutionRule clauses = 
  let pvs = filter F.positive (Set.unions clauses)
      lblows = map (findBlowup clauses) pvs
      (_, p) = List.minimum lblows in
  resolveOn p clauses

resolveOn :: Formula -> Clauses -> Clauses
resolveOn p clauses =
  let p' = F.opp p 
      (pos, notpos) = List.partition (elem p) clauses 
      (neg, other) = List.partition (elem p') notpos
      pos' = map (filter (/= p)) pos
      neg' = map (filter (/= p')) neg
      res0 = List.allPairs (∪) pos' neg' in
  other ∪ filter (not . Prop.trivial) res0

-- Davis-Putnam procedure

dp :: Clauses -> Bool
dp [] = True
dp clauses = if elem [] clauses then False else
             case oneLiteralRule clauses of
               Just clauses' -> dp clauses'
               Nothing -> 
                 case affirmativeNegativeRule clauses of
                 Just clauses' -> dp clauses'
                 Nothing -> dp(resolutionRule clauses)

dpsat :: Formula -> Bool
dpsat = dp . Cnf.defcnfs

dptaut :: Formula -> Bool
dptaut = not . dpsat . Not

findCount :: Clauses -> Formula -> (Int, Formula)
findCount cls l =
  let m = length(filter (elem l) cls)
      n = length(filter (elem (F.opp l)) cls) in
  (m + n, l)

dpll :: Clauses -> Bool
dpll [] = True
dpll clauses = 
  if elem [] clauses then False else
  case oneLiteralRule clauses of
    Just clauses' -> dpll clauses'
    Nothing -> 
      case affirmativeNegativeRule clauses of
      Just clauses' -> dpll clauses'
      Nothing -> 
        let pvs = filter F.positive (Set.unions clauses) 
            lcounts = map (findCount clauses) pvs 
            (_, p) = List.maximum lcounts in
        dpll (Set.insert [p] clauses) 
        || dpll (Set.insert [F.opp p] clauses)

dpllsat :: Formula -> Bool
dpllsat = dpll . Cnf.defcnfs

dplltaut :: Formula -> Bool
dplltaut = not . dpllsat . Not
