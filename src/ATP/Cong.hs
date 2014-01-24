
-- Congruence closure.

module ATP.Cong
  ( ccsatisfiable
  , ccvalid
  )
where

import ATP.Util.Prelude 
import qualified ATP.Equal as Equal
import qualified ATP.Fol as Fol
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Util.List as List
import qualified ATP.Util.ListSet as Set
import ATP.Util.ListSet ((∪))
import qualified ATP.Util.UnionFind as UF
import ATP.Util.UnionFind(Partition)
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Maybe as Maybe

subterms :: Term -> [Term]
subterms tm = case tm of
  (Fn _f args) -> foldr (Set.union . subterms) [tm] args
  _ -> [tm]

congruent :: Partition Term -> (Term, Term) -> Bool
congruent eqv (s,t) = case (s,t) of
  (Fn f fargs, Fn g gargs) -> f == g && List.all2 (UF.equivalent eqv) fargs gargs
  _ -> False

emerge :: (Term, Term) -> (Partition Term, Map Term [Term]) 
          -> (Partition Term, Map Term [Term]) 
emerge (s,t) (eqv, pfn) =
  let s' = UF.canonize eqv s 
      t' = UF.canonize eqv t in
  if s' == t' then (eqv,pfn) else
  let sp = Maybe.fromMaybe [] (Map.lookup s' pfn)
      tp = Maybe.fromMaybe [] (Map.lookup t' pfn) 
      eqv' = UF.equate (s,t) eqv 
      st' = UF.canonize eqv' s' 
      pfn' = Map.insert st' (sp ∪ tp) pfn 
  in foldr (\(u,v) (eq, pf) ->
               if congruent eq (u,v) then emerge (u,v) (eq, pf)
               else (eq, pf))
        (eqv', pfn') (List.allPairs (,) sp tp)

predecessors :: Term -> Map Term [Term] -> Map Term [Term] 
predecessors t pfn = case t of
  Fn _f a -> foldr (\s m -> let tms = Maybe.fromMaybe [] (Map.lookup s m) in
                           Map.insert s (Set.insert t tms) m)
                   pfn (Set.setify a)
  _ -> pfn

ccsatisfiable :: [Formula] -> Bool
ccsatisfiable fms = 
  let (pos, neg) = List.partition F.positive fms 
      eqps = map Equal.destEq pos
      eqns = map (Equal.destEq . F.opp) neg
      lrs = map fst eqps ++ map snd eqps ++ map fst eqns ++ map snd eqns
      pfn = foldr predecessors Map.empty (Set.unions $ map subterms lrs)
      (eqv, _) = foldr emerge (UF.unequal, pfn) eqps in
  all (\(l, r) -> not $ UF.equivalent eqv l r) eqns

ccvalid :: Formula -> Bool
ccvalid fm = 
  let fms = Prop.simpdnf $ Skolem.askolemize $ Not $ Fol.generalize fm in
  not $ any ccsatisfiable fms

