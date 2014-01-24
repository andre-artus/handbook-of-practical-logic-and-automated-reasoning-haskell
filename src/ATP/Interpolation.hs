
module ATP.Interpolation
  ( interpolate
  , einterpolate
  ) 
where

#include "undefined.h" 

import ATP.Util.Prelude
import qualified ATP.DefCnf as Cnf
import qualified ATP.EqElim as EqElim
import qualified ATP.Equal as Equal
import qualified ATP.Fol as Fol
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Herbrand as Herbrand
import qualified ATP.Order as Order
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Util.ListSet as Set
import ATP.Util.ListSet((\\), (∪))
import qualified ATP.Util.Lib as Lib
import ATP.Util.Lib((⟾))
import ATP.Util.Log (Log)
import qualified Data.List as List
import qualified Data.Map as Map

-- * Interpolation

pinterpolate :: Formula -> Formula -> Formula
pinterpolate p q = 
  let orify a r = Prop.apply (a ⟾ (⊥)) r ∨ Prop.apply (a ⟾ (⊤)) r in
  Prop.simplify $ foldr orify p (Prop.atoms p \\ Prop.atoms q)

urinterpolate :: Log m => Formula -> Formula -> m (Formula)
urinterpolate p q = 
  let fm = Skolem.specialize $ Skolem.prenex $ p ∧ q
      fvs = Fol.fv fm
      (consts, funcs) = Herbrand.herbfuns fm
      cntms = map (\(c, _) -> Fn c []) consts in
  do tups <- Herbrand.dpRefineLoop (Prop.simpcnf fm) cntms funcs fvs 0 [] [] []
     let fmis = map (\tup -> Fol.apply (Map.fromList (zip fvs tup)) fm) tups
         (ps, qs) = List.unzip (map F.destAnd fmis) 
     return $ pinterpolate (F.listConj(Set.setify ps)) (F.listConj(Set.setify qs))

toptermt :: [(Pred, Int)] -> Term -> [Term]
toptermt _ (Var _) = []
toptermt _ (Num _) = []
toptermt fns (tm @ (Fn f args)) = if elem (f, length args) fns then [tm]
                           else Set.unions (map (toptermt fns) args)

topterms :: [(Pred, Int)] -> Formula -> [Term]
topterms fns = F.atomUnion (\(R _ args) -> Set.unions (map (toptermt fns) args))

uinterpolate :: Log m => Formula -> Formula -> m Formula
uinterpolate p q = 
  let fp = Fol.functions p
      fq = Fol.functions q
      simpinter tms n c = 
        case tms of
          [] -> c
          (tm @ (Fn f args) : otms) -> 
            let v = "v_" ++ show n
                c' = EqElim.replace (tm ⟾ Var v) c
                c'' = if elem (f, length args) fp 
                      then (∃) v c' else (¥) v c' in
            simpinter otms (n+1::Int) c'' 
          _ -> __IMPOSSIBLE__ in
  do c <- urinterpolate p q 
     let tts = topterms ((fp \\ fq) ∪ (fq \\ fp)) c
         tms = List.sortBy (Lib.decreasing Order.termSize) tts 
     return $ simpinter tms 1 c

cinterpolate :: Log m => Formula -> Formula -> m Formula
cinterpolate p q = 
  let fm = Skolem.nnf (p ∧ q)
      efm = F.listEx (Fol.fv fm) fm
      fns = map fst (Fol.functions fm)
      (p', q') = F.destAnd $ fst $ Skolem.skolem efm fns 
  in uinterpolate p' q'

interpolate :: Log m => Formula -> Formula -> m Formula
interpolate p q =
  let vs = map Var (Set.intersect (Fol.fv p) (Fol.fv q))
      fns = Fol.functions (p ∧ q)
      n = foldr (Cnf.maxVarIndex "c_" . fst) 0 fns + 1
      cs = map (\i -> Fn ("c_" ++ show i) []) [n .. n + length vs - 1]
      fn_vc = Map.fromList (zip vs cs)
      fn_cv = Map.fromList (zip cs vs)
      p' = EqElim.replace fn_vc p 
      q' = EqElim.replace fn_vc q in
  do fm <- cinterpolate p' q'
     return $ EqElim.replace fn_cv fm

einterpolate :: Log m => Formula -> Formula -> m Formula
einterpolate p q =
  let p' = Equal.equalitize p
      q' = Equal.equalitize q
      p'' = if p == p' then p else fst (F.destImp p') ∧ p
      q'' = if q == q' then q else fst (F.destImp q') ∧ q in
  interpolate p'' q''
