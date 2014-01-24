
-- Relation between first-order and propositonal logic; Herbrand theorem. 

module ATP.Herbrand
  ( herbfuns
  , groundtuples
  , gilmore
  , dpRefineLoop
  , davisputnam
  , davisputnam'
  ) 
where

import Prelude 
import qualified ATP.Dp as Dp
import qualified ATP.Fol as Fol
import ATP.FormulaSyn
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Util.Log as Log
import ATP.Util.Log (Log)
import qualified ATP.Util.List as List
import qualified ATP.Util.ListSet as Set
import qualified Data.Map as Map

-- * Herbrand

-- Function symbols with arity.

type FuncA = (Func, Int)

herbfuns :: Formula -> ([FuncA], [FuncA])
herbfuns fm = 
    let syms @ (cns, fns) = List.partition ((== 0) . snd) (Fol.functions fm) in
    if null cns then ([("c", 0)], fns) else syms

groundterms :: [Term] -> [FuncA] -> Int -> [Term]
groundterms cntms _ 0 = cntms
groundterms cntms funcs n = 
  let grtps (f, arity) =  map (Fn f) (groundtuples cntms funcs (n-1) arity) in
  concat (map grtps funcs)

groundtuples :: [Term] -> [FuncA] -> Int -> Int -> [[Term]]
groundtuples _ _ 0 0 = [[]]
groundtuples _ _ _ 0 = []
groundtuples cntms funcs n m = 
  let tups k = List.allPairs (:) 
               (groundterms cntms funcs k)
               (groundtuples cntms funcs (n-k) (m-1)) in
  concat (map tups [0 .. n])

herbloop :: Log m => (a -> (Formula -> Formula) -> [b] -> [b])
         -> ([b] -> Bool) 
         -> a -> [Term] -> [FuncA] -> Vars -> Int
         -> [b] -> [[Term]] -> [[Term]] -> m [[Term]]
herbloop mfn tfn fl0 cntms funcs fvs n fl tried tuples = do 
  Log.infoM "herbloop" $ show (length tried) ++ " ground instances tried; " ++ show (length fl) ++ " items in list"
  case tuples of
    [] -> let newtups = groundtuples cntms funcs n (length fvs) in
          herbloop mfn tfn fl0 cntms funcs fvs (n+1) fl tried newtups
    tup:tups -> let fl' = mfn fl0 (Fol.apply $ Map.fromList $ zip fvs tup) fl in
                if not(tfn fl') then return (tup:tried) else
                herbloop mfn tfn fl0 cntms funcs fvs n fl' (tup:tried) tups

gilmoreLoop :: Log m => Clauses -> [Term] -> [FuncA] -> Vars -> Int
            -> Clauses -> [[Term]] -> [[Term]] -> m [[Term]] 
gilmoreLoop =
  let mfn djs0 ifn djs =
          filter (not . Prop.trivial) 
             (Prop.distrib (Set.image (Set.image ifn) djs0) djs) in 
  herbloop mfn (/= [])

gilmore :: Log m => Formula -> m Int
gilmore fm = 
    let sfm = Skolem.skolemize(Not(Fol.generalize fm)) 
        fvs = Fol.fv sfm 
        (consts,funcs) = herbfuns sfm 
        cntms = map (\(c,_) -> Fn c []) consts in
    do tms <- gilmoreLoop (Prop.simpdnf sfm) cntms funcs fvs 0 [[]] [] []
       return (length tms)

dpMfn :: Clauses -> (Formula -> Formula) -> Clauses -> Clauses
dpMfn cjs0 ifn = Set.union (map (map ifn) cjs0)

dpLoop :: Log m => Clauses -> [Term] -> [FuncA] -> Vars 
          -> Int -> Clauses -> [[Term]] -> [[Term]] -> m [[Term]] 
dpLoop = herbloop dpMfn Dp.dpll

davisputnam :: Log m => Formula -> m Int
davisputnam fm =
  let sfm = Skolem.skolemize(Not(Fol.generalize fm)) 
      fvs = Fol.fv sfm 
      (consts, funcs) = herbfuns sfm
      cntms = map (\(c,_) -> Fn c []) consts in -- image
  do tms <- dpLoop (Prop.simpcnf sfm) cntms funcs fvs 0 [] [] []
     return (length tms)

dpRefine :: Clauses -> Vars -> [[Term]] -> [[Term]] -> [[Term]] 
dpRefine cjs0 fvs dunno need =
  case dunno of
    [] -> need
    cl : dknow ->
      let mfn = dpMfn cjs0 . Fol.apply . Map.fromList . zip fvs 
          need' = if Dp.dpll(foldr mfn [] (need ++ dknow)) 
                  then cl:need else need in
      dpRefine cjs0 fvs dknow need'

dpRefineLoop :: Log m => Clauses -> [Term] -> [FuncA] -> Vars 
                -> Int -> Clauses -> [[Term]] -> [[Term]] -> m [[Term]]
dpRefineLoop cjs0 cntms funcs fvs n cjs tried tuples =
  do tups <- dpLoop cjs0 cntms funcs fvs n cjs tried tuples 
     return (dpRefine cjs0 fvs tups [])

davisputnam' :: Log m => Formula -> m Int
davisputnam' fm =
  let sfm = Skolem.skolemize(Not(Fol.generalize fm)) 
      fvs = Fol.fv sfm 
      (consts, funcs) = herbfuns sfm 
      cntms = map (\(c,_) -> Fn c []) consts in
  do tms <- dpRefineLoop (Prop.simpcnf sfm) cntms funcs fvs 0 [] [] []
     return (length tms)

