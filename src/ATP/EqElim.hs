
-- * Equality elimination

module ATP.EqElim 
  ( replace
  , modifyS
  , modifyT
  , modifyE
  , brand
  , bmeson
  ) 
where

#include "undefined.h" 

import ATP.Util.Prelude 
import qualified ATP.Equal as Equal
import qualified ATP.Fol as Fol
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Meson as Meson
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Tableaux as Tableaux
import qualified ATP.Util.List as List
import qualified ATP.Util.ListSet as Set
import ATP.Util.ListSet((\\))
import ATP.Util.Log (Log)
import qualified ATP.Util.Monad as M
import qualified Data.Map as Map
import Data.Map(Map)

modifyS :: Clause -> Clauses
modifyS cl = case List.find Equal.isEq cl of
               Nothing -> [cl]
               Just eq1 -> 
                 let (s, t) = Equal.destEq eq1 
                     eq2 = Equal.mkEq t s
                     sub = modifyS (cl \\ [eq1]) in
                 map (Set.insert eq1) sub ++ map (Set.insert eq2) sub

modifyT :: Clause -> Clause
modifyT [] = []
modifyT (p:ps) = if Equal.isEq p then
                   let (s, t) = Equal.destEq p 
                       ps' = modifyT ps
                       w = Var (Fol.variant "w" (Fol.fv (p:ps'))) in
                   Not(Equal.mkEq t w) : Equal.mkEq s w : ps'
                 else p : modifyT ps

findNestNonvar :: Term -> Maybe Term
findNestNonvar (Var _) = Nothing 
findNestNonvar (Num _) = Nothing 
findNestNonvar (Fn _ args) = List.find (not . Fol.isVar) args

findNvSubterm :: Formula -> Maybe Term
findNvSubterm (Not p) = findNvSubterm p
findNvSubterm (Atom (R "=" st)) = List.findFirst findNestNonvar st
findNvSubterm (Atom (R _ args)) = List.find (not . Fol.isVar) args
findNvSubterm _ = __IMPOSSIBLE__ 

replacet :: Map Term Term -> Term -> Term
replacet rfn tm = case Map.lookup tm rfn of
  Just tm' -> tm'
  Nothing -> case tm of
    Var _ -> tm
    Num _ -> tm
    Fn f args -> Fn f (map (replacet rfn) args)

replace :: Map Term Term -> Formula -> Formula
replace = Fol.onformula . replacet

emodify :: Vars -> Clause -> Clause
emodify fvs cls = 
  case List.findFirst findNvSubterm cls of
    Nothing -> cls
    Just t -> let w = Fol.variant "w" fvs 
                  cls' = map (replace (Map.singleton t (Var w))) cls in
              emodify (w : fvs) (Not(Equal.mkEq t (Var w)) : cls')

modifyE :: Clause -> Clause
modifyE cls = emodify (Fol.fv cls) cls

brand :: Clauses -> Clauses
brand cls = 
  let cls1 = map modifyE cls
      cls2 = Set.unions (map modifyS cls1) in
  [Equal.mkEq (Var "x") (Var "x")] : map modifyT cls2

bpuremeson :: Log m => Formula -> m Int
bpuremeson fm = 
  let cls = brand(Prop.simpcnf (Skolem.specialize (Skolem.pnf fm)))
      rules = List.concat (map Meson.contrapositives cls) in
  Tableaux.deepen (\n -> do M.ignore $ Meson.mexpand rules [] Bot Just (Map.empty, n, 0)
                            return n) 0

bmeson :: Log m => Formula -> m [Int]
bmeson fm = 
  let fm1 = Skolem.askolemize (Not (Fol.generalize fm)) in
  mapM (bpuremeson . F.listConj) (Prop.simpdnf fm1)
