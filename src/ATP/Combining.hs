
-- The Nelson-Oppen method.

module ATP.Combining
  ( slowNelop
  , slowNelopInt
  , slowNelopDlo
  , nelop
  , nelopInt
  , nelopDlo
  , intLang
  , dloLang
  , addDefault
  )
where
 
#include "undefined.h"

import ATP.Util.Prelude 
import qualified ATP.Cong as Cong
import qualified ATP.Cooper as Cooper
import qualified ATP.DefCnf as Cnf
import qualified ATP.Dlo as Dlo
import qualified ATP.Equal as Equal
import qualified ATP.Fol as Fol
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Util.Debug as Debug
import ATP.Util.Lib((⟾))
import qualified ATP.Util.List as List
import qualified ATP.Util.ListSet as Set
import ATP.Util.ListSet((\\))
import qualified ATP.Util.Print as PP
import ATP.Util.Print(Print)
import qualified Control.Monad.Reader as Reader
import Control.Monad.Reader (Reader)
import qualified Data.Maybe as Maybe

-- * Nelson-Oppen

data Lang = Lang { name :: String
                 , fn :: (Func, Int) -> Bool
                 , rn :: Rational -> Bool
                 , pr :: (Pred, Int) -> Bool
                 , dp :: Formula -> Bool 
                 }

instance Print Lang where
  pPrint = PP.text . name

dloLang :: Lang
dloLang = Lang "dloLang" fdesc ndesc pdesc Dlo.valid
  where fdesc = const False 
        ndesc = const True
        pdesc = flip elem preds
        preds = [ ("≤", 2::Int), ("<", 2), ("≥", 2), (">", 2)]

intqelim :: Formula -> Formula
intqelim = Cooper.integerQelim

intLang :: Lang
intLang = Lang "intLant" fdesc ndesc pdesc elim
  where fdesc = flip elem funcs
        ndesc = const True
        pdesc = flip elem preds
        elim fm = intqelim (Fol.generalize fm) == Top
        funcs = [("-", 1::Int), ("+", 2), ("-", 2), ("*", 2)]
        preds = [("≤", 2::Int), ("<", 2), ("≥", 2), (">", 2)]

addDefault :: [Lang] -> [Lang]
addDefault langs = langs ++ [ Lang "uninterpLang"
                                   (\sn -> not $ List.any (flip fn sn) langs)
                                   (const False)
                                   (\sn -> sn == ("=", 2))
                                   Cong.ccvalid ]

chooseLang :: [Lang] -> Formula -> Maybe Lang
chooseLang langs fm = case fm of
  Atom(R "=" [Num n, _]) -> List.find (flip rn n) langs
  Atom(R "=" [_, Num n]) -> List.find (flip rn n) langs
  Atom(R "=" [Fn f args, _]) -> List.find (flip fn (f, length args)) langs
  Atom(R "=" [_, Fn f args]) -> List.find (flip fn (f, length args)) langs
  Atom(R p args) -> List.find (flip pr (p,length args)) langs
  _ -> Debug.impossible

listify :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c 
listify f l cont = case l of 
  [] -> cont []
  h:t -> f h (\h' -> listify f t (\t' -> cont (h':t')))

homot :: Print a => Lang -> Term -> (Term -> [Formula] -> Reader Int a) -> [Formula] -> Reader Int a
homot lang tm cont defs = case tm of 
  Var _ -> cont tm defs
  Num r -> 
    if rn lang r 
    then {-# SCC "homot1" #-} cont tm defs
    else {-# SCC "homot2" #-} do
      n <- Reader.ask
      Reader.local (+1) $ cont (Var ("v_" ++ show n)) (Var ("v_" ++ show n) ≡ tm : defs)
  Fn f args -> 
    if fn lang (f, length args) 
    then listify (homot lang) args (\a -> cont (Fn f a)) defs
    else do
      n <- Reader.ask
      Reader.local (+1) $ cont (Var ("v_" ++ show n)) (Var ("v_" ++ show n) ≡ tm : defs)

homol :: Print a => [Lang] -> Formula -> (Formula -> [Formula] -> Reader Int a) -> [Formula] -> Reader Int a
homol langs fm cont defs = case fm of 
  Not f -> homol langs f (\p -> cont (Not p)) defs
  Atom (R p args) -> 
    let lang = case chooseLang langs fm of 
          Just l -> l 
          Nothing -> __IMPOSSIBLE__ 
    in listify (homot lang) args (\a -> cont (Atom (R p a))) defs
  _ -> error "homol: not a literal"

homo :: Print a => [Lang] -> [Formula] -> ([Formula] -> [Formula] -> Reader Int a) -> [Formula] -> Reader Int a
homo langs fms cont = 
  listify (homol langs) fms
          (\dun defs -> if null defs then cont dun defs
                        else homo langs defs (\res -> cont (dun ++ res)) [])

homogenize :: [Lang] -> [Formula] -> [Formula]
homogenize langs fms = 
  let n = 1 + foldr (Cnf.maxVarIndex "v_") 0 (Fol.fv fms) 
  in Reader.runReader (homo langs fms (\res _ -> return res) []) n

belongs :: Lang -> Formula -> Bool
belongs lang fm = 
  List.all (fn lang) (Fol.functions fm) &&
  List.all (rn lang) (Fol.nums fm) &&
  List.all (pr lang) (Fol.predicates fm \\ [("=", 2)])

langpartition :: [Lang] -> [Formula] -> [[Formula]]
langpartition langs fms = case langs of
  [] -> if null fms then [] else error "langpartition"
  l:ls -> let (fms1, fms2) = List.partition (belongs l) fms in
          fms1 : langpartition ls fms2

-- * Interpolants

arreq :: Vars -> [Formula]
arreq l = case l of 
  v1:v2:rest -> Var v1 ≡ Var v2 : arreq (v2 : rest)
  _ -> []

arrangement :: [Vars] -> [Formula]
arrangement part = 
  foldr (Set.union . arreq) 
    (map (\(v,w) -> Var v ≠ Var w) (List.distinctPairs (map head part))) 
    part

destDef :: Formula -> Maybe (Var, Term)
destDef fm = case fm of 
  Atom (R "=" [Var x, t]) | not (elem x $ Fol.fv t) -> Just (x, t)
  Atom (R "=" [t, Var x]) | not (elem x $ Fol.fv t) -> Just (x, t)
  _ -> Nothing 

redeqs :: Clause -> Clause
redeqs eqs = case List.find (Maybe.isJust . destDef) eqs of
  Just eq -> 
    let (x, t) = case destDef eq of 
          Just xt -> xt 
          Nothing -> __IMPOSSIBLE__ 
    in redeqs (map (Fol.apply (x ⟾ t)) (eqs \\ [eq]))
  Nothing -> eqs

trydps :: [(Lang, Clause)] -> Clause -> Bool
trydps ldseps fms =
  List.any (\(lang, fms0) -> dp lang $ Not $ F.listConj $ redeqs $ fms0 ++ fms)
           ldseps

allpartitions :: Ord a => [a] -> [[[a]]]
allpartitions = foldr (\h y -> foldr (allinsertions h) [] y) [[]] 
  where allinsertions x l acc = 
          foldr (\p acc' -> ((x:p) : (l \\ [p])) : acc') (([x]:l):acc) l

slowNelopRefute :: [Var] -> [(Lang, Clause)] -> Bool
slowNelopRefute vars ldseps = 
  List.all (trydps ldseps . arrangement) (allpartitions vars)

slowNelop1 :: [Lang] -> Clause -> Bool
slowNelop1 langs fms0 = 
  let fms = homogenize langs fms0 
      seps = langpartition langs fms
      fvlist = map Fol.fv seps
      vars = List.filter (\x -> length (List.filter (elem x) fvlist) >= 2) (Set.unions fvlist) 
  in slowNelopRefute vars (zip langs seps)

slowNelop :: [Lang] -> Formula -> Bool
slowNelop langs fm = List.all (slowNelop1 langs) (dnf $ simp $ Not fm)
 where 
  simp = tracef "simp" Skolem.simplify
  dnf = tracef "dnf" Prop.simpdnf

slowNelopInt :: Formula -> Bool
slowNelopInt = slowNelop (addDefault [intLang])

slowNelopDlo :: Formula -> Bool
slowNelopDlo = slowNelop (addDefault [dloLang])

findasubset :: ([a] -> Maybe b) -> Int -> [a] -> Maybe b
findasubset p 0 _ = p []
findasubset _ _ [] = Nothing
findasubset p m (h:t) = 
  case findasubset (p . (h:)) (m-1) t of
    Just x -> Just x
    Nothing -> findasubset p m t

findsubset :: ([a] -> Bool) -> [a] -> Maybe [a]
findsubset p l = 
  List.findFirst (\n -> findasubset (\x -> if p x then Just x else Nothing) n l)
            [0 .. length l]
                   

nelopRefute :: [Formula] -> [(Lang, Clause)] -> Bool
nelopRefute eqs ldseps = 
  case findsubset (trydps ldseps . map F.opp) eqs of
    Nothing -> False
    Just dj -> List.all (\eq -> nelopRefute (eqs \\ [eq])
                                (map (\(dps, es) -> (dps, eq:es)) ldseps)) dj

nelop1 :: [Lang] -> Clause -> Bool
nelop1 langs fms0 = 
  let fms = homogenize langs fms0 
      seps = langpartition langs fms
      fvlist = map (Set.unions . map Fol.fv) seps
      vars = List.filter (\x -> length (List.filter (elem x) fvlist) >= 2)
                         (Set.unions fvlist) 
      eqs = map (\(a,b) -> Equal.mkEq (Var a) (Var b)) (List.distinctPairs vars) in
  nelopRefute eqs (zip langs seps)

nelop :: [Lang] -> Formula -> Bool
nelop langs fm = List.all (nelop1 langs) (Prop.simpdnf $ Skolem.simplify $ Not fm)

-- > nelop :: [Lang] -> Formula -> Bool
-- > nelop langs fm = Debug.impossible

-- > nelop :: [Lang] -> Formula -> Bool
-- > nelop langs fm = Exn.assert False undefined

-- > nelop :: [Lang] -> Formula -> Bool
-- > nelop langs fm = Exn.assert False True

-- > nelop :: [Lang] -> Formula -> Bool
-- > nelop langs fm = __IMPOSSIBLE__

nelopInt :: Formula -> Bool
nelopInt = nelop (addDefault [intLang])

nelopDlo :: Formula -> Bool
nelopDlo = nelop (addDefault [dloLang])

-- let langs = addDefault [intLang]
-- let fm :: Formula = ATP.Util.Parse.parse "1 = 1"
