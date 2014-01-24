
-- * Stålmark's method

module ATP.Stal 
  ( stalmarck )
where

#include "undefined.h" 

import ATP.Util.Prelude 
import qualified ATP.DefCnf as Cnf
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Prop as Prop
import qualified ATP.Util.List as List
import qualified ATP.Util.ListSet as Set
import ATP.Util.ListSet ((∪), (∩), (\\))
import qualified ATP.Util.Log as Log
import ATP.Util.Log (Log)
import qualified ATP.Util.UnionFind as UF
import ATP.Util.UnionFind (Partition)
import qualified Data.Map as Map
import Data.Map (Map)

type Part = Partition Formula
type Pair = (Formula, Formula)
type Pairs = [Pair]
type Trigger = (Pair, Pairs)
type Triggers = [Trigger]
type TrigMap = Map Formula Triggers
type Erf = (Part, TrigMap)

name :: Rel -> String
name (R f []) = f
name _ = __IMPOSSIBLE__ 

triplicate :: Formula -> (Formula, [Formula])
triplicate fm = 
  let fm' = Prop.nenf fm
      n = 1 + F.overatoms (Cnf.maxVarIndex "p_" . name) fm' 0 
      (p, defs, _) = Cnf.maincnf (fm', Map.empty, n)
  in (p, map (snd . snd) (Map.toList defs))

atom :: Formula -> Formula
atom lit = if F.negative lit then F.opp lit else lit

align :: Pair -> Pair
align (p, q) = 
  if atom p < atom q then align (q, p) else
  if F.negative p then (F.opp p, F.opp q) else (p, q)

equate2 :: Pair -> Part -> Part
equate2 (p, q) eqv =  UF.equate (F.opp p, F.opp q) (UF.equate (p, q) eqv)

irredundant :: Part -> Pairs -> Pairs
irredundant rel eqs = case eqs of
  [] -> []
  (p, q) : oth -> 
    if UF.canonize rel p == UF.canonize rel q then irredundant rel oth
    else Set.insert (p, q) $ irredundant (equate2 (p, q) rel) oth

consequences :: Pair -> Formula -> Pairs -> Pairs
consequences peq@(p, q) fm eqs =
  let follows (r, s) = Prop.tautology $ ((p ⇔ q) ∧ fm) ⊃ (r ⇔ s) in
  irredundant (equate2 peq UF.unequal) (filter follows eqs)

triggers :: Formula -> Triggers
triggers fm = 
  let poslits = Set.insert (⊤) (map Atom $ Prop.atoms fm)
      lits = poslits ∪ map F.opp poslits
      pairs = List.allPairs (,) lits lits
      npairs = filter (\(p, q) -> atom p /= atom q) pairs
      eqs = Set.setify $ map align npairs
      raw = map (\p -> (p, consequences p fm eqs)) eqs
  in filter (not . null . snd) raw

trigger :: Formula -> Triggers
trigger fm = case fm of
  [$form| $x ⇔ $y ∧ $z |] -> instTrigger (x, y, z) trigAnd
  [$form| $x ⇔ $y ∨ $z |] -> instTrigger (x, y, z) trigOr
  [$form| $x ⇔ $y ⊃ $z |] -> instTrigger (x, y, z) trigImp
  [$form| $x ⇔ ($y ⇔ $z) |] -> instTrigger (x, y, z) trigIff
  _ -> __IMPOSSIBLE__ 
 where 
  trigAnd = triggers [$form| p ⇔ q ∧ r |]
  trigOr = triggers [$form| p ⇔ q ∨ r |]
  trigImp = triggers [$form| p ⇔ q ⊃ r |]
  trigIff = triggers [$form| p ⇔ (q ⇔ r) |]
  ddnegate [$form| ¬ ¬ $p |] = p
  ddnegate f = f
  instfn (x, y, z) = 
    let subfn = Map.fromList [ (R "p" [], x), (R "q" [], y), (R "r" [], z) ] 
    in ddnegate . Prop.apply subfn
  inst2fn i (p, q) = align $ (instfn i p, instfn i q)
  instnfn i (a, c) = (inst2fn i a, map (inst2fn i) c)
  instTrigger = map . instnfn

relevance :: Triggers -> TrigMap
relevance trigs =
  let insertRelevant :: Formula -> Trigger -> TrigMap -> TrigMap
      insertRelevant p trg f = 
        Map.insert p (Set.insert trg $ maybe [] id (Map.lookup p f)) f
      insertRelevant2 trg@((p,q), _) = insertRelevant p trg . insertRelevant q trg
  in foldr insertRelevant2 Map.empty trigs 

equatecons :: Pair -> Erf -> (Pairs, Erf)
equatecons (p0, q0) erf@(eqv, rfn) =
  let p = UF.canonize eqv p0 
      q = UF.canonize eqv q0
  in if p == q then ([], erf) else
  let p' = UF.canonize eqv (F.opp p0)
      q' = UF.canonize eqv (F.opp q0)
      eqv' = equate2 (p, q) eqv
      look f = maybe [] id (Map.lookup f rfn)
      spPos = look p
      spNeg = look p'
      sqPos = look q
      sqNeg = look q'
      rfn' = Map.insert (UF.canonize eqv' p) (spPos ∪ sqPos) $
              Map.insert (UF.canonize eqv' p') (spNeg ∪ sqNeg) rfn
      nw = (spPos ∩ sqPos) ∪ (spNeg ∩ sqNeg)
  in (foldr (Set.union . snd) [] nw, (eqv', rfn'))

zeroSaturate :: Erf -> Pairs -> Erf
zeroSaturate erf assigs = case assigs of
  [] -> erf
  (p, q) : ts -> 
   let (news, erf') = equatecons (p, q) erf in
   zeroSaturate erf' (ts ∪ news)             

zeroSaturateAndCheck :: Erf -> Pairs -> Erf
zeroSaturateAndCheck erf trigs =
  let erf'@(eqv', _) = zeroSaturate erf trigs
      vars = filter F.positive (UF.equated eqv')
  in if List.any (\x -> UF.canonize eqv' x == UF.canonize eqv' ((¬) x)) vars
     then snd $ equatecons (Top, Not Top) erf' else erf'

truefalse :: Part -> Bool
truefalse pfn = UF.canonize pfn (Not Top) == UF.canonize pfn Top

-- * Higher Saturation Levels

equateset :: [Formula] -> Erf -> Erf
equateset s0 eqfn = case s0 of
  a : s1@(b : _) -> equateset s1 (snd $ equatecons (a, b) eqfn)
  _ -> eqfn

inter :: [Formula] -> Erf -> Erf -> Map Formula [Formula] -> Map Formula [Formula] -> Erf -> Erf
inter els erf1@(eq1, _) erf2@(eq2, _) rev1 rev2 erf = case els of
  [] -> erf
  x:xs -> 
    let b1 = UF.canonize eq1 x
        b2 = UF.canonize eq2 x
        s1 = maybe __IMPOSSIBLE__ id (Map.lookup b1 rev1)
        s2 = maybe __IMPOSSIBLE__ id (Map.lookup b2 rev2)
        s = s1 ∩ s2
    in inter (xs \\ s) erf1 erf2 rev1 rev2 (equateset s erf)

reverseq :: [Formula] -> Part -> Map Formula [Formula]
reverseq domain eqv =
  let a1 = map (\x -> (x, UF.canonize eqv x)) domain in
  foldr (\(y, x) f -> Map.insert x (Set.insert y (maybe [] id $ Map.lookup x f)) f)
    Map.empty a1

stalIntersect :: Erf -> Erf -> Erf -> Erf
stalIntersect erf1@(eq1, _) erf2@(eq2, _) erf =
  if truefalse eq1 then erf2 else if truefalse eq2 then erf1 else
  let dom1 = UF.equated eq1
      dom2 = UF.equated eq2
      comdom = dom1 ∩ dom2
      rev1 = reverseq dom1 eq1 
      rev2 = reverseq dom2 eq2
  in inter comdom erf1 erf2 rev1 rev2 erf

saturate :: Int -> Erf -> Pairs -> [Formula] -> Erf
saturate n erf assigs allvars =
  let erf'@(eqv', _) = zeroSaturateAndCheck erf assigs in
  if n == 0 || truefalse eqv' then erf' else
  let erf''@(eqv'', _) = splits n erf' allvars allvars in
  if eqv'' == eqv' then erf'' else saturate n erf'' [] allvars

splits :: Int -> Erf -> [Formula] -> [Formula] -> Erf
splits n erf@(eqv, _) allvars vars = case vars of
  [] -> erf
  p : ovars -> 
    if UF.canonize eqv p /= p then splits n erf allvars ovars else
    let erf0 = saturate (n-1) erf [(p, Not Top)] allvars
        erf1 = saturate (n-1) erf [(p, Top)] allvars
        erf'@(eqv', _) = stalIntersect erf0 erf1 erf
    in if truefalse eqv' then erf' else splits n erf' allvars ovars

saturateUpto :: Log m => [Formula] -> Int -> Int -> Triggers -> Pairs -> m Bool
saturateUpto vars n m trigs assigs =
 if n > m then error $ "Not " ++ show m ++ "-easy" else do
 Log.infoM "saturateUpto" $ "*** Starting " ++ show n ++ "-saturation"
 Log.debugM' "saturateUpto" $ pPrint (vars, n, m, trigs, assigs)
 let (eqv, _) = saturate n (UF.unequal, relevance trigs) assigs vars
 if truefalse eqv then return True else saturateUpto vars (n+1) m trigs assigs

stalmarck :: Log m => Formula -> m Bool
stalmarck fm = 
  let includeTrig (e, cqs) f = Map.insert e (cqs ∪ maybe [] id (Map.lookup e f)) f
      fm' = Prop.simplify $ (¬) fm
  in if fm' == (⊥) then return True else if fm' == (⊤) then return False else
  let (p, triplets) = triplicate fm'
      trigfn = foldr (flip (foldr includeTrig) . trigger) Map.empty triplets
      vars = map Atom (Set.unions $ map Prop.atoms triplets)
  in saturateUpto vars 0 2 (Map.toList trigfn) [(p, (⊤))]

