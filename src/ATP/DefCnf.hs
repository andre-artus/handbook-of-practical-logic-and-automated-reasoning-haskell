
-- Definitional CNF

module ATP.DefCnf 
  ( maxVarIndex
  , maincnf
  , defcnf
  , defcnf1
  , defcnfs
  , tests
  ) 
where

import ATP.Util.Prelude 
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Prop as Prop
import qualified ATP.Util.ListSet as Set
import qualified ATP.Util.Misc as Misc
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Test.QuickCheck as Q
import Test.QuickCheck (Property, (==>))

mkprop :: Int -> (Formula, Int)
mkprop n = (Atom $ R ("p_" ++ show n) [], n + 1)

type Trip = (Formula, Map Formula (Formula, Formula), Int)

maincnf :: Trip -> Trip
maincnf (trip @ (fm, _, _)) = case fm of
   And p q -> defstep And (p, q) trip
   Or p q -> defstep Or (p, q) trip
   Iff p q -> defstep Iff (p, q) trip
   _ -> trip

defstep :: (Formula -> Formula -> Formula) 
        -> (Formula, Formula) -> Trip -> Trip
defstep op (p, q) (_, defs, n) =
  let (fm1, defs1, n1) = maincnf (p, defs, n) 
      (fm2, defs2, n2) = maincnf (q, defs1, n1) 
      fm' = op fm1 fm2 in
  case Map.lookup fm' defs2 of
    Just (v,_) -> (v, defs2, n2)
    Nothing -> (v, Map.insert fm' (v, v ⇔ fm') defs2, n3)
      where (v, n3) = mkprop n2

maxVarIndex :: String -> String -> Int -> Int
maxVarIndex pfx s n =
  let m = length pfx 
      l = length s in
  if l <= m || take m s /= pfx then n else
  let s' = take (l-m) (drop m s) in
  case Misc.getInt s' of
    Nothing -> n
    Just n' -> max n n'

mkDefcnf :: (Trip -> Trip) -> Formula -> [[Formula]]
mkDefcnf fn fm =
  let fm' = Prop.nenf fm 
      n = 1 + F.overatoms (maxVarIndex "p_" . show) fm' 0
      (fm'', defs, _) = fn (fm', Map.empty, n) 
      deflist = map (snd . snd) (Map.toList defs) in
  Set.unions(Prop.simpcnf fm'' : map Prop.simpcnf deflist)

defcnf1 :: Formula -> Formula
defcnf1 fm = F.listConj $ map F.listDisj $ mkDefcnf maincnf fm

{- 
:module + DefCnf Prop
defcnf1 $ parse "(p ∨ (q ∧ ¬ r)) ∧ s"
-} 

subcnf :: (Trip -> Trip) -> (Formula -> Formula -> Formula)
          -> (Formula, Formula) -> Trip -> Trip
subcnf sfn op (p,q) (_, defs, n) =
  let (fm1, defs1, n1) = sfn(p,defs,n) 
      (fm2, defs2, n2) = sfn(q,defs1,n1) in 
  (op fm1 fm2, defs2, n2)

orcnf :: Trip -> Trip
orcnf (trip @ (fm, _, _)) = case fm of
   Or p q -> subcnf orcnf Or (p,q) trip
   _ -> maincnf trip

andcnf :: Trip -> Trip
andcnf (trip @ (fm, _, _)) = case fm of
   And p q -> subcnf andcnf And (p,q) trip
   _ -> orcnf trip

defcnfs :: Formula -> [[Formula]]
defcnfs = mkDefcnf andcnf

defcnf :: Formula -> Formula 
defcnf = F.listConj . map F.listDisj . defcnfs

-- * Tests

prop_defcnf_sat :: Property
prop_defcnf_sat = Q.label "defcnf_sat" $
  Q.forAll (Prop.forms 5) $ \f -> Prop.satisfiable f ==> Prop.satisfiable (defcnf f)

prop_defcnf_sat' :: Property
prop_defcnf_sat' = Q.label "defcnf_sat'" $
  Q.forAll (Prop.forms 5) $ \f -> Prop.satisfiable (defcnf f) ==> Prop.satisfiable f

tests :: IO ()
tests = do 
  Q.quickCheck prop_defcnf_sat
  Q.quickCheck prop_defcnf_sat'
