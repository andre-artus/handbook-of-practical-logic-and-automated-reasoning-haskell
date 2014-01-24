
module ATP.Geom
  ( invariantUnderTranslation
  , invariantUnderRotation
  , invariantUnderScaling
  , invariantUnderShearing
  , originate
  , wu 
  )
where

#include "undefined.h" 

import ATP.Util.Prelude 
import ATP.Equal (lhs)
import qualified ATP.Fol as Fol
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Grobner as Grobner
import qualified ATP.Poly as P
import ATP.Poly (zero)
import qualified ATP.Util.List as List
import qualified ATP.Util.ListSet as LSet
import ATP.Util.ListSet ((\\))
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Allow interactive use of Grobner without unused import warning

__ :: Formula -> IO Bool
__ = Grobner.decide

-- * Geometry 

coordinations :: [(String, Formula)]
coordinations = 
  [ -- Points 1, 2 and 3 lie on a common line 
    ( "collinear" 
    , [$form| (x_1 - x_2) * (y_2 - y_3) = (y_1 - y_2) * (x_2 - x_3) |] )
    -- Lines (1,2) and (3,4) are parallel
  , ( "parallel"
    , [$form| (x_1 - x_2) * (y_3 - y_4) = (y_1 - y_2) * (x_3 - x_4) |] )
    -- Lines (1,2) and (3,4) are perpendicular 
  , ( "perpendicular"
    , [$form| (x_1 - x_2) * (x_3 - x_4) + (y_1 - y_2) * (y_3 - y_4) = 0 |] )
    -- Lines (1,2) and (3,4) have the same length 
  , ( "lengths_eq"
    , [$form| (x_1 - x_2)^2 + (y_1 - y_2)^2 = (x_3 - x_4)^2 + (y_3 - y_4)^2 |] )
  , ( "is_midpoint" -- Point 1 is the midpoint of line (2,3) 
    , [$form| 2 * x_1 = x_2 + x_3 ∧ 2 * y_1 = y_2 + y_3 |] )
  , ("is_intersection" -- Lines (2,3) and (4,5) meet at point 1 
    , [$form| (x_1 - x_2) * (y_2 - y_3) = (y_1 - y_2) * (x_2 - x_3) ∧ 
         (x_1 - x_4) * (y_4 - y_5) = (y_1 - y_4) * (x_4 - x_5) |] )
  , ("=" -- Points 1 and 2 are the same
    , [$form| (x_1 = x_2) /\ (y_1 = y_2) |] )
  ]

coordinate :: Formula -> Formula
coordinate = F.onatoms $ \(R a args) -> 
  let getVars (Var v) = (Var $ v ++ "_x", Var $ v ++ "_y")
      getVars _ = __IMPOSSIBLE__ 
      (xtms, ytms) = unzip (map getVars args)
      xs = ["x_" ++ show n | n <- [1 .. length args]]
      ys = ["y_" ++ show n | n <- [1 .. length args]]
      θ = Map.fromList $ zip (xs ++ ys) (xtms ++ ytms)
  in Fol.apply θ (fromJust $ lookup a coordinations)

invariant :: (Term, Term) -> (String, Formula) -> Formula
invariant (x', y') (_s, z) = z ⇔ Fol.apply θ z
 where 
  m n = 
    let x = "x_" ++ show n
        y = "y_" ++ show n
        i = Map.fromList $ zip ["x", "y"] [Var x, Var y]
    in Map.insert x (Fol.apply i x') . Map.insert y (Fol.apply i y')
  θ = foldr m Map.empty [1 .. (5 :: Integer)]

invariantUnderTranslation :: (String, Formula) -> Formula
invariantUnderTranslation = invariant ([$term| x + x' |], [$term| y + y' |])

invariantUnderRotation :: (String, Formula) -> Formula
invariantUnderRotation fm = 
  [$form| s^2 + c^2 = 1 |] ⊃ (invariant ([$term| c * x - s * y |], [$term| s * x + c * y |]) fm)

originate :: Formula -> Formula
originate fm = case Fol.fv fm of
  a:b:_ -> Fol.apply (Map.fromList [ (a ++ "_x", zero), (a ++ "_y", zero), (b ++ "_y", zero)]) (coordinate fm)
  _ -> error "Impossible" 

invariantUnderScaling :: (String, Formula) -> Formula
invariantUnderScaling fm = 
  [$form| ¬ A = 0 |] ⊃ (invariant ([$term| A * x |], [$term| A * y |]) fm)

invariantUnderShearing :: (String, Formula) -> Formula
invariantUnderShearing = invariant ([$term| x + b * y |], [$term| y |])

{- 
:{
(Grobner.decide . originate) 
  [$form| is_midpoint(m,a,c) ∧ perpendicular(a,c,m,b) ⊃ lengths_eq(a,b,b,c) |]
:}
-} 

pprove :: Vars -> [Term] -> Term -> [Formula] -> [Formula]
pprove vars triang p degens 
 | p == zero = degens
 | otherwise = case triang of
   [] -> p ≡ zero : degens
   q@[$term| $_ + ^x * _ |] : qs 
    | x /= head vars -> 
      if elem (head vars) (Fol.fv p) 
      then foldr (pprove vars triang) degens (P.coefficients vars p) 
      else pprove (tail vars) triang p degens
    | otherwise -> 
      let (k, p') = P.pdivide vars p q in
      if k == 0 then pprove vars qs p' degens else
      let degens' = (¬) (P.phead vars q ≡ zero) : degens in
      foldr (pprove vars qs) degens' (P.coefficients vars p') 
   _ -> __IMPOSSIBLE__ 

triangulate :: Vars -> [Term] -> [Term] -> [Term]
triangulate vars consts pols 
 | null vars = pols
 | otherwise = 
   let (cns, tpols) = List.partition (P.isConstant vars) pols in
   if null cns then triangulate vars (cns ++ consts) tpols else
   if length pols <= 1 then pols ++ triangulate (tail vars) [] consts else
   let n = minimum $ map (P.degree vars) pols
       p = fromJust $ List.find (\p' -> P.degree vars p' == n) pols
       ps = pols \\ [p]
   in triangulate vars consts $ p : map (\q -> snd $ P.pdivide vars q p) ps

wu :: Formula -> Vars -> Vars -> [Formula]
wu fm vars zeros =
  let gfm0 = coordinate fm
      gfm = Fol.apply (foldr (flip Map.insert zero) Map.empty zeros) gfm0
  in if not $ Set.fromList vars == Set.fromList (Fol.fv gfm) then error "wu: bad parameters" else
  let (ant, con) = F.destImp gfm
      pols = map (lhs . P.atom vars) (F.conjuncts ant)
      ps = map (lhs . P.atom vars) (F.conjuncts con)
      tri = triangulate vars [] pols
  in foldr (\p -> LSet.union (pprove vars tri p [])) [] ps 
