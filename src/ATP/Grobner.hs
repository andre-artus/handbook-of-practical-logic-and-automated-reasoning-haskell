
module ATP.Grobner
  ( decide )
where

#include "undefined.h" 

import ATP.Util.Prelude hiding (const, div)
import ATP.Complex (Err, failwith, tryFind)
import qualified ATP.Fol as Fol
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.MPoly as P
import ATP.MPoly (Monom, Poly)
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Util.List as List
import qualified ATP.Util.Log as Log
import ATP.Util.Log (Log)
import qualified ATP.Util.Monad as M

-- * Gröbner bases

type Basis = [Poly]

reduce1 :: Monom -> Poly -> Err Poly
reduce1 cm pol = case pol of 
  [] -> failwith "reduce1"
  hm:cms -> do 
    (c, m) <- P.mdiv cm hm 
    return $ P.cmul (-c, m) cms

reduceb ::  Monom -> Basis -> Err Poly
reduceb = tryFind . reduce1

reduce :: Basis -> Poly -> [Monom]
reduce pols pol = case pol of
  [] -> []
  cm:ptl -> case (do b <- reduceb cm pols
                     return $ reduce pols (b + ptl)) of 
    Left _ -> cm : reduce pols ptl
    Right ms -> ms

spoly :: Poly -> Poly -> Poly
spoly pol1 pol2 = case (pol1, pol2) of
  ([], _) -> []
  (_, []) -> []
  (m1:ptl1, m2:ptl2) -> 
    let m = P.mlcm m1 m2 in
    case (do d1 <- P.mdiv m m1
             d2 <- P.mdiv m m2
             return $ P.cmul d1 ptl1 - P.cmul d2 ptl2) of
      Left _ -> error "spoly"
      Right r -> r

grobner :: Log m => Basis -> [(Poly, Poly)] -> m Basis
grobner basis pairs = do
  Log.infoM "grobner" $ show (length basis) ++ " basis elements and " ++ show (length pairs) ++ " pairs"
  case pairs of
    [] -> return basis
    (p1, p2) : opairs -> 
      let sp = reduce basis (spoly p1 p2) in
      if null sp then grobner basis opairs else
      if List.all (List.all (== 0) . snd) sp then return [sp] else
      let newcps = map (\p -> (p, sp)) basis in
      grobner (sp:basis) (opairs ++ newcps)

groebner :: Log m => Basis -> m Basis
groebner basis = grobner basis (List.distinctPairs basis)

rabinowitsch :: Vars -> Var -> Poly -> Poly
rabinowitsch vars v p = P.const vars 1 - P.var vars v * p

trivial :: Log m => [Formula] -> m Bool
trivial fms = 
  let vars0 = Fol.fv fms
      (eqs, neqs) = List.partition F.positive fms
      rvs = [ Fol.variant ('_' : show n) vars0 | n <- [1..length neqs] ]
      vars = vars0 ++ rvs
      poleqs = map (P.polyatom vars) eqs
      polneqs = map (P.polyatom vars . F.opp) neqs
      pols = poleqs ++ zipWith (rabinowitsch vars) rvs polneqs
  in do 
    b1 <- groebner pols
    return $ null $ reduce b1 (P.const vars 1)

decide :: Log m => Formula -> m Bool
decide fm = 
  let fm1 = Skolem.specialize $ Skolem.prenex $ Skolem.nnf $ Skolem.simplify fm in
  M.all trivial (Prop.simpdnf $ Skolem.nnf $ Not fm1)
