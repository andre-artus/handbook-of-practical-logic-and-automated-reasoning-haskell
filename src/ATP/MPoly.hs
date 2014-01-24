
module ATP.MPoly
  ( Monom
  , mdiv
  , mlcm
  , Poly
  , cmul
  , const
  , var
  , polyatom
  )
where

#include "undefined.h" 

import ATP.Util.Prelude hiding (const, div)
import qualified ATP.Util.Prelude as Prelude
import ATP.Complex (Err, failwith)
import ATP.FormulaSyn
import qualified ATP.Order as Order
import qualified ATP.Util.Monad as M
import qualified Data.List as List
import qualified Ratio

type Monom = (Rational, [Int])

mmul :: Monom -> Monom -> Monom
mmul (c1, m1) (c2, m2) = (c1 * c2, zipWith (+) m1 m2)

mdiv :: Monom -> Monom -> Err Monom
mdiv (c1, m1) (c2, m2) = do 
  r <- M.zipWith indexSub m1 m2
  return $ (c1 / c2, r)
 where 
  indexSub n1 n2 
   | n1 < n2 = failwith "mdiv"
   | otherwise = return $ n1 - n2

mlcm :: Monom -> Monom -> Monom
mlcm (_, m1) (_, m2) = (1, zipWith max m1 m2)

(≪) :: [Int] -> [Int] -> Bool
m1 ≪ m2 = 
  let n1 = sum m1
      n2 = sum m2 
  in n1 < n2 || n1 == n2 && Order.lexord (>) m1 m2

type Poly = [Monom]

instance Num Poly where
  (+) = add
  (-) = sub
  (*) = mul
  negate = neg
  abs = error "Unimplemented" 
  signum = error "Unimplemented" 
  fromInteger = error "Unimplemented"

instance Fractional Poly where
  (/) = div
  recip = inv
  fromRational = error "Unimplemented"

cmul :: Monom -> Poly -> Poly
cmul = map . mmul

neg :: Poly -> Poly
neg = map (first negate)

const :: Vars -> Rational -> Poly
const vars c 
 | c == 0 = []
 | otherwise = [(c, map (Prelude.const 0) vars)]

var :: Vars -> Var -> Poly
var vars x = [(1, map (\y -> if x == y then 1 else 0) vars)]

add :: Poly -> Poly -> Poly
add l1 l2 = case (l1, l2) of
  ([], _) -> l2
  (_, []) -> l1
  ((c1, m1) : o1, (c2, m2) : o2) 
   | m1 == m2 -> 
     let c = c1 + c2
         rest = o1 + o2
     in if c == 0 then rest else (c, m1) : rest
   | m2 ≪ m1 -> (c1, m1) : o1 + l2
   | otherwise -> (c2, m2) : l1 + o2

sub :: Poly -> Poly -> Poly
sub l1 l2 = l1 + (- l2)

mul :: Poly -> Poly -> Poly
mul l1 l2 = case l1 of
  [] -> []
  (h1:t1) -> cmul h1 l2 + t1 * l2

pow :: Vars -> Poly -> Int -> Poly
pow vars l n = iterate (* l) (const vars 1) !! n

inv :: Poly -> Poly
inv p = case p of 
  [(c, m)] | List.all (== 0) m -> [(1 / c, m)]
  _ -> error "mpolyInv: non-constant polynomial"

div :: Poly -> Poly -> Poly
div p q = p * inv q

polynate :: Vars -> Term -> Poly
polynate vars tm = case tm of
  Var x -> var vars x
  [$term| - $t |] -> - (polynate vars t)
  [$term| $s + $t |] -> polynate vars s + polynate vars t
  [$term| $s - $t |] -> polynate vars s - polynate vars t
  [$term| $s * $t |] -> polynate vars s * polynate vars t
  [$term| $s / $t |] -> polynate vars s / polynate vars t
  [$term| $s ^ $n |] -> case n of
     Num n' | Ratio.denominator n' == 1 -> pow vars (polynate vars s) (fromInteger $ Ratio.numerator n')
     _ -> __IMPOSSIBLE__ 
  Num r -> const vars r
  _ -> __IMPOSSIBLE__ 

polyatom :: Vars -> Formula -> Poly
polyatom vars fm = case fm of
  Atom (R "=" [s, t]) -> polynate vars [$term| $s - $t |]
  _ -> error "polyatom: not an equation"

