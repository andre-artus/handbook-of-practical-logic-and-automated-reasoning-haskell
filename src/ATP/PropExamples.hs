
module ATP.PropExamples
  ( ramsey
  , mkIndex
  , carry
  , ripplecarry
  , mkAdderTest
  , halfAdder
  , mux
  , prime
  )
where

#include "undefined.h"

import ATP.Util.Prelude
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Prop as P
import qualified ATP.Util.ListSet as Set 
import qualified ATP.Util.Tuple as Tuple

ramsey :: Int -> Int -> Int -> Formula 
ramsey s t n = 
  let vertices = [1 .. n]
      yesgrps = map (Set.allSets 2) (Set.allSets s vertices)
      nogrps = map (Set.allSets 2) (Set.allSets t vertices) 
      e [m, n'] = Atom $ R ("p_" ++ show m ++ "_" ++ show n') [] 
      e _ = __IMPOSSIBLE__ 
  in (F.listDisj $ map (F.listConj . map e) yesgrps)
       ∨ (F.listDisj $ map (F.listConj . map ((¬) . e)) nogrps)

halfsum :: Formula -> Formula -> Formula 
halfsum x y = x ⇔ (¬) y

halfcarry :: Formula -> Formula -> Formula 
halfcarry = (∧)

halfAdder :: Formula -> Formula -> Formula 
          -> Formula -> Formula
halfAdder x y s c = (s ⇔ halfsum x y) ∧ (c ⇔ halfcarry x y)

carry :: Formula -> Formula -> Formula -> Formula
carry x y z = (x ∧ y) ∨ ((x ∨ y) ∧ z)

-- 'sum' is in the Haskell Prelude

csum :: Formula -> Formula -> Formula -> Formula
csum x y z = halfsum (halfsum x y) z

fa :: Formula -> Formula -> Formula -> Formula 
   -> Formula -> Formula
fa x y z s c = (s ⇔ csum x y z) ∧ (c ⇔ carry x y z)

type Wire = Int -> Formula

conjoin :: Wire -> [Int] -> Formula
conjoin f = F.listConj . map f

ripplecarry :: Wire -> Wire -> Wire -> Wire -> Wire
ripplecarry x y c out n = 
  conjoin (\i -> fa (x i) (y i) (c i) (out i) (c (i+1))) [0 .. n-1]

mkIndex :: Var -> Int -> Formula
mkIndex x i = Atom $ R (x ++ "_" ++ show i) []

mkIndex2 :: Var -> Int -> Int -> Formula
mkIndex2 x i j = Atom $ R (x ++ "_" ++ show i ++ "_" ++ show j) []

ripplecarry0 :: Wire -> Wire -> Wire -> Wire -> Wire
ripplecarry0 x y c out n =
  P.simplify (ripplecarry x y (\i -> if i == 0 then Bot else c i) out n)

ripplecarry1 :: Wire -> Wire -> Wire -> Wire -> Wire
ripplecarry1 x y c out n =
  P.simplify
   (ripplecarry x y (\i -> if i == 0 then Top else c i) out n)

mux :: Formula -> Formula -> Formula -> Formula 
mux sel in0 in1 = ((¬) sel ∧ in0) ∨ (sel ∧ in1)

offset :: Int -> Wire -> Wire
offset n x i = x(n + i) 

carryselect :: Wire -> Wire -> Wire -> Wire -> Wire -> Wire -> Wire 
            -> Wire -> Int -> Int -> Formula
carryselect x y c0 c1 s0 s1 c s n k =
  let k' = min n k 
      fm = (ripplecarry0 x y c0 s0 k' ∧ ripplecarry1 x y c1 s1 k') 
           ∧ (c k' ⇔ mux (c 0) (c0 k') (c1 k')) 
           ∧ conjoin (\i -> s i ⇔ mux (c 0) (s0 i) (s1 i)) [0 .. k'-1] in
  if k' < k then fm else
     fm ∧ carryselect
          (offset k x) (offset k y) (offset k c0) (offset k c1)
          (offset k s0) (offset k s1) (offset k c) (offset k s)
          (n - k) k

mkAdderTest :: Int -> Int -> Formula
mkAdderTest n k =
  let (x, y, c, s, c0, s0, c1, s1, c2, s2) = 
        Tuple.map10 mkIndex ("x", "y", "c", "s", "c0", "s0", "c1", "s1", "c2", "s2")
  in (carryselect x y c0 c1 s0 s1 c s n k ∧ (¬) (c 0) ∧
     (ripplecarry0 x y c2 s2 n) ⊃ 
       (c n ⇔ c2 n) ∧ conjoin (\i -> s i ⇔ s2 i) [0 .. n-1])

rippleshift :: Wire -> Wire -> Wire -> Formula -> Wire -> Wire
rippleshift u v c z w n =
  ripplecarry0 u v (\i -> if i == n then w(n - 1) else c(i + 1))
                   (\i -> if i == 0 then z else w(i - 1)) n

type Wire2 = Int -> Int -> Formula

multiplier :: Wire2 -> Wire2 -> Wire2 -> Wire -> Wire
multiplier x u v out n =
  if n == 1 then (out 0 ⇔ x 0 0) ∧ (¬) (out 1) else
  P.simplify
   ((out 0 ⇔ x 0 0) 
    ∧ rippleshift
         (\i -> if i == n-1 then Bot else x 0 (i + 1))
         (x 1) (v 2) (out 1) (u 2) n ∧
            (if n == 2 then (out 2 ⇔ u 2 0) ∧ (out 3 ⇔ u 2 1) else
            conjoin (\k -> rippleshift (u k) (x k) (v(k + 1)) (out k)
                                (if k == n-1 then \i -> out(n + i)
                                 else u(k + 1)) n) [2 .. n-1]))

bitLength :: Int -> Int
bitLength x = if x == 0 then 0 else 1 + bitLength (x `div` 2)

bit :: Int -> Int -> Bool
bit n x = if n == 0 then x `mod` 2 == 1 else bit (n - 1) (x `div` 2)

congruentTo :: Wire -> Wire2
congruentTo x m n =
  conjoin (\i -> if bit i m then x i else (¬) (x i)) [0 .. n-1]

prime :: Int -> Formula
prime p =
  let (x, y, out) = Tuple.map3 mkIndex ("x", "y", "out")
      m i j = x i ∧ y j
      (u, v) = Tuple.map2 mkIndex2 ("u", "v")
      n = bitLength p in
  (¬) (multiplier m u v out (n - 1) ∧
        congruentTo out p (max n (2 * n - 2)))
