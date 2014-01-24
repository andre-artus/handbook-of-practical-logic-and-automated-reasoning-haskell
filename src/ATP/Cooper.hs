
module ATP.Cooper
  ( zero
  , one
  , isInteger
  , integer1
  , integer2
  , destInteger
  , evalc
  , integerQelim
  , naturalQelim
  )
where

#include "undefined.h" 

import ATP.Util.Prelude
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Order as Order
import qualified ATP.Qelim as Qelim
import qualified ATP.Skolem as Skolem
import ATP.Util.ListSet ((∪))
import qualified ATP.Util.Print as PP
import qualified Data.List as List
import qualified Ratio

-- * Numerals

zero :: Term
zero = Num 0

one :: Term
one = Num 1

makeInteger :: Integer -> Term
makeInteger n = Num $ n Ratio.% 1

isInteger :: Term -> Bool
isInteger (Num n) = Ratio.denominator n == 1
isInteger _ = False

destInteger :: Term -> Integer
destInteger (Num n) = 
  if Ratio.denominator n == 1 then Ratio.numerator n
  else error "non-integral rational"
destInteger t = error' $ PP.text "illegal integer:" <+> pPrint t

integer1 :: (Integer -> Integer) -> Term -> Term
integer1 fn = makeInteger . fn . destInteger

integer2 :: (Integer -> Integer -> Integer) -> Term -> Term -> Term
integer2 fn m n = makeInteger $ fn (destInteger m) (destInteger n)

linearCmul :: Integer -> Term -> Term
linearCmul 0 _ = zero
linearCmul n tm = 
  case tm of 
    [$term| $c * $x + $r |] -> integer1 ((*) n) c * x + linearCmul n r
    k -> integer1 ((*) n) k

linearAdd :: Vars -> Term -> Term -> Term
linearAdd vars tm1 tm2 =
  case (tm1, tm2) of 
    ([$term| $c1 * ^x1 + $r1 |], [$term| $c2 * ^x2 + $r2|]) -> 
       if x1 == x2 then
         let c = integer2 (+) c1 c2 in
         if c == zero then linearAdd vars r1 r2
         else c * Var x1 + linearAdd vars r1 r2
       else if Order.earlier vars x1 x2 then
         c1 * Var x1 + linearAdd vars r1 tm2
       else
         c2 * Var x2 + linearAdd vars tm1 r2
    ([$term| $c1 * ^x1 + $r1 |], _) -> c1 * Var x1 + linearAdd vars r1 tm2
    (_, [$term| $c2 * ^x2 + $r2 |]) -> c2 * Var x2 + linearAdd vars tm1 r2
    _ -> integer2 (+) tm1 tm2

linearNeg :: Term -> Term
linearNeg = linearCmul (-1)

linearSub :: Vars -> Term -> Term -> Term
linearSub vars tm1 tm2 = linearAdd vars tm1 (linearNeg tm2)

linearMul :: Term -> Term -> Term
linearMul tm1 tm2 = 
  if isInteger tm1 then linearCmul (destInteger tm1) tm2
  else if isInteger tm2 then linearCmul (destInteger tm2) tm1
  else error ("linearMul: nonlinearity: (" ++ show tm1 ++ ", " ++ show tm2 ++ ")")

lint :: Vars -> Term -> Term
lint vars tm =
  case tm of
   [$term| ^_ |] -> one * tm + zero
   [$term| - $t |] -> linearNeg (lint vars t)
   [$term| $s + $t |] -> linearAdd vars (lint vars s) (lint vars t)
   [$term| $s - $t |] -> linearSub vars (lint vars s) (lint vars t)
   [$term| $s * $t |] -> linearMul (lint vars s) (lint vars t)
   _ -> if isInteger tm then tm else error $ "lint: unknown term: " ++ show tm

mkatom :: Vars -> Pred -> Term -> Formula 
mkatom vars p t = Atom (R p [zero, lint vars t])

linform :: Vars -> Formula -> Formula 
linform vars fm =
 case fm of
   Atom(R "divides" [c, t]) -> Atom(R "divides" [integer1 abs c, lint vars t])
   [$form| $s = $t |] -> mkatom vars "=" (t - s)
   [$form| $s < $t |] -> mkatom vars "<" (t - s)
   [$form| $s > $t |] -> mkatom vars "<" (s - t)
   [$form| $s ≤ $t |] -> mkatom vars "<" (t + one - s)
   [$form| $s ≥ $t |] -> mkatom vars "<" (s + one - t)
   _ -> fm 

posineq :: Formula -> Formula 
posineq fm = case fm of
  [$form| ¬ ($n0 < $t) |] | n0 == zero -> zero ≺ linearSub [] one t
  _ -> fm

formlcm :: Term -> Formula -> Integer
formlcm x f = case f of
  Atom(R _ [_, [$term| $c * $y + _ |]]) 
   | x == y -> abs $ destInteger c
  Not p -> formlcm x p
  And p q -> lcm (formlcm x p) (formlcm x q)
  Or p q -> lcm (formlcm x p) (formlcm x q)   
  _ -> 1

adjustcoeff :: Term -> Integer -> Formula -> Formula 
adjustcoeff x l fm = 
 case fm of
   Atom (R p [d, [$term| $c * $y + $z |]]) | y == x ->
     let m = l `div` (destInteger c)
         n = if p == "<" then abs m else m
         xtm = fromInteger (m `div` n) * x in
     Atom(R p [linearCmul (abs m) d, xtm + linearCmul n z])
   Not p -> (¬) $ adjustcoeff x l p
   And p q -> adjustcoeff x l p ∧ adjustcoeff x l q
   Or p q -> adjustcoeff x l p ∨ adjustcoeff x l q
   _ -> fm

unitycoeff :: Term -> Formula -> Formula 
unitycoeff x fm = 
  let l = formlcm x fm
      fm' = adjustcoeff x l fm in
  if l == 1 then fm' else
  let xp = one * x + zero in
  Atom (R "divides" [fromInteger l, xp]) ∧ adjustcoeff x l fm

minusinf :: Term -> Formula -> Formula 
minusinf x fm =
 case fm of
   [$form| $n0 = $n1 * $y + _ |] 
    | n0 == zero && n1 == one && x == y -> (⊥)
   [$form| $n0 < $n1 * $y + _ |] 
    | n0 == zero && n1 == one && x == y -> (⊥)
   [$form| $n0 < _ * $y + _ |] 
    | n0 == zero && x == y -> (⊤)
   [$form| ¬ $p |] -> (¬) $ minusinf x p
   [$form| $p ∧ $q |] -> minusinf x p ∧ minusinf x q
   [$form| $p ∨ $q |] -> minusinf x p ∨ minusinf x q
   _ -> fm

divlcm :: Term -> Formula -> Integer
divlcm x fm =
 case fm of
   Atom (R "divides" [d, [$term| _ * $y + _ |]]) 
    | x == y -> destInteger d
   Not p -> divlcm x p
   And p q -> lcm (divlcm x p) (divlcm x q)
   Or p q -> lcm (divlcm x p) (divlcm x q)
   _ -> 1

bset :: Term -> Formula -> [Term]
bset x fm = case fm of 
  [$form| ¬ ($n0 = $n1 * $y + $a) |] 
   | n0 == zero && n1 == one && x == y -> [linearNeg a]
  [$form| $n0 = $n1 * $y + $a |] 
   | n0 == zero && n1 == one && x == y -> [linearNeg $ linearAdd [] a one]
  [$form| $n0 < $n1 * $y + $a |] 
   | n0 == zero && n1 == one && x == y -> [linearNeg a]
  [$form| ¬ $p |] -> bset x p
  [$form| $p ∧ $q |] -> bset x p ∪ bset x q
  [$form| $p ∨ $q |] -> bset x p ∪ bset x q
  _ -> []

linrep :: Vars -> Term -> Term -> Formula -> Formula 
linrep vars x t fm =
 case fm of
   Atom(R p [d, [$term| $c * $y + $a |]]) | x == y ->
     let ct = linearCmul (destInteger c) t in
     Atom $ R p [d, linearAdd vars ct a]
   Not p -> (¬) $ linrep vars x t p
   And p q -> linrep vars x t p ∧ linrep vars x t q
   Or p q -> linrep vars x t p ∨ linrep vars x t q
   _ -> fm

cooper :: Vars -> Formula -> Formula 
cooper vars (Ex x0 p0) =
  let x = Var x0
      p = unitycoeff x p0
      p_inf = Skolem.simplify $ minusinf x p
      bs = bset x p
      js = [1 .. divlcm x p]
      p_element j b = linrep vars x (linearAdd vars b (makeInteger j)) p
      stage j = F.listDisj
        (linrep vars x (makeInteger j) p_inf :
         map (p_element j) bs) 
  in F.listDisj (map stage js)
cooper _ _ = error "cooper: not an existential formula"

operations :: [(Pred, Integer -> Integer -> Bool)]
operations = [ ("=",(==))
             , ("<",(<))
             , (">",(>)) 
             , ("<=",(<=))
             , ("≤",(<=)) 
             , (">=",(>=))
             , ("≥",(>=))
             , ("divides", \x y -> y `mod` x == 0)
             ]

evalc :: Formula -> Formula 
evalc = F.onatoms atfn 
 where 
  atfn (at@(R p [s, t])) = case List.lookup p operations of
    Just op -> 
      if isInteger s && isInteger t then 
        if op (destInteger s) (destInteger t) then (⊤) else (⊥)
      else Atom at
    Nothing -> Atom at
  atfn _ = __IMPOSSIBLE__ 

integerQelim :: Formula -> Formula 
integerQelim = 
 Skolem.simplify . evalc . Qelim.lift linform (Qelim.cnnf posineq . evalc) cooper

relativize :: (Var -> Formula) -> Formula -> Formula 
relativize r fm =
 case fm of
   Not p -> (¬) $ relativize r p
   And p q -> relativize r p ∧ relativize r q
   Or p q -> relativize r p ∨ relativize r q
   Imp p q -> relativize r p ⊃ relativize r q
   Iff p q -> relativize r p ⇔ relativize r q
   All x p -> (¥) x (r x ⊃ relativize r p)
   Ex x p -> (∃) x (r x ∧ relativize r p)
   _ -> fm

naturalQelim :: Formula -> Formula 
naturalQelim = integerQelim . relativize (\x -> zero ≤ Var x)
