
module ATP.Bdd 
  ( Bdd
  , taut
  , tests
  )
where

import ATP.Util.Prelude hiding (and, or)
import qualified ATP.Dp as Dp
import ATP.FormulaSyn 
import qualified ATP.Prop as Prop
import qualified Control.Monad.State as State
import Control.Monad.State (State)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Test.QuickCheck as Q
import Test.QuickCheck (Property)


type Index = Int

type Node = (String, Index, Index)

data Bdd = Bdd { -- Range is the integers ∉ {-1.0,1}
                 unique :: Map Node Index
                 -- Domain is the positive integers > 1
               , expand :: Map Index Node
               , next :: Int
               , ord :: String -> String -> Bool
               }

type S = (Bdd, Map (Index, Index) Index)

type BddState a = State S a

expandNode :: Index -> BddState Node
expandNode n = do
  (bdd, _) <- State.get
  return $ 
   if n >= 0 then maybe ("", 1, 1) id (Map.lookup n $ expand bdd)
   else let (p, l, r) = maybe ("", 1, 1) id (Map.lookup (-n) $ expand bdd)
        in (p, -l, -r)

lookupUnique :: Node -> BddState Index
lookupUnique node = do
  (bdd, comp) <- State.get
  case Map.lookup node (unique bdd) of
    Just node' -> return node'
    Nothing -> let n = next bdd in do
      State.put (bdd { unique = Map.insert node n (unique bdd)
                     , expand = Map.insert n node (expand bdd)
                     , next = n + 1 }, comp)
      return n

mkNode :: Node -> BddState Index
mkNode (s, l, r) 
 | l == r = return l
 | l >= 0 = lookupUnique (s, l, r)
 | otherwise = fmap negate $ lookupUnique (s, -l, -r)

new :: (String -> String -> Bool) -> Bdd
new = Bdd Map.empty Map.empty 2

order :: Bdd -> String -> String -> Bool
order bdd p1 p2 = p2 == "" && p1 /= "" || ord bdd p1 p2

and :: Int -> Int -> BddState Index
and m1 m2
  | m1 == -1 || m2 == -1 = return (-1)
  | m1 == 1 = return m2 
  | m2 == 1 = return m1 
  | otherwise =
    do (bdd, comp) <- State.get
       case (Map.lookup (m1, m2) comp, Map.lookup (m2, m1) comp) of
         (Just n, _) -> return n
         (_, Just n) -> return n
         _ -> do 
           (p1, l1, r1) <- expandNode m1
           (p2, l2, r2) <- expandNode m2
           let (p, lpair, rpair) 
                 | p1 == p2 = (p1, (l1, l2), (r1, r2))
                 | order bdd p1 p2 = (p1, (l1, m2), (r1, m2))
                 | otherwise = (p2, (m1, l2), (m1, r2))
           lnew <- uncurry and lpair
           rnew <- uncurry and rpair
           ind <- mkNode (p, lnew, rnew)
           State.modify (\(bdd', comp') -> (bdd', Map.insert (m1, m2) ind comp'))
           return ind

or :: Int -> Int -> BddState Index
or m1 m2 = fmap negate $ and (-m1) (-m2)

imp :: Int -> Int -> BddState Index
imp m1 = or (-m1)

iff :: Int -> Int -> BddState Index
iff m1 m2 = do
  ind1 <- and m1 m2
  ind2 <- and (-m1) (-m2)
  or ind1 ind2

fromFormula :: Formula -> BddState Index
fromFormula fm = case fm of
  Bot -> return (-1)
  Top -> return 1
  Atom (R s []) -> mkNode (s, 1, -1)
  Atom  _ -> error "Non-propositional atom"
  Not p -> fmap negate $ fromFormula p
  And p q -> do
    ind1 <- fromFormula p
    ind2 <- fromFormula q
    and ind1 ind2
  Or p q -> do
    ind1 <- fromFormula p
    ind2 <- fromFormula q
    or ind1 ind2
  Imp p q -> do
    ind1 <- fromFormula p
    ind2 <- fromFormula q
    imp ind1 ind2
  Iff p q -> do
    ind1 <- fromFormula p
    ind2 <- fromFormula q
    iff ind1 ind2
  _ -> error "Quantifiers"

taut :: Formula -> Bool
taut fm = State.evalState (fromFormula fm) (new (<), Map.empty) == 1

-- * Tests

prop_taut_correct :: Property
prop_taut_correct = Q.label "ATP.Bdd: taut_correct" $
  Q.forAll (Prop.forms 5) $ \f -> 
    Dp.dplltaut f == taut f

tests :: IO ()
tests = Q.quickCheck prop_taut_correct

