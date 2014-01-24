
module ATP.Rewrite
  ( rewrite )
where

import Prelude 
import qualified ATP.Fol as Fol
import ATP.FormulaSyn
import qualified ATP.Resolution as Resolution
import qualified Data.Map as Map

rewrite1 :: [Formula] -> Term -> Maybe Term
rewrite1 eqs t = case eqs of
  Atom(R "=" [l,r]):oeqs -> 
    case Resolution.termMatch Map.empty [(l,t)] of
      Nothing -> rewrite1 oeqs t
      Just env -> Just $ Fol.apply env r
  _ -> Nothing

rewrite :: [Formula] -> Term -> Term
rewrite eqs tm = 
  case rewrite1 eqs tm of
    Just tm' -> rewrite eqs tm'
    Nothing -> 
      case tm of 
        Var _ -> tm
        Num _ -> tm
        Fn f args -> let tm' = Fn f (map (rewrite eqs) args) in
                     if tm' == tm then tm else rewrite eqs tm'
