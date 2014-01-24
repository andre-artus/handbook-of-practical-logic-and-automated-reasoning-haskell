
-- MESON: Model Elimination Subgoal OrieNted

module ATP.Meson
  ( mexpand
  , contrapositives
  , basicMeson
  , meson
  )
where
  
import Prelude 
import qualified ATP.Fol as Fol
import ATP.FormulaSyn
import qualified ATP.Formula as F
import qualified ATP.Prolog as Prolog
import ATP.Prolog(Rule(Rule))
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Tableaux as Tableaux
import qualified ATP.Util.List as List
import ATP.Util.ListSet((\\))
import ATP.Util.Log(Log)
import qualified ATP.Util.Monad as M
import qualified Data.Map as Map

contrapositives :: Clause -> [Rule]
contrapositives cls = 
  let base = map (\c -> Rule (map F.opp (cls \\ [c])) c) cls in
  if all F.negative cls then Rule (map F.opp cls) Bot : base else base

basicMexpand :: [Rule] -> [Formula] -> Formula 
        -> ((Env, Int, Int) -> Maybe a) -> (Env, Int, Int) -> Maybe a
basicMexpand rules ancestors g cont (env, n, k) =
  if n < 0 then fail "Too deep"  else
  let findFn a = do env' <- Tableaux.unifyLiterals env (g, F.opp a) 
                    cont (env', n, k) in
  case List.findFirst findFn ancestors of
    Just env' -> Just env'
    Nothing -> 
      let findFn2 rule = 
            let (Rule asm c, k') = Prolog.renamer k rule in
            do env' <- Tableaux.unifyLiterals env (g,c)
               foldr (basicMexpand rules (g:ancestors)) 
                 cont asm (env', n - length asm, k') in
      List.findFirst findFn2 rules 

pureBasicMeson :: Log m => Formula -> m Int
pureBasicMeson fm = 
  let cls = Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm 
      rules = concat (map contrapositives cls) in
  Tableaux.deepen (\n -> do M.ignore $ basicMexpand rules [] Bot Just (Map.empty, n, 0) 
                            return n) 0

basicMeson :: Log m => Formula -> m [Int]
basicMeson fm = 
  let fm1 = Skolem.askolemize $ Not $ Fol.generalize fm in
  mapM (pureBasicMeson . F.listConj) (Prop.simpdnf fm1)

equal :: Env -> Formula -> Formula -> Bool
equal env fm1 fm2 = 
  case Tableaux.unifyLiterals env (fm1, fm2) of
    Nothing -> False
    Just env' -> env == env'

expand2 :: ([Formula] -> ((Env, Int, Int) -> Maybe a) -> (Env, Int, Int) -> Maybe a) 
        -> [Formula] -> Int -> [Formula] -> Int -> Int 
        -> ((Env, Int, Int) -> Maybe a) -> Env -> Int -> Maybe a
expand2 expfn goals1 n1 goals2 n2 n3 cont env k =
  expfn goals1 (\(e1,r1,k1) ->
       expfn goals2 (\(e2,r2,k2) ->
                       if n2 + r1 <= n3 + r2 then Nothing
                       else cont(e2,r2,k2))
              (e1,n2+r1,k1))
       (env,n1,k)

mexpand ::  [Rule] -> [Formula] -> Formula
        -> ((Env, Int, Int) -> Maybe a) -> (Env, Int, Int) -> Maybe a
mexpand rules ancestors g cont (env,n,k) 
  | n < 0 = fail "Too deep"
  | any (equal env g) ancestors = fail "repetition" 
  | otherwise =
    case List.findFirst (\a -> do env' <- Tableaux.unifyLiterals env (g, F.opp a)
                                  cont (env', n, k)) ancestors of
      Just e -> Just e
      Nothing -> List.findFirst findFn rules
          where findFn r = let (Rule asm c, k') = Prolog.renamer k r in
                           do env' <- Tableaux.unifyLiterals env (g,c)
                              mexpands rules (g:ancestors) asm cont 
                                       (env',n-length asm,k')

mexpands :: [Rule] -> [Formula] -> [Formula] 
         -> ((Env, Int, Int) -> Maybe a) -> (Env, Int, Int) -> Maybe a
mexpands rules ancestors gs cont (env,n,k) =
  if n < 0 then fail "Too deep" else
  let m = length gs in
  if m <= 1 then foldr (mexpand rules ancestors) cont gs (env,n,k) else
  let n1 = n `div` 2 
      n2 = n - n1 
      (goals1,goals2) = splitAt (m `div` 2) gs 
      expfn = expand2 (mexpands rules ancestors) in
  case expfn goals1 n1 goals2 n2 (-1) cont env k of
    Just e -> Just e
    Nothing -> expfn goals2 n1 goals1 n2 n1 cont env k

pureMeson :: Log m => Formula -> m Int
pureMeson fm = 
  let cls = Prop.simpcnf $ Skolem.specialize $ Skolem.pnf fm 
      rules = concat (map contrapositives cls) in
  Tableaux.deepen (\n -> do M.ignore $ mexpand rules [] Bot Just (Map.empty, n, 0) 
                            return n) 0

meson :: Log m => Formula -> m [Int]
meson fm = 
  let fm1 = Skolem.askolemize $ Not $ Fol.generalize fm in
  mapM (pureMeson . F.listConj) (Prop.simpdnf fm1)
