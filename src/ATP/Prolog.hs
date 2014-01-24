
module ATP.Prolog
  ( Rule(..)
  , renamer
  , hornprove
  , simpleprolog
  , prolog
  )
where
                      
import Prelude 
import qualified ATP.Fol as Fol
import qualified ATP.Formula as F
import ATP.FormulaSyn
import qualified ATP.Prop as Prop
import qualified ATP.Skolem as Skolem
import qualified ATP.Tableaux as Tableaux
import qualified ATP.Unif as Unif
import qualified ATP.Util.Lex as Lex
import qualified ATP.Util.List as List
import ATP.Util.Log(Log)
import qualified ATP.Util.Parse as P
import ATP.Util.Parse (Parse, Parser, parser)
import qualified ATP.Util.Print as PP
import ATP.Util.Print(Print, pPrint, (<+>), (<>)) 
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

data Rule = Rule [Formula] Formula

renamer :: Int -> Rule -> (Rule, Int)
renamer k (Rule asm c) = 
  let fvs = Fol.fv $ F.listConj $ c:asm
      n = length fvs
      vvs = map (\m -> Var ('_' : show m)) [k .. k+n-1]
      inst :: Formula -> Formula 
      inst = Fol.apply $ Map.fromList (zip fvs vvs) in
  (Rule (map inst asm) (inst c), k+n)
      

backchain :: [Rule] -> Int -> Int -> Env -> [Formula] -> Maybe Env
backchain rules n k env goals = case goals of 
  [] -> Just env
  g:gs -> 
    if n == 0 then Nothing else List.findFirst findFn rules
      where findFn rule = 
              let (Rule a c, k') = renamer k rule in
              do env' <- Tableaux.unifyLiterals env (c,g) 
                 backchain rules (n-1) k' env' (a ++ gs)

hornify :: Clause -> Maybe Rule
hornify cls = 
  let (pos, neg) = List.partition F.positive cls in
  if length pos > 1 then Nothing
  else Just $ Rule (map F.opp neg) (if null pos then Bot else head pos)

hornprove :: Log m => Formula -> m (Env, Int)
hornprove fm = 
  let rules = map hornify (Prop.simpcnf $ Skolem.skolemize 
                           $ Not $ Fol.generalize fm) 
      rules' = if any (not . Maybe.isJust) rules 
               then error "clause not horn" else map Maybe.fromJust rules 
      tabFn n = case backchain rules' n 0 Map.empty [Bot] of
                  Nothing -> Nothing
                  Just env -> Just (env, n) in
  Tableaux.deepen tabFn 0

simpleprolog :: [String] -> String -> Maybe Env
simpleprolog rules gl = simpleprolog' (map P.parse rules) (P.parse gl)

simpleprolog' :: [Rule] -> Formula -> Maybe Env
simpleprolog' rules gl = backchain rules (-1) 0 Map.empty [gl]

prolog :: [String] -> String -> Maybe [Formula]
prolog rules gl = prolog' (map P.parse rules) (P.parse gl)

prolog' :: [Rule] -> Formula -> Maybe [Formula]
prolog' rules gl = 
  let mapFn env x = do t <- Map.lookup x env
                       return $ Atom(R "=" [Var x, t]) in
  do env1 <- simpleprolog' rules gl
     env2 <- Unif.solve env1
     mapM (mapFn env2) (Fol.fv gl)

-- -----------------------------------------------------------------------------
--  Parsing                                                                     
-- -----------------------------------------------------------------------------

instance Parse Rule where
  parser = parseRule

parseRule :: Parser Rule
parseRule = 
  do f <- parser
     fs <- P.option [] $ do
            Lex.reservedOp ":-"
            P.commas parser
     Lex.dot
     return $ Rule fs f

-- -----------------------------------------------------------------------------
--  Printing                                                                    
-- -----------------------------------------------------------------------------

instance Print Rule where
  pPrint (Rule [] f) = pPrint f <> PP.text "."
  pPrint (Rule fs f) =
    pPrint f <+> PP.text ":-" 
             <+> PP.cat (PP.punctuate PP.comma (map pPrint fs)) <> PP.text "."
