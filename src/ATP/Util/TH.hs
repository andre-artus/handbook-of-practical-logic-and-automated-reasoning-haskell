
-- Template Haskell utils.

module ATP.Util.TH 
  ( conE
  , conP
  , varE
  , varP
  , appE
  )
where

import Prelude
import qualified Language.Haskell.TH as T

appE :: String -> T.ExpQ -> T.ExpQ
appE = T.appE . T.varE . T.mkName

conE :: String -> [T.ExpQ] -> T.ExpQ
conE c es = foldl1 T.appE $ T.conE (T.mkName c) : es

conP :: String -> [T.PatQ] -> T.PatQ
conP = T.conP . T.mkName

varE :: String -> T.ExpQ
varE = T.varE . T.mkName

varP :: String -> T.PatQ
varP = T.varP . T.mkName
