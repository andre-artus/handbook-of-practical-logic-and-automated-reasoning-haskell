
{- 
| An interface for reporting "impossible" errors.  This file
was stolen from Agda.
-} 

module ATP.Util.Impossible 
  ( Impossible(..)
  , throwImpossible 
  , catchImpossible 
  )
where

import Prelude 
import Control.Exception as Exn
import Data.Typeable

{- 
| "Impossible" errors, annotated with a file name and a line
  number corresponding to the source code location of the error.
-} 

data Impossible = Impossible String Integer 
  deriving Typeable

instance Show Impossible where
  show (Impossible file line) = unlines
    [ "An internal error has occurred. Please report this as a bug."
    , "Location of the error: " ++ file ++ ":" ++ show line
    ]

instance Exception Impossible where

{- 
| Abort by throwing an \"impossible\" error. You should not use
  this function directly. Instead use the macro in @undefined.h@.
-} 

throwImpossible :: Impossible -> a
throwImpossible = Exn.throw

{- 
| Catch an \"impossible\" error, if possible.
-} 

catchImpossible :: IO a -> (Impossible -> IO a) -> IO a
catchImpossible = Exn.catch
