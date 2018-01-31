module Solved

import Data.Vect
import Grid
import Valid

%default total
%access public export

isSolved : (g : Grid n) -> {auto valid : Valid g} -> Bool
isSolved (MkGrid xs) = all (all (/= Empty)) xs

data Solved :  (g : Grid n) -> {auto valid : Valid g} -> Type where
  IsSolved : {auto valid : Valid g} -> (solved : isSolved g {valid} = True) -> Solved g {valid}
