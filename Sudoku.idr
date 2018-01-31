module Sudoku

import Data.Vect
import Grid
import Valid
import Solved

%default total

generateCases : (g : Grid n) -> {auto prf : Valid g} -> Lazy (List (g : (Grid n) ** Valid g))
generateCases g = ?a

notSolved : {valid : Valid g} -> (contra : isSolved g {valid} = True -> Void) -> Solved g {valid} -> Void
notSolved contra (IsSolved solved) = contra solved

decSolved : (g : Grid n) -> {auto prf : Valid g} -> Dec (Solved g)
decSolved g = case decEq (isSolved g) True of
                   Yes prf => Yes $ IsSolved prf
                   No contra => No $ notSolved contra

filterSolved : List (g : (Grid n) ** Valid g) -> List (g : (Grid n) ** (valid : Valid g ** Solved g))
filterSolved [] = []
filterSolved ((g ** valid) :: xs) = case decSolved g of
                                         (Yes prf) => (g ** valid ** prf) :: filterSolved xs
                                         (No contra) => filterSolved xs

solve : (g : Grid n) -> {auto prf : Valid g} -> List (g' : (Grid n) ** (valid : Valid g' ** Solved g'))
solve g = filterSolved $ generateCases g
