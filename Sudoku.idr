module Sudoku

import Data.Vect
import Grid
import Valid
import Solved

%default total
%access public export

-- A helper function for cartesianProduct, to append each element of a list onto each of
-- the vects.
cartesianMapAppend : List a -> (List (Vect k a)) -> (List (Vect (S k) a))
cartesianMapAppend [] ys = []
cartesianMapAppend (x :: xs) [] = []
cartesianMapAppend (x :: xs) ys = map (x::) ys ++ cartesianMapAppend xs ys

-- For a vect where each element could have multiple values, take the cartesian product of
-- the values in each position to determine all possible states the final vect could be in.
-- E.g. [[3,4],[5,6]] Means that the final vector's first position could be 3 or 4, and it's
--                    second position could be 5 or 6.
-- The output would be [[3,5],[4,5],[3,6],[4,6]], which represents the 4 possible states
-- of the output vector
-- This is computed lazily, because the output size grows very quickly w.r.t the input
cartesianProduct : (Vect n (List a)) -> (List (Vect n a))
cartesianProduct [] = [[]]
cartesianProduct (x :: xs) = cartesianMapAppend x (cartesianProduct xs)

mapChoices : Grid n -> (Value n -> List (Value n)) -> (List (Grid n))
mapChoices (MkGrid xs) f = map MkGrid $ cartesianProduct $ map cartesianProduct $ map (map f) xs

setOfFin : List (Fin n)
setOfFin {n} = setOfFin' n
  where setOfFin' : (acc : Nat) -> List (Fin n)
        setOfFin' Z = []
        setOfFin' (S k) = case (natToFin k n) of
                               Just fin => fin :: setOfFin' k
                               Nothing => []

tryValues : Value n -> List (Value n)
tryValues Empty {n} = map Filled setOfFin
tryValues (Filled x) = [Filled x]

filterValid : List (Grid n) -> List (g : (Grid n) ** Valid g)
filterValid [] = []
filterValid (g :: xs) = case decValid g of
                             Yes prf => (g ** prf) :: filterValid xs
                             No contra => filterValid xs

generateCases : (g : Grid n) -> {auto prf : Valid g} -> (List (g' : Grid n ** Valid g'))
generateCases g = filterValid $ mapChoices g tryValues

filterSolved : List (g : (Grid n) ** Valid g) -> List (g : (Grid n) ** (valid : Valid g ** Solved g))
filterSolved [] = []
filterSolved ((g ** valid) :: xs) = case decSolved g of
                                         Yes prf => (g ** valid ** prf) :: filterSolved xs
                                         No contra => filterSolved xs

solveSudoku : (g : Grid n) -> {auto prf : Valid g} -> Lazy (List (g' : (Grid n) ** (valid : Valid g' ** Solved g')))
solveSudoku g = filterSolved $ generateCases g
