module Sodoku

import Data.Vect

data Value : (n : Nat) -> Type where
  Empty : Value n
  Filled : (x : Fin n) -> Value n

Eq (Value n) where
  (==) Empty Empty = True
  (==) Empty (Filled x) = False
  (==) (Filled x) Empty = False
  (==) (Filled x) (Filled y) = x == y

data Grid : (n : Nat) -> Type where
  MkGrid : Vect (n*n) (Vect (n*n) (Value (n*n))) -> Grid (n*n)

blank : (n : Nat) -> Grid (n*n)
blank n = MkGrid (replicate (n*n) (replicate (n*n) Empty))

nodups : Eq a => List a -> Bool
nodups [] = True
nodups (x :: xs) = (not $ elem x xs) && nodups xs

rowsValid : Grid n -> Bool
rowsValid (MkGrid xs) = all (nodups . filter (/= Empty) . toList) xs

colsToRows : Grid n -> Grid n
colsToRows (MkGrid xs) = MkGrid (transpose xs)

colsValid : Grid n -> Bool
colsValid = rowsValid . colsToRows

splitUp : Vect (m*n) a -> Vect m (Vect n a)
splitUp xs {n = n} {m = Z} = []
splitUp xs {n = n} {m = (S k)} = take n xs :: splitUp (drop n xs)

boxsToRows : Grid n -> Grid n
boxsToRows (MkGrid xs) = MkGrid $
  (map Vect.concat . Vect.concat . --Combine back into n*n
   map transpose .                 --Transpose the boxes and rows
   splitUp . map splitUp)          --Split into m*m*m*m
  xs

boxsValid : Grid n -> Bool
boxsValid = rowsValid . boxsToRows

isValid : Grid n -> Bool
isValid g = rowsValid g && colsValid g && boxsValid g

data Valid : Grid n -> Type where
  IsValid : {g : Grid n} -> (prf : isValid g = True) -> Valid g

exampleValidGrid : Grid 4
exampleValidGrid = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Empty, Empty],
                          [Filled 0, Empty, Empty, Filled 3],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Empty, Empty, Filled 2]]

exampleInvalidGrid : Grid 4
exampleInvalidGrid = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Empty, Empty],
                          [Filled 1, Empty, Empty, Filled 3],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Empty, Empty, Filled 2]]

validPrf : Valid Sodoku.exampleValidGrid
validPrf = IsValid Refl

invalidPrf : (contra : Valid Sodoku.exampleInvalidGrid) -> Void
invalidPrf (IsValid Refl) impossible

isSolved : (g : Grid n) -> {auto valid : Valid g} -> Bool
isSolved (MkGrid xs) = all (all (/= Empty)) xs

data Solved :  (g : Grid n) -> {auto valid : Valid g} -> Type where
  IsSolved : {auto valid : Valid g} -> (solved : isSolved g {valid} = True) -> Solved g {valid}

exampleSolved : Grid 1
exampleSolved = MkGrid $ the (Vect (1*1) $ Vect (1*1) (Value (1*1))) $
                         [[Filled 0]]

exampleNotSolved : Grid 1
exampleNotSolved = MkGrid $ the (Vect (1*1) $ Vect (1*1) (Value (1*1))) $
                         [[Empty]]

solvedPrf : Solved Sodoku.exampleSolved
solvedPrf = IsSolved Refl

notSolvedPrf : Solved Sodoku.exampleNotSolved -> Void
notSolvedPrf (IsSolved Refl) impossible

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
