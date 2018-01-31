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

data Row : Nat -> a -> Type where
  MkRow : (n : Nat) -> Vect (n*n) a -> Row (n*n) a

data Grid : (n : Nat) -> Type where
  MkGrid : Vect (n*n) (Vect (n*n) (Value (n*n))) -> Grid (n*n)

blank : (n : Nat) -> Grid (n*n)
blank n = MkGrid (replicate (n*n) (replicate (n*n) Empty))

rows : Grid n -> Grid n
rows = id

nodups : Eq a => List a -> Bool
nodups [] = True
nodups (x :: xs) = (not $ elem x xs) && nodups xs

rowsValid : Grid n -> Bool
rowsValid (MkGrid xs) = all (nodups . filter (/= Empty) . toList) xs

cols : Grid n -> Grid n
cols (MkGrid xs) = MkGrid (transpose xs)

colsValid : Grid n -> Bool
colsValid = rowsValid . cols

splitUp : Vect (m*n) a -> Vect m (Vect n a)
splitUp xs {n = n} {m = Z} = []
splitUp xs {n = n} {m = (S k)} = take n xs :: splitUp (drop n xs)

boxs : Grid n -> Grid n
boxs (MkGrid xs) {n=m*m} = MkGrid $
  (map Vect.concat . Vect.concat . --Combine back into n*n
   map transpose .                 --Transpose the boxes and rows
   splitUp . map splitUp)          --Split into m*m*m*m
   xs

boxsValid : Grid n -> Bool
boxsValid = rowsValid . boxs

isValid : Grid n -> Bool
isValid g = rowsValid g && colsValid g && boxsValid g

data Valid : Grid n -> Type where
  IsValid : (g : Grid n) -> {auto prf : isValid g = True} -> Valid g

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
validPrf = IsValid exampleValidGrid

invalidPrf : (contra : Valid Sodoku.exampleInvalidGrid) -> Void
invalidPrf (IsValid exampleInvalidGrid) impossible

isSolved : Grid n -> {auto prf : isValid g = True} -> Bool
isSolved (MkGrid xs) = all (all (/= Empty)) xs

data Solved : Grid n -> Type where
  IsSolved : (g : Grid n) -> {auto valid : isValid g = True} -> {auto solved : isSolved g {prf=valid} = True} -> Solved g

exampleSolved : Grid 1
exampleSolved = MkGrid $ the (Vect (1*1) $ Vect (1*1) (Value (1*1))) $
                         [[Filled 0]]

exampleNotSolved : Grid 1
exampleNotSolved = MkGrid $ the (Vect (1*1) $ Vect (1*1) (Value (1*1))) $
                         [[Empty]]

solvedPrf : Solved Sodoku.exampleSolved
solvedPrf = IsSolved exampleSolved

notSolvedPrf : Solved Sodoku.exampleNotSolved -> Void
notSolvedPrf (IsSolved exampleNotSolved) impossible
