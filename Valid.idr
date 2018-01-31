module Valid

import Data.Vect
import Grid

%default total
%access public export

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
