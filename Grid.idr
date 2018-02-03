module Grid

import Data.Vect
import Data.List

%default total
%access public export

data Value : (n : Nat) -> Type where
  Empty : Value n
  Filled : (x : Fin n) -> Value n

Eq (Value n) where
  (==) Empty Empty = True
  (==) Empty (Filled x) = False
  (==) (Filled x) Empty = False
  (==) (Filled x) (Filled y) = x == y

Uninhabited (Empty = Filled _) where
  uninhabited Refl impossible

Uninhabited (Filled _ = Empty) where
  uninhabited Refl impossible

negCong : (contra : (x = y) -> Void) -> (Filled x = Filled y) -> Void
negCong contra Refl = contra Refl

DecEq (Value n) where
  decEq Empty Empty = Yes Refl
  decEq Empty (Filled x) = No uninhabited
  decEq (Filled x) Empty = No uninhabited
  decEq (Filled x) (Filled y) = case decEq x y of
                                     Yes prf => Yes (rewrite prf in Refl)
                                     No contra => No (negCong contra)

data Grid : (n : Nat) -> Type where
  MkGrid : Vect (n*n) (Vect (n*n) (Value (n*n))) -> Grid (n*n)

Show (Fin n) where
  show x = show $ finToNat x

Show (Value n) where
  show Empty = "Empty"
  show (Filled x) = "Filled " ++ show x

Show (Grid n) where
  show (MkGrid xs) = Strings.(++) "MkGrid " $ show xs

blank : (n : Nat) -> Grid (n*n)
blank n = MkGrid (replicate (n*n) (replicate (n*n) Empty))

rows : a -> a
rows = id

cols : Vect n (Vect m a) -> Vect m (Vect n a)
cols = transpose

splitUp : Vect (m*n) a -> Vect m (Vect n a)
splitUp xs {n = n} {m = Z} = []
splitUp xs {n = n} {m = (S k)} = take n xs :: splitUp (drop n xs)

boxs : Vect (n*n) (Vect (n*n) a) -> Vect (n*n) (Vect (n*n) a)
boxs xs = ( map Vect.concat . Vect.concat --Combine back into n*n
          . map cols                      --Cols the boxes and rows
          . splitUp . map splitUp)        --Split into m*m*m*m
          xs
