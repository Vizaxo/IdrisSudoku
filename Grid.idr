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
