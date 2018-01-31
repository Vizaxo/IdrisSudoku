module Grid

import Data.Vect

%default total

public export
data Value : (n : Nat) -> Type where
  Empty : Value n
  Filled : (x : Fin n) -> Value n

public export
Eq (Value n) where
  (==) Empty Empty = True
  (==) Empty (Filled x) = False
  (==) (Filled x) Empty = False
  (==) (Filled x) (Filled y) = x == y

public export
data Grid : (n : Nat) -> Type where
  MkGrid : Vect (n*n) (Vect (n*n) (Value (n*n))) -> Grid (n*n)

export
blank : (n : Nat) -> Grid (n*n)
blank n = MkGrid (replicate (n*n) (replicate (n*n) Empty))
