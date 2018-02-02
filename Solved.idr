module Solved

import Data.Vect
import Grid
import Valid

%default total
%access public export

data NoDups : Vect n a -> Type where
  EmptyNoDups : NoDups []
  ThisNotDup : (contra : Not (Elem x xs)) -> (induction : NoDups xs) -> NoDups (x :: xs)

hasDup : (prf : Elem x xs) -> NoDups (x :: xs) -> Void
hasDup prf (ThisNotDup contra induction) = contra prf

consHasDup : (contra : NoDups xs -> Void) -> NoDups (x :: xs) -> Void
consHasDup contra (ThisNotDup notElem induction) = contra induction

decNoDups : DecEq a => (v : Vect n a) -> Dec (NoDups v)
decNoDups [] = Yes EmptyNoDups
decNoDups (x :: xs) = case isElem x xs of
                           Yes prf => No (hasDup prf)
                           No this => case decNoDups xs of
                                           Yes that => Yes (ThisNotDup this that)
                                           No contra => No (consHasDup contra)

data RecursiveNoDups : Vect n (Vect m a) -> Type where
  EmptyRecursiveNoDups : RecursiveNoDups []
  ThisNoDups : (prf : NoDups x) -> (induction : RecursiveNoDups xs) -> RecursiveNoDups (x :: xs)

restHasDups : (contra : RecursiveNoDups xs -> Void) -> RecursiveNoDups (x :: xs) -> Void
restHasDups contra (ThisNoDups prf induction) = contra induction

thisHasDups : (contra : NoDups x -> Void) -> RecursiveNoDups (x :: xs) -> Void
thisHasDups contra (ThisNoDups prf induction) = contra prf

decRecursiveNoDups : DecEq a => (xs : Vect n (Vect m a)) -> Dec (RecursiveNoDups xs)
decRecursiveNoDups [] = Yes EmptyRecursiveNoDups
decRecursiveNoDups (x :: xs) = case decNoDups x of
                                    Yes xPrf => case decRecursiveNoDups xs of
                                                     Yes xsPrf => Yes (ThisNoDups xPrf xsPrf)
                                                     No contra => No (restHasDups contra)
                                    No contra => No (thisHasDups contra)

data Solved :  (g : Grid n) -> Type where
  SolvedRow : (vaild : Valid (MkGrid xs)) -> (prf : RecursiveNoDups xs) -> Solved (MkGrid xs)

notSolved : (contra : RecursiveNoDups xs -> Void) -> Solved (MkGrid xs) -> Void
notSolved contra (SolvedRow vaild prf) = contra prf

decSolved : (g : Grid n) -> {auto valid : Valid g} -> Dec (Solved g)
decSolved (MkGrid xs) {valid} = case decRecursiveNoDups xs of
                                     Yes prf => Yes (SolvedRow valid prf)
                                     No contra => No ((notSolved contra))
