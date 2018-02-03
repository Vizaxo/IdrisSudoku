module Valid

import Grid
import Data.Vect

%default total
%access public export

data NoDupsButEmpty : Vect n (Value m) -> Type where
  EmptyList : NoDupsButEmpty []
  ThisEmpty : (induction : NoDupsButEmpty xs) -> NoDupsButEmpty (Empty :: xs)
  ThisValue : (prf : Not (Elem x xs)) -> (induction : NoDupsButEmpty xs) -> NoDupsButEmpty (x :: xs)

data HasDupValue : Vect n (Value m) -> Type where
  ThisDupValue : (prf : Elem x xs) -> (notEmpty : Not (Empty = x)) -> HasDupValue (x :: xs)
  ThatDupValue : (induction : HasDupValue xs) -> HasDupValue (x :: xs)

Uninhabited (HasDupValue []) where
  uninhabited (ThisDupValue _ _) impossible
  uninhabited (ThatDupValue _) impossible

notThisOrThatDupValue : (notElem : Not (Elem (Filled x) xs)) ->
                        (noDupXs : Not (HasDupValue xs)) ->
                        HasDupValue ((Filled x) :: xs) -> Void
notThisOrThatDupValue notElem noDupXs (ThisDupValue prf notEmpty) = notElem prf
notThisOrThatDupValue notElem noDupXs (ThatDupValue induction) = noDupXs induction

notThatDupEmpty : (contra : Not (HasDupValue xs)) -> HasDupValue (Empty :: xs) -> Void
notThatDupEmpty contra (ThisDupValue prf emptyInverse) = emptyInverse Refl
notThatDupEmpty contra (ThatDupValue prf) = contra prf

decHasDupValue : (v : Vect n (Value m)) -> Dec (HasDupValue v)
decHasDupValue [] = No uninhabited
decHasDupValue (Empty :: xs) = case decHasDupValue xs of
                                    Yes prf => Yes (ThatDupValue prf)
                                    No contra => No (notThatDupEmpty contra)
decHasDupValue ((Filled x) :: xs) = case decHasDupValue xs of
                                         Yes prf => Yes (ThatDupValue prf)
                                         No noDupXs => case isElem (Filled x) xs of
                                                           Yes prf => Yes (ThisDupValue prf uninhabited)
                                                           No notElem => No (notThisOrThatDupValue notElem noDupXs)

data InvalidRows : Vect n (Vect m a) -> Type where
  ThisRowInvalid : (prf : HasDupValue x) -> InvalidRows (x :: xs)
  ThatRowInvalid : (prf : InvalidRows xs) -> InvalidRows (x :: xs)

Uninhabited (InvalidRows []) where
  uninhabited (ThisRowInvalid _) impossible
  uninhabited (ThatRowInvalid _) impossible

data ValidRows : Vect n (Vect m a) -> Type where
  ValidEmpty : ValidRows []
  ValidRow : (prf : NoDupsButEmpty x) -> (induction : ValidRows xs) -> ValidRows (x :: xs)
  NotInvalidRow : (contra : Not (HasDupValue x)) -> (induction : ValidRows xs) -> ValidRows (x :: xs)

dupNoDupInverse : HasDupValue x -> NoDupsButEmpty x -> Void
dupNoDupInverse (ThisDupValue prf notEmpty) (ThisEmpty induction) = notEmpty Refl
dupNoDupInverse (ThisDupValue prf notEmpty) (ThisValue contra induction) = contra prf
dupNoDupInverse (ThatDupValue induction) (ThisEmpty x) = dupNoDupInverse induction x
dupNoDupInverse (ThatDupValue induction) (ThisValue prf x) = dupNoDupInverse induction x

validInvalidRowsInverse : InvalidRows xs -> ValidRows xs -> Void
validInvalidRowsInverse (ThisRowInvalid prf) (ValidRow prf2 induction) = dupNoDupInverse prf prf2
validInvalidRowsInverse (ThisRowInvalid prf) (NotInvalidRow contra induction) = contra prf
validInvalidRowsInverse (ThatRowInvalid prf) (ValidRow x induction) = validInvalidRowsInverse prf induction
validInvalidRowsInverse (ThatRowInvalid prf) (NotInvalidRow contra induction) = validInvalidRowsInverse prf induction

data ValidCols : Vect n (Vect m a) -> Type where
  ColsValid : (prf : ValidRows (cols g)) -> ValidCols g

data ValidBoxs : Vect (n*n) (Vect (n*n) a) -> Type where
  BoxsValid : (prf : ValidRows (boxs g)) -> ValidBoxs g

data Valid : Grid n -> Type where
  IsValid : (rows : ValidRows g) -> (cols : ValidCols g) -> (boxs : ValidBoxs g) -> Valid (MkGrid g)

hasDupInvalid : (prf : HasDupValue x) -> ValidRows (x :: xs) -> Void
hasDupInvalid prf (NotInvalidRow contra x) = contra prf
hasDupInvalid prf (ValidRow contra x) = dupNoDupInverse prf contra

hasInvalidRow : (notValidXs : Not (ValidRows xs)) -> ValidRows (x :: xs) -> Void
hasInvalidRow notValidXs (NotInvalidRow contra x) = notValidXs x
hasInvalidRow notValidXs (ValidRow contra x) = notValidXs x

decValidRows : (g : Vect n (Vect m (Value k))) -> Dec (ValidRows g)
decValidRows [] {n=Z} = Yes $ ValidEmpty
decValidRows (x :: xs) {n=S k} = case decHasDupValue x of
                                      Yes prf => No (hasDupInvalid prf)
                                      No notValidX => case decValidRows xs of
                                                           Yes prf => Yes (NotInvalidRow notValidX prf)
                                                           No notValidXs => No ((hasInvalidRow notValidXs))

badRows : (contra : Not (ValidRows xs)) -> Valid (MkGrid xs) -> Void
badRows contra (IsValid rows cols boxs) = contra rows

badCols : (contra : Not (ValidRows (cols xs))) -> Valid (MkGrid xs) -> Void
badCols contra (IsValid rows (ColsValid cols) boxs) = contra cols

badBoxs : (contra : Not (ValidRows (boxs xs))) -> Valid (MkGrid xs) -> Void
badBoxs contra (IsValid rows cols (BoxsValid boxs)) = contra boxs

decValid : (g : Grid n) -> Dec (Valid g)
decValid (MkGrid xs) =
  case decValidRows xs of
       Yes rowPrf =>
         case decValidRows (cols xs) of
              Yes colPrf =>
                case decValidRows (boxs xs) of
                  Yes boxPrf =>
                    Yes (IsValid rowPrf (ColsValid colPrf) (BoxsValid boxPrf))
                  No contra => No (badBoxs contra)
              No contra => No (badCols contra)
       No contra => No (badRows contra)
