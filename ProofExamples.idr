module ProofExamples

import Data.Vect
import Grid
import Valid
import Solved
import Sudoku

%default total
%access public export

findInvalidPrf : {auto contra : Not (Valid g)} -> Not (Valid g)
findInvalidPrf {contra} = contra

findValidPrf : {auto prf : Valid g} -> Valid g
findValidPrf {prf} = prf

exampleValidGrid : Grid 4
exampleValidGrid = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Empty, Empty],
                          [Filled 0, Empty, Empty, Filled 3],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Empty, Empty, Filled 2]]

  {-
validPrf : ()
validPrf = findValidPrf exampleValidGrid {prf=?a}
  -}

blankPrf : Valid (blank 2)
blankPrf = findValidPrf

exampleInvalidGrid : Grid 4
exampleInvalidGrid = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Filled 1, Empty],
                          [Filled 1, Empty, Empty, Filled 3],
                          [Filled 1, Empty, Filled 2, Empty],
                          [Empty, Empty, Empty, Filled 2]]

invalidPrf : Not (Valid ProofExamples.exampleInvalidGrid)
invalidPrf = badRows $ hasDupInvalid (ThatDupValue (ThisDupValue Here uninhabited))

exampleSolved : Grid 1
exampleSolved = MkGrid $ the (Vect (1*1) $ Vect (1*1) (Value (1*1))) $
                         [[Filled 0]]

validSolved : Valid (ProofExamples.exampleSolved)
validSolved = IsValid (ValidRow (ThisValue uninhabited EmptyList) ValidEmpty)
        (ColsValid (ValidRow (ThisValue uninhabited EmptyList)
                             ValidEmpty))
        (BoxsValid (ValidRow (ThisValue uninhabited EmptyList)
                             ValidEmpty))

solvedPrf : Solved ProofExamples.exampleSolved {valid=ProofExamples.validSolved}
solvedPrf = IsSolved Refl

exampleNotSolved : Grid 1
exampleNotSolved = MkGrid $ the (Vect (1*1) $ Vect (1*1) (Value (1*1))) $
                         [[Empty]]

notSolvedPrf : Solved ProofExamples.exampleNotSolved -> Void
notSolvedPrf (IsSolved Refl) impossible
