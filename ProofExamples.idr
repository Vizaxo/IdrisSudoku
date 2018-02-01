module ProofExamples

import Data.Vect
import Grid
import Valid
import Solved
import Sudoku

%default total
%access public export

exampleValidGrid : Grid 4
exampleValidGrid = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Empty, Empty],
                          [Filled 0, Empty, Empty, Filled 3],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Empty, Empty, Filled 2]]

validPrf : Valid ProofExamples.exampleValidGrid
validPrf = IsValid Refl

exampleInvalidGrid : Grid 4
exampleInvalidGrid = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Empty, Empty],
                          [Filled 1, Empty, Empty, Filled 3],
                          [Filled 1, Empty, Empty, Empty],
                          [Empty, Empty, Empty, Filled 2]]

invalidPrf : (contra : Valid ProofExamples.exampleInvalidGrid) -> Void
invalidPrf (IsValid Refl) impossible


exampleSolved : Grid 1
exampleSolved = MkGrid $ the (Vect (1*1) $ Vect (1*1) (Value (1*1))) $
                         [[Filled 0]]

solvedPrf : Solved ProofExamples.exampleSolved
solvedPrf = IsSolved Refl

exampleNotSolved : Grid 1
exampleNotSolved = MkGrid $ the (Vect (1*1) $ Vect (1*1) (Value (1*1))) $
                         [[Empty]]

notSolvedPrf : Solved ProofExamples.exampleNotSolved -> Void
notSolvedPrf (IsSolved Refl) impossible

singleEmpty : Grid 4
singleEmpty = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Filled 2, Filled 3],
                          [Filled 2, Filled 3, Filled 0, Filled 1],
                          [Filled 1, Filled 2, Filled 3, Filled 0],
                          [Filled 3, Filled 0, Filled 1, Filled 2]]

notSolvedSingleEmptyPrf : Solved ProofExamples.singleEmpty -> Void
notSolvedSingleEmptyPrf (IsSolved Refl) impossible

solvedSingleEmptyPrf : NonEmpty (solveSudoku ProofExamples.singleEmpty)
solvedSingleEmptyPrf = IsNonEmpty


almostSolved : Grid 4
almostSolved = MkGrid $ the (Vect (2*2) $ Vect (2*2) (Value (2*2))) $
                         [[Empty, Filled 1, Filled 2, Filled 3],
                          [Filled 2, Empty, Filled 0, Filled 1],
                          [Filled 1, Empty, Filled 3, Empty],
                          [Filled 3, Filled 0, Filled 1, Filled 2]]
