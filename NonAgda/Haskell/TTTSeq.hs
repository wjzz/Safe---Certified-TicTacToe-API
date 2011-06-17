{-# OPTIONS -Wall #-}
{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Main where

import Data.Sequence hiding (filter)
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F
import Data.List

data Color = X | O
             deriving (Eq, Show)
                      
otherColor :: Color -> Color                      
otherColor X = O
otherColor O = X

data Move = P11 | P12 | P13 |
            P21 | P22 | P23 |
            P31 | P32 | P33
            deriving (Eq, Ord, Enum, Show)
                      
allMoves :: [Move]
allMoves = [P11 .. P33]

data Result = Draw | Win Color
              deriving (Show, Eq)

newtype Board = Board (Seq Move)

emptyBoard :: Board
emptyBoard = Board empty

addMove :: Board -> Move -> Board
addMove (Board ms) m = Board (ms |> m)

validMoves :: Board -> [Move]
validMoves (Board ms) = filter (`F.notElem` ms) allMoves

isEmptyField :: Board -> Move -> Bool
isEmptyField (Board ms) m = m `F.elem` ms

winningPositions :: [[Move]]
winningPositions = [[P11 , P12 , P13] ,
                    [P21 , P22 , P23] ,
                    [P31 , P32 , P33] ,
                    
                    [P11 , P21 , P31] ,
                    [P12 , P22 , P32] ,
                    [P13 , P23 , P33] ,
                    
                    [P11 , P22 , P33] ,
                    [P13 , P22 , P31] ]

movesByColor :: Board -> Color -> [Move]
movesByColor (Board ms) c = aux ms c

aux :: Seq Move -> Color -> [Move]
aux ms c = 
  case viewl ms of
    EmptyL   -> []
    a :< ms' -> case c of
                  X -> a : aux ms' O
                  O -> aux ms' X
      
hasWon :: [Move] -> Bool
hasWon ms = any (all (`elem` ms)) winningPositions

isFinished :: Board -> Maybe Result
isFinished b@(Board ms)
  | hasWon (movesByColor b X) = Just (Win X)
  | hasWon (movesByColor b O) = Just (Win O)                              
  | Seq.length ms == 9        = Just Draw                                           
  | otherwise                 = Nothing

gameResult :: Result
gameResult = bestResultByColor X emptyBoard

resultCmp :: Color -> Result -> Result -> Ordering
resultCmp X (Win X)  _      = GT
resultCmp X Draw    (Win X) = LT
resultCmp X Draw     Draw   = EQ
resultCmp X Draw    (Win O) = GT
resultCmp X (Win O)  _      = LT
resultCmp O m1 m2 = resultCmp X m2 m1

bestResultByColor :: Color -> Board -> Result
bestResultByColor c b = 
  case isFinished b of 
    Just (result) -> result
    Nothing -> 
      let
        moves  = validMoves b
      in
       case moves of
         [] -> error "Implementation error!"         
         _  -> maximumBy (resultCmp c) $ map (bestResultByColor (otherColor c) . addMove b) moves

main :: IO ()
main = print gameResult
