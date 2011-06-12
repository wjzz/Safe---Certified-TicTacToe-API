datatype color = X | O

fun otherColor X = O
|   otherColor O = X

datatype move = P11 | P12 | P13
              | P21 | P22 | P23
              | P31 | P32 | P33

val allmoves = [P11 , P12, P13 , P21, P22, P23, P31, P32, P33]

val emptyBoard = []

fun addMove b m = m :: b

datatype result = Draw | Win of color

fun member a ls = List.exists (fn a2 => a = a2) ls

val winningPositions = [[P11 , P12 , P13] ,
                        [P21 , P22 , P23] ,
                        [P31 , P32 , P33] ,
                        
                        [P11 , P21 , P31] ,
                        [P12 , P22 , P32] ,
                        [P13 , P23 , P33] ,
                    
                        [P11 , P22 , P33] ,
                        [P13 , P22 , P31] ]

fun aux _ [] = []
|   aux X (h :: t) = h :: aux O t
|   aux O (h :: t) = aux X t

fun movesByColor c b = aux c (List.rev b)

fun wonC c b = List.exists (List.all (fn winPosMove => member winPosMove (movesByColor c b))) 
                           winningPositions
fun getResult b = 
    if wonC X b then
        SOME (Win X)
    else if wonC O b then
            SOME (Win O)
    else if length b = 9 then
        SOME Draw
    else
        NONE

fun validMoves b = List.filter (fn move => not (member move b))
                               allmoves
fun maxX (Win X) _ = Win X
|   maxX Draw (Win X) = Win X
|   maxX Draw Draw = Draw
|   maxX Draw (Win O) = Draw
|   maxX (Win O) r = r

fun maxO (Win O) _ = Win O
|   maxO Draw (Win O) = Win O
|   maxO Draw Draw = Draw
|   maxO Draw (Win X) = Draw
|   maxO (Win X) r = r

fun maxByColor O = maxO
|   maxByColor X = maxX

exception ImplementionError

fun maximumByColor c [] = raise ImplementionError
  | maximumByColor c (h :: []) = h
  | maximumByColor c (h :: hs) = maxByColor c h (maximumByColor c hs)                                 

val count = ref 0

fun bestResultByColor c b = 
    case getResult b of
        SOME res => (count := 1 + !count ; res) |
        NONE => 
          let 
              val moves = validMoves b 
          in 
              case moves of
                  [] => raise ImplementionError |
                  _  => maximumByColor c (List.map (bestResultByColor (otherColor c) o addMove b) moves)
          end

fun gameResult () = bestResultByColor X emptyBoard

fun showResult  Draw   = "Draw"
  | showResult (Win X) = "Win X"
  | showResult (Win O) = "Win O"                       

val () = print (showResult (gameResult ()) ^  "\n")
val () = print (Int.toString (!count) ^  "\n")

        
(* What if we try to construct the game tree? *)

datatype gameTree = Leaf of result | Node of gameTree list

fun generateTree b = 
    case getResult b of
        SOME res => Leaf res |
        NONE => 
        let 
            val moves = validMoves b
        in
            case moves of 
                [] => raise ImplementionError |
                _ => Node (List.map (generateTree o addMove b) moves)
        end

fun fullTree () = generateTree emptyBoard

fun noOfNodes (Leaf _)  = 1
  | noOfNodes (Node ls) = List.foldl (fn (a,b) => a + b) 0 (List.map noOfNodes ls)

val () = print (Int.toString (noOfNodes (fullTree ())) ^ "\n")
