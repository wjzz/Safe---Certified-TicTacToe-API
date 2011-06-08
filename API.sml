
signature BOARD =
    sig
        type board
        val empty : board
        val is_empty : board -> bool
    end

structure Board :> BOARD =
struct
  type board = int list
  val empty = []
  fun is_empty [] = true
    | is_empty (_ :: _) = false
end

fun tail (a :: _) = a
