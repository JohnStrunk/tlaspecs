------------------------------ MODULE nQueens ------------------------------
(***************************************************************************)
(* This solves the N queens problem.                                       *)
(*                                                                         *)
(* The model parameter is the size of the chess board.                     *)
(*                                                                         *)
(* The queens are represented as a set of tuples, where each tuple is the  *)
(* x, y coordinate of a queen.  This gives the queens complete freedom to  *)
(* "move" around the board, with the exception that 2 may not occupy the   *)
(* same square.                                                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS size  \* The size of the chess board

VARIABLES Queens  \* The set of queens

abs(r) == IF r < 0 THEN -r ELSE r

RECURSIVE mod(_, _)
mod(a, b) == IF a > b THEN mod(a-b, b) ELSE a

(***************************************************************************)
(* This set of functions determine whether 2 queens can attack each other  *)
(* by determining if they are horizontally, vertically, or diagonally      *)
(* aligned.                                                                *)
(***************************************************************************)
Horizontal(p, q) == p[2] = q[2]

Vertical(p, q) == p[1] = q[1]

Diagonal(p, q) == abs(p[1] - q[1]) = abs(p[2] - q[2])

CanAttack(p, q) == \/ Horizontal(p, q)
                   \/ Vertical(p, q)
                   \/ Diagonal(p, q)

(***************************************************************************)
(* We start with all queens lined up vertically in the 1st column.         *)
(***************************************************************************)
Init == Queens = {1} \X (1..size)

(***************************************************************************)
(* The temporal part of the spec is how the queens move around the board.  *)
(* We allow 1 queen to move for each step, and that queen may move         *)
(* (increment, with wrap-around) either horizontally or vertically.  We    *)
(* must also insist that the cardinality of the set remains equal to the   *)
(* size of the board to prevent cases where 2 queens occupy the same       *)
(* square.                                                                 *)
(***************************************************************************)
MoveX(q) == << mod(q[1] + 1, size), q[2] >>
MoveY(q) == << q[1], mod(q[2] + 1, size) >>

NextX == \E q \in Queens : Queens' = (Queens \ {q}) \union {MoveX(q)}
NextY == \E q \in Queens : Queens' = (Queens \ {q}) \union {MoveY(q)}
Next == /\ \/ NextX
           \/ NextY
        /\ Cardinality(Queens') = size

(***************************************************************************)
(* We determine a solution to the problem by asserting (in the checker)    *)
(* that there are no positions of the queens where they are all "safe".    *)
(* Therefore, we use UnSolved as an invariant.                             *)
(***************************************************************************)
Safe(Q) ==  \A p, q \in Q : \/ p = q
                            \/ ~CanAttack(p, q)
UnSolved == ~Safe(Queens)

Spec == Init /\ [][Next]_<<Queens>>

=============================================================================
\* Modification History
\* Last modified Wed Feb 24 21:07:25 EST 2021 by jstrunk
\* Created Tue Feb 23 20:35:07 EST 2021 by jstrunk
