----------------------------- MODULE nQueensOpt -----------------------------
(***************************************************************************)
(* This is a refinement of the general N queens problem to reduce the      *)
(* state space so that we can solve on larger boards.                      *)
(*                                                                         *)
(* Here, we use the optimization that (1) no 2 queens may occupy the same  *)
(* column, so we use a sequence with 1 entry per column to represent the   *)
(* positions.  And (2) we know that queens may not occupy the same row, so *)
(* we initialize the positions to be different rows.  Steps are then       *)
(* position "swaps" within the sequence.                                   *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS size  \* The size of the chess board

VARIABLES Queens  \* The tuple (sequence) of queens

abs(r) == IF r < 0 THEN -r ELSE r

(***************************************************************************)
(* This creates a sequence of consecutive integers from n to m inclusive   *)
(*                                                                         *)
(* SeqTo(3, 5) == << 3, 4, 5 >>                                            *)
(***************************************************************************)
RECURSIVE SeqTo(_, _)
SeqTo(n, m) == IF n <= m THEN << n >> \o SeqTo(n+1, m) ELSE << >>

Init == Queens = SeqTo(1, size)

Next == \E n, m \in (1..size) : Queens' = [ Queens EXCEPT ![n]=Queens[m], ![m]=Queens[n] ] 

(***************************************************************************)
(* Defining "safe" is simplified since we only need to check for diagonal. *)
(* Horizontal and vertical are disallowed by our definition of the state   *)
(* space and transitions.                                                  *)
(***************************************************************************)
Safe(Q) ==  \A p, q \in (1..size) : \/ p = q
                                    \/ abs(p - q) /= abs(Q[p] - Q[q]) \* not diagonal
Unsolved == ~Safe(Queens)

Spec == Init /\ [][Next]_<<Queens>>

=============================================================================
\* Modification History
\* Last modified Wed Feb 24 21:15:16 EST 2021 by jstrunk
\* Created Wed Feb 24 20:21:47 EST 2021 by jstrunk
