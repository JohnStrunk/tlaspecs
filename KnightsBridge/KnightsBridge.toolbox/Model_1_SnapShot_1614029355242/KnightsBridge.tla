--------------------------- MODULE KnightsBridge ---------------------------
(***************************************************************************)
(* Four knights must cross a norrow bridge...                              *)
(*                                                                         *)
(* It is night, and they will need the light from Archibald's torch to     *)
(* cross.  Sadly, the bridge will hold only two knights at a time, and the *)
(* torch will only burn for another fifteen minutes.  Now, Archibald is    *)
(* quick and nimble, he can make it in just one minute.  Baldur is strong  *)
(* and can make it in two minutes.  Now Charleston is old and will need    *)
(* five minutes to cross.  And lastly David is trimit and frail, he will   *)
(* need eight minutes to make the trip.                                    *)
(*                                                                         *)
(* Can all four knights cross the bridge before the torch burns out?       *)
(*                                                                         *)
(* https://twitter.com/MCLMouritzen/status/1362929925083308032             *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

VARIABLES Knights,     \* The set of knights
          TorchSide,   \* The side of the river the torch is on
          ElapsedTime  \* The amount of time that has passed


(***************************************************************************)
(* The sides of the river.                                                 *)
(*                                                                         *)
(* This is used for type checking (TypeOk)                                 *)
(***************************************************************************)
Side == {"Near", "Far"}

(***************************************************************************)
(* Max(S) returns the maximum element in a set (of numbers)                *)
(***************************************************************************)
Max(S) == CHOOSE m \in S : (\A n \in S: m \geq n) 



(***************************************************************************)
(* The type invariant for this specification.                              *)
(***************************************************************************)
TypeOk == /\ \A k \in Knights: k.side \in Side  \* Every knight must be on a side
          /\ TorchSide \in Side                 \* The torch must be on a side
          /\ ElapsedTime \in Nat



(***************************************************************************)
(* The starting configuration:                                             *)
(* - All knights start on the Near side                                    *)
(* - Each knight takes a certain amount of time to cross (constant)        *)
(* - The torch starts on the Near side                                     *)
(* - Time starts at zero                                                   *)
(***************************************************************************)
Init == /\ Knights = {
               [side |-> "Near", time |-> 1],  \* Archibald
               [side |-> "Near", time |-> 2],  \* Baldur
               [side |-> "Near", time |-> 5],  \* Charleston
               [side |-> "Near", time |-> 8]   \* David
           }
        /\ TorchSide = "Near"  \* Torch starts on the Near side
        /\ ElapsedTime = 0     \* Time starts from zero



(***************************************************************************)
(* The allowed steps are to move one or two (max the bridge will hold)     *)
(* knights, with the torch from one side to the other.                     *)
(*                                                                         *)
(* For a step to be valid, the torch must be on the starting side, and     *)
(* there must be one or more knights also on that side.                    *)
(*                                                                         *)
(* The time that elapses for the crossing is the time it takes the slowest *)
(* knight to cross.                                                        *)
(***************************************************************************)
NearToFar == /\ TorchSide = "Near"
             /\ \E travelers \in SUBSET Knights:
                 /\ Cardinality(travelers) = 1 \/ Cardinality(travelers) = 2
                 /\ \A k \in travelers: k.side = "Near"
                 /\ Knights' = { IF k \in travelers
                                 THEN [ k EXCEPT !.side = "Far" ]
                                 ELSE k
                                 : k \in Knights}
                 /\ ElapsedTime' = ElapsedTime + Max({k.time: k \in travelers})
             /\ TorchSide' = "Far"

FarToNear == /\ TorchSide = "Far"
             /\ \E travelers \in SUBSET Knights:
                 /\ Cardinality(travelers) = 1 \/ Cardinality(travelers) = 2
                 /\ \A k \in travelers: k.side = "Far"
                 /\ Knights' = { IF k \in travelers
                                 THEN [ k EXCEPT !.side = "Near" ]
                                 ELSE k
                                 : k \in Knights}
                 /\ ElapsedTime' = ElapsedTime + Max({k.time: k \in travelers})
             /\ TorchSide' = "Near"

Next == \/ NearToFar
        \/ FarToNear
        
Spec == Init /\ [][Next]_<<Knights, TorchSide, ElapsedTime>>


-----------------------------------------------------------------------------


(***************************************************************************)
(* The riddle is solved by having all knights on the far side of the river *)
(* within the 15 minutes that the torch has left.                          *)
(*                                                                         *)
(* By specifying AllAcross = FALSE as invariant, the model checker will    *)
(* alert us to any execution traces that result in a solution.             *)
(***************************************************************************)
AllAcross == /\ \A k \in Knights: k.side = "Far"
             /\ ElapsedTime <= 15

=============================================================================
\* Modification History
\* Last modified Sun Feb 21 21:57:08 EST 2021 by johns
\* Created Sat Feb 20 19:50:27 EST 2021 by johns
