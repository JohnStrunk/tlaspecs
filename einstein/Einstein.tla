------------------------------ MODULE Einstein ------------------------------

(***************************************************************************)
(* Einstein's riddle                                                       *)
(*                                                                         *)
(* The situation:                                                          *)
(* * There are 5 houses in five different colors.                          *)
(* * In each house lives a person with a different nationality.            *)
(* * These five owners drink a certain type of beverage, smoke a certain   *)
(*   brand of cigar and keep a certain pet.                                *)
(* * No owners have the same pet, smoke the same brand of cigar or drink   *)
(*   the same beverage.                                                    *)
(*                                                                         *)
(* The question is: Who owns the fish?                                     *)
(*                                                                         *)
(* Hints:                                                                  *)
(* * the Brit lives in the red house                                       *)
(* * the Swede keeps dogs as pets                                          *)
(* * the Dane drinks tea                                                   *)
(* * the green house is on the left of the white house                     *)
(* * the green house's owner drinks coffee                                 *)
(* * the person who smokes Pall Mall rears birds                           *)
(* * the owner of the yellow house smokes Dunhill                          *)
(* * the man living in the center house drinks milk                        *)
(* * the Norwegian lives in the first house                                *)
(* * the man who smokes blends lives next to the one who keeps cats        *)
(* * the man who keeps horses lives next to the man who smokes Dunhill     *)
(* * the owner who smokes BlueMaster drinks beer                           *)
(* * the German smokes Prince                                              *)
(* * the Norwegian lives next to the blue house                            *)
(* * the man who smokes blend has a neighbor who drinks water              *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

(***************************************************************************)
(* Define the possible values for each of the categories                   *)
(***************************************************************************)
Colors == { "red", "white", "green", "yellow", "blue" }
Nationalities == { "Brit", "Swede", "Dane", "Norwegian", "German" }
Beverages == { "tea", "coffee", "milk", "beer", "water" }
Cigars == { "PallMall", "Dunhill", "blends", "BlueMaster", "Prince" }
Pets == { "dog", "birds", "cats", "horses", "fish" }
Houses == 1..Cardinality(Colors)

(***************************************************************************)
(* The answer will be sequences of each of the categories.  The owner of   *)
(* the fish will be Nationality[i] where Pet[i]="fish".                    *)
(***************************************************************************)

(***************************************************************************)
(* All the permutations of a given set (as a set of sequences)             *)
(***************************************************************************)
Perm(set) == {s \in [1..Cardinality(set) -> set] : \A x, y \in 1..Cardinality(set) : s[x] # s[y] \/ x = y}

(***************************************************************************)
(* Define the "universe" of possible configurations.                       *)
(*                                                                         *)
(* Note: each of the record fields could be defined as "pet: Perm(Pets)",  *)
(* but this produces a state space that is too big for the model checker.  *)
(* The filtering in the definition is done by applying some simple logic   *)
(* based on the "hints" to trim the universe down to something that can be *)
(* solved in a few minutes.                                                *)
(***************************************************************************)
Universe == [
    color: { P \in Perm(Colors) :
                /\ \E a, b \in Houses : 
                    /\ a = b - 1
                    /\ P[a] = "green"
                    /\ P[b] = "white"
                /\ P[2] = "blue"
                /\ P[3] # "green"
    },
    nationality: { P \in Perm(Nationalities) :
                      /\ P[1] = "Norwegian" 
                      /\ P[3] # "Dane"
    },
    beverage: { P \in Perm(Beverages) : P[3] = "milk" },
    cigar: { P \in Perm(Cigars) :
                /\ P[3] # "BlueMaster"
    },
    pet: Perm(Pets)
]

Answer == CHOOSE ans \in Universe :
    \* the Brit lives in the red house
    /\ \E h \in Houses: /\ ans.nationality[h] = "Brit"
                        /\ ans.color[h] = "red"
    \* the Swede keeps dogs as pets
    /\ \E h \in Houses: /\ ans.nationality[h] = "Swede"
                        /\ ans.pet[h] = "dog"
    \* the Dane drinks tea
    /\ \E h \in Houses: /\ ans.nationality[h] = "Dane"
                        /\ ans.beverage[h] = "tea"
    \* the green house is on the left of the white house (opt)
    /\ \E g, w \in Houses: /\ ans.color[g] = "green"
                           /\ ans.color[w] = "white"
                           /\ g = w - 1
    \* the green house's owner drinks coffee
    /\ \E h \in Houses: /\ ans.color[h] = "green"
                        /\ ans.beverage[h] = "coffee"
    \* the person who smokes Pall Mall rears birds
    /\ \E h \in Houses: /\ ans.cigar[h] = "PallMall"
                        /\ ans.pet[h] = "birds"
    \* the owner of the yellow house smokes Dunhill
    /\ \E h \in Houses: /\ ans.color[h] = "yellow"
                        /\ ans.cigar[h] = "Dunhill"
    \* the man living in the center house drinks milk (opt)
    /\ ans.beverage[3] = "milk"
    \* the Norwegian lives in the first house (opt)
    /\ ans.nationality[1] = "Norwegian"
    \* the man who smokes blends lives next to the one who keeps cats
    /\ \E b, c \in Houses: /\ ans.cigar[b] = "blends"
                           /\ ans.pet[c] = "cats"
                           /\ \/ b = c - 1
                              \/ b = c + 1
    \* the man who keeps horses lives next to the man who smokes Dunhill
    /\ \E h, d \in Houses: /\ ans.pet[h] = "horses"
                           /\ ans.cigar[d] = "Dunhill"
                           /\ \/ h = d - 1
                              \/ h = d + 1
    \* the owner who smokes BlueMaster drinks beer
    /\ \E h \in Houses: /\ ans.beverage[h] = "beer"
                        /\ ans.cigar[h] = "BlueMaster"
    \* the German smokes Prince
    /\ \E h \in Houses: /\ ans.nationality[h] = "German"
                        /\ ans.cigar[h] = "Prince"
    \* the Norwegian lives next to the blue house (opt)
    /\ \E n, b \in Houses: /\ ans.nationality[n] = "Norwegian"
                           /\ ans.color[b] = "blue"
                           /\ \/ n = b - 1
                              \/ n = b + 1
    \* the man who smokes blend has a neighbor who drinks water
    /\ \E b, w \in Houses: /\ ans.cigar[b] = "blends"
                           /\ ans.beverage[w] = "water"
                           /\ \/ b = w - 1
                              \/ b = w + 1
FishOwner == LET h == CHOOSE h \in Houses: Answer.pet[h] = "fish"
             IN Answer.nationality[h]

=============================================================================
\* Modification History
\* Last modified Wed Mar 02 10:34:01 EST 2022 by jstrunk
\* Created Wed Mar 10 20:17:57 EST 2021 by jstrunk
