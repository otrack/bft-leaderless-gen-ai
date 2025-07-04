---- MODULE Service ----

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    CmdSet,        \* Set of commands
    ValSet,        \* Set of possible output values
    InitState      \* Initial state (natural number)

\* CanonicalOrder: [CmdSet -> Int], commands are sorted by their natural value
RECURSIVE CanonicalOrder
CanonicalOrder == [c \in CmdSet |-> CHOOSE i \in 1..Cardinality(CmdSet): \A d \in CmdSet \ {c}: i # CanonicalOrder[d]]

\* not commands
Bot == "⊥"
None == "None"

ASSUME Bot \notin CmdSet /\ None \notin CmdSet 

\* Tau: [Nat × CmdSet -> Nat × ValSet], deterministic transition
Tau(s, c) == 
           IF c = "A"
               THEN <<s + 1, "OK">>
           ELSE IF c = "B"
               THEN <<s * 2, "OK">>
           ELSE <<s, "OK">>

Conflicts(c, d) == c # d /\ {c, d} \cap {"A", "B"} # {}
====