--------------------- MODULE VectorConsensus ---------------------
EXTENDS Service

CONSTANT
    Parameters,
    Inputs

VARIABLES
    decided,
    proposed

Init ==
    /\ decided = [x \in Parameters |-> {}]
    /\ proposed = [x \in Parameters |-> {}]

Propose(x, y) ==
    /\ x \in Parameters
    /\ y \in Inputs
    /\ proposed' = [proposed EXCEPT ![x] = proposed[x] \union {y}]
    /\ IF decided[x] = {}
         THEN decided' = [decided EXCEPT ![x] = {y}]
         ELSE UNCHANGED decided         

Decision(x) == CHOOSE y \in Inputs: y \in decided'[x]

Next ==
    \E x \in Parameters, y \in Inputs: Propose(x,y)

Validity ==
    \A x \in Parameters: decided[x] # {} => \A y \in decided[x]: y \in proposed[x]

Agreement ==
    \A x \in Parameters: Cardinality(decided[x]) \leq 1

Spec ==
    Init /\ [][Next]_<<decided, proposed>>

=============================================================================
