---------------------- MODULE BLSMR ----------------------

EXTENDS Service

CONSTANTS
    ProcSet          \* Set of processes

ASSUME ProcSet /= {}

VARIABLES
    deps               \* deps[p][c] = dependencies of command c at process p (set of cmds, {bot}, or {none})

Vars == << deps >>

\* ----- PHASES AS PREDICATES OVER deps -----

\* A command is in phase Start at p if it is not in deps[p].
StartPhase(p, c) == deps[p][c] = {None}

\* A command is in phase Pending when it was submitted locally.
PendingPhase(p, c) == deps[p][c] = {Bot}

\* A command is in phase Commit at p if it is in deps[p] and its mapping differs from Bot
CommitPhase(p, c) == ~StartPhase(p,c) /\ ~PendingPhase(p,c)

\* The transitive closure of deps at p starting from {c}.
step(S,p,c) == S \cup UNION { IF deps[p][c2] \subseteq CmdSet THEN deps[p][c2] ELSE {} : c2 \in S }
RECURSIVE TC(_,_,_)
TC(S,p,c) == IF S = step(S,p,c) THEN S ELSE TC(step(S,p,c),p,c)

\* A command is in phase Stable at p if it is committed and all its transitive dependencies are also committed (not ⊥).
StablePhase(p, c) ==
    /\ CommitPhase(p, c)
    /\ \A d \in TC({c},p, c): CommitPhase(p, d)

\* ----- STATE TRANSITIONS -----

\* A process can submit a command, initializing it as ⊥ if not present.
Submit(p, c) ==
    /\ p \in ProcSet
    /\ c \in CmdSet
    /\ StartPhase(p, c)
    /\ deps' = [deps EXCEPT ![p][c] = {Bot}]

isSafe(p, c, D) ==
    /\ c \notin D
    /\ \A q \in ProcSet: CommitPhase(q, c) => deps[q][c] = D
    /\ \A d \in CmdSet: (Conflicts(c,d) /\ \E q \in ProcSet: CommitPhase(q,d)) => d \in D

\* A process can commit a command with a dependency set D (can be from Start or after Submit).
Commit(p, c, D) ==
    /\ p \in ProcSet
    /\ c \in CmdSet
    /\ D \in SUBSET CmdSet 
    /\ ~ CommitPhase(p, c)
    /\ isSafe(p, c, D)
    /\ deps' = [deps EXCEPT ![p][c] = D]

Next ==
    \E p \in ProcSet, c \in CmdSet:
        (StartPhase(p, c) /\ Submit(p, c))
    \/ \E q \in ProcSet, d \in CmdSet, D \in SUBSET CmdSet:
        Commit(q, d, D)

Init ==
    /\ deps = [p \in ProcSet |-> [c \in CmdSet |-> {None}]]

Spec ==
    Init /\ [][Next]_Vars

\* ----- PROPERTIES -----

\* Validity: If p commits c, then c is a command, and all its dependencies are commands.
Validity ==
    \A p \in ProcSet: \A c \in CmdSet:
        CommitPhase(p, c) =>
            (\A d \in deps[p][c]: d \in CmdSet)

\* Agreement: For each c, there exists D such that, for all p, if c is committed at p then deps[p][c] = D.
Agreement ==
    \A c \in CmdSet:
        \E D \in SUBSET CmdSet:
            \A p \in ProcSet: StablePhase(p, c) => (deps[p][c] = D)

\* Consistency: If p commits c with D and q commits d with D', and c, d conflict, then d ∈ D or c ∈ D'.
Consistency ==
    \A p, q \in ProcSet:
      \A c, d \in CmdSet:
        (Conflicts(c, d) /\ CommitPhase(p, c) /\ CommitPhase(q, d)) =>
            (d \in deps[p][c] \/ c \in deps[q][d])

Inv ==
    Validity /\ Agreement /\ Consistency

\* Liveness: If a command is committed at some process, it is eventually committed at all.
Liveness ==
    \A c \in CmdSet:
      \A p \in ProcSet:
        (CommitPhase(p, c)) => \A q \in ProcSet: <>(CommitPhase(q, c))
================================================================================
