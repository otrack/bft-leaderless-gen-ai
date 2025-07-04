---- MODULE DDS ----
EXTENDS Service

VARIABLES
  announced          \* [CmdSet -> [deps: SUBSET CmdSet, fast: BOOLEAN]]: output per command

Init ==
  /\ announced = [c \in CmdSet |-> [deps |-> {"None"}, fast |-> FALSE]]

isAnnounced(c) == announced[c].deps # {"None"}

\* Helper: set of conflicting, already announced commands
Deps(c) ==
  {d \in CmdSet : d # c /\ Conflicts(c, d) /\ isAnnounced(d)}

Announce(c) ==
  LET
    possibleDeps == Deps(c)
  IN
    \E D \in SUBSET possibleDeps, b \in BOOLEAN:
      /\ \A cp \in CmdSet:
            (cp # c /\ Conflicts(c, cp) /\ isAnnounced(cp)) => (c \in announced[cp].deps \/ cp \in D)
      /\ announced' = [announced EXCEPT ![c] = [deps |-> D, fast |-> b]]

Next ==
  \E c \in CmdSet: ~isAnnounced(c) /\ Announce(c)

\* State Invariants

\* Validity: Dependencies must be commands
Validity ==
  \A c \in CmdSet:
    isAnnounced(c) =>
      \A d \in announced[c].deps:
        d \in CmdSet

\* Visibility: For all c, cp \in CmdSet, if both are announced and they conflict, then c \in announced[cp].deps or cp \in announced[c].deps
Visibility ==
  \A c, cp \in CmdSet:
    (isAnnounced(c) /\ isAnnounced(cp) /\ Conflicts(c, cp)) =>
      (c \in announced[cp].deps \/ cp \in announced[c].deps)

\* Weak Agreement: If fast = TRUE for c, then announced[c].deps is a subset of possible dependencies
WeakAgreement ==
  \A c \in CmdSet:
    announced[c].fast = TRUE => announced[c].deps \subseteq Deps(c)

Liveness ==
    \A c \in CmdSet : <> isAnnounced(c)

INV == Validity /\ Visibility /\ WeakAgreement

Spec ==
  Init /\ [][Next]_<<announced>> /\ WF_<<announced>>(Next)

\* End of module
================================================================