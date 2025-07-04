--------------------- MODULE LIN ---------------------

EXTENDS FiniteSets, SequencesExt, Service

CONSTANTS
    DEBUG,
    ProcSet,     
    f,           
    ClientSet

ASSUME /\ ProcSet /= {}
       /\ ClientSet /= {}

VARIABLES
    deps,
    client,     
    S,           
    L,           
    E,            
    Outbox,       
    Inflight,     
    Responses     

BLSMR == INSTANCE BLSMR 
         WITH ProcSet <- ProcSet, 
              deps <- deps

Vars ==  <<deps, client, S, L, E, Outbox, Inflight, Responses>>

\* ------------------------------
\* CLIENT ACTIONS (sequentiality enforced)
\* ------------------------------
ClientInvoke(c, cmdc) ==
    /\ c \in ClientSet /\ cmdc \in CmdSet
    /\ Responses[c][cmdc] = {}
    /\ Inflight[c] = Bot
    /\ client[cmdc] = c
    /\ Inflight' = [Inflight EXCEPT ![c] = cmdc]    
    /\ UNCHANGED <<deps, client, S, L, E, Outbox, Responses>>

ClientRespond(c, v) ==
    /\ c \in ClientSet
    /\ Inflight[c] # Bot
    /\  LET respSet == {r \in Responses[c][Inflight[c]] : r[2] = v}
        IN
            /\ Cardinality(respSet) >= f+1
            /\ Inflight' = [Inflight EXCEPT ![c] = Bot]
            /\ UNCHANGED <<deps, client, S, L, E, Outbox, Responses>>

ClientRecvResp(c, p, cmdc, v) ==
    /\ c \in ClientSet /\ p \in ProcSet /\ cmdc \in CmdSet /\ v \in ValSet
    /\ <<cmdc, v, c>> \in Outbox[p]
    /\ Responses' = [Responses EXCEPT ![c] = [@ EXCEPT ![cmdc] = @ \cup {<<p, v>>}]]
    /\ Outbox' = [Outbox EXCEPT ![p] = @ \ {<<cmdc, v, c>>}]
    /\ UNCHANGED <<deps, client, S, L, E, Inflight>>
 
\* ------------------------------
\* REPLICA ACTIONS
\* ------------------------------
RepInvoke(p, cmdc, c) ==
    /\ p \in ProcSet
    /\ cmdc \in CmdSet
    /\ c \in ClientSet
    /\ Inflight[c] = cmdc
    /\ BLSMR!Submit(p, cmdc)
    /\ UNCHANGED <<client, S, L, E, Outbox, Inflight, Responses>>

TopologicalSortCanonical(p, cmds) ==    
    LET
        DepsInBatch == [cmdd \in cmds |-> deps[p][cmdd] \cap cmds]
        RECURSIVE RecSort(_,_)
        RecSort(sorted, remaining) ==
            IF remaining = {} THEN sorted
            ELSE LET
                ready == {cmdc \in remaining : \A cmdd \in DepsInBatch[cmdc]: \E i \in 1..Len(sorted): cmdd = sorted[i]}
                next == IF ready = {} THEN 
                           CHOOSE cmdc \in remaining: \A cmdd \in remaining: cmdc # cmdd => CanonicalOrder[cmdc] < CanonicalOrder[cmdd]
                        ELSE 
                           CHOOSE cmdc \in ready: \A cmdd \in ready: cmdc # cmdd => CanonicalOrder[cmdc] < CanonicalOrder[cmdd]
                IN RecSort(Append(sorted, next), remaining \ {next})
    IN
        RecSort(<<>>, cmds)

RECURSIVE ApplySeq(_,_,_)
ApplySeq(state, cmds, acc) ==
    IF Len(cmds) = 0 THEN <<state, acc>>
    ELSE
        LET tr == Tau(state, cmds[1])
            newAcc == [acc EXCEPT ![cmds[1]] = tr[2]]
        IN ApplySeq(tr[1], Tail(cmds), newAcc)

Execute(p, cmdc) ==
    /\ p \in ProcSet 
    /\ cmdc \in CmdSet
    /\ BLSMR!StablePhase(p, cmdc)
    /\ cmdc \notin E[p]
    /\  LET
            beta == BLSMR!TC({cmdc}, p, cmdc)
            orderedBeta == TopologicalSortCanonical(p, beta \ { L[p][i] : i \in 1..Len(L[p]) })
            emptyMap == [d \in {orderedBeta[i] : i \in 1..Len(orderedBeta)} |-> CHOOSE v \in ValSet: TRUE]
            pair == ApplySeq(S[p], orderedBeta, emptyMap)
            newS == pair[1]
            outs == pair[2]
            newE == E[p] \cup beta
            newL == L[p] \o orderedBeta
            newOut == Outbox[p] \cup {<<orderedBeta[d], outs[orderedBeta[d]], client[orderedBeta[d]]>> : d \in 1..Len(orderedBeta)}
        IN
            /\ L' = [L EXCEPT ![p] = newL]
            /\ S' = [S EXCEPT ![p] = newS]
            /\ E' = [E EXCEPT ![p] = newE]
            /\ Outbox' = [Outbox EXCEPT ![p] = newOut]
            /\ UNCHANGED <<deps, client, Inflight, Responses>>

\* ------------------------------
\* SMR INVARIANTS from preliminaries.tex, "state-machine replication"
\* ------------------------------

\* 1. Validity: If a correct process executes a command, then it is a valid command.
Validity ==
    \A p \in ProcSet: \A i \in 1..Len(L[p]): L[p][i] \in CmdSet

\* 2. Integrity: Each process executes each command at most once.
Integrity ==
    \A p \in ProcSet: \A c \in CmdSet: Len(SelectSeq(L[p], LAMBDA x: x = c)) <= 1

\* 3. Consistency: Correct processes execute conflicting commands in the same order.
Position(c, seq) ==
  IF \E i \in 1..Len(seq) : seq[i] = c
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = c
    ELSE Len(seq) + 1

Precedes(c, d) ==
  \E p \in ProcSet :
    /\ Conflicts(c, d)
    /\ \E i \in 1..Len(L[p]) : L[p][i] = c
    /\ Position(c, L[p]) < Position(d, L[p])

PrecedesPairs ==
  { <<c, d>> \in CmdSet \X CmdSet : Precedes(c, d) }

RECURSIVE Reaches(_,_)
Reaches(c, d) ==
  \/ <<c, d>> \in PrecedesPairs
  \/ \E e \in CmdSet : <<c, e>> \in PrecedesPairs /\ Reaches(e, d)

NoPrecedesCycle ==
  \A c \in CmdSet : ~Reaches(c, c)

Consistency == NoPrecedesCycle

\* ------------------------------
\* INITIALIZATION & NEXT
\* ------------------------------
Init ==
    /\ BLSMR!Init
    /\ client = [cmd \in CmdSet |-> CHOOSE c \in ClientSet: TRUE]
    /\ S = [p \in ProcSet |-> InitState]
    /\ L = [p \in ProcSet |-> <<>>]
    /\ E = [p \in ProcSet |-> {}]
    /\ Outbox = [p \in ProcSet |-> {}]
    /\ Inflight = [c \in ClientSet |-> Bot]
    /\ Responses = [c \in ClientSet |-> [cmdc \in CmdSet |-> {}]]

Next ==
    \/ \E c \in ClientSet, cmdc \in CmdSet: 
        /\ ClientInvoke(c, cmdc) 
        /\ Print(<<"ClientInvoke", cmdc, c, Inflight[c], Inflight'[c] >> ,TRUE) 
    \/ \E c \in ClientSet, p \in ProcSet, cmdc \in CmdSet, v \in ValSet: 
        /\ ClientRecvResp(c, p, cmdc, v) 
        /\ DEBUG => Print(<<"ClientRecvResp", c, p >> ,TRUE)
    \/ \E c \in ClientSet, v \in ValSet: 
        /\ ClientRespond(c, v) 
        /\ Print(<<"ClientRespond", c, Inflight[c], v >> ,TRUE)
    \/ \E p \in ProcSet, cmdc \in CmdSet, c \in ClientSet: 
        /\ RepInvoke(p, cmdc, c) 
        /\ DEBUG => Print(<<"RepInvoke", cmdc, c, deps' >> ,TRUE)
    \/ \E p \in ProcSet, cmdc \in CmdSet: 
        /\ Execute(p, cmdc) 
        /\ DEBUG => Print(<<"Execute", p, cmdc, Outbox' >> ,TRUE)
    \/ (\E c \in ClientSet, p \in ProcSet, cmdc \in CmdSet, D \in SUBSET CmdSet: 
        /\ Inflight[c] = cmdc  \* a bit restrictive but otherwise Byz replicas can submit non-invoked commands
        /\ BLSMR!Commit(p, cmdc, D)
        /\ DEBUG => Print(<<"BLSMR!Commit", p, cmdc, D >> ,TRUE) 
        /\ UNCHANGED <<client, S, L, E, Outbox, Inflight, Responses>>)

Spec ==
    Init /\ [][Next]_Vars

\* The invariants from SMR in preliminaries.tex:
SMRInvariants ==
    Validity /\ Integrity /\ Consistency
 
=============================================================================