!----------------------------- MODULE Winter -----------------------------
EXTENDS Service, Sequences, FiniteSets, Naturals

CONSTANTS
    ProcSet,     \* Set of processes
    ClientSet,   \* Set of clients (for compacted dependencies)
    F            \* Number of tolerated Byzantine failures

VARIABLES
    announced,   \* [CmdSet -> [deps: [ClientSet -> Nat], fast: BOOLEAN]], stores discovered deps & fast-path flag
    mailbox,     \* [ProcSet -> Seq(Message)], local mailbox for each process
    faulty       \* SUBSET ProcSet

\* BQS instance for quorum logic, parameterized as in EPaxos.tla
BQS == INSTANCE BQS WITH ProcSet <- ProcSet, f <- F, faulty <- faulty

\* Wintermute DDS instance, parameterized with 'announced'
DDS == INSTANCE DDS WITH announced <- announced

\* Message structure
Message == [
    type : {"Announce", "Reply"},
    from : ProcSet,
    to   : ProcSet \cup {"all"},
    cmd  : CmdSet,
    deps : [ClientSet -> Nat],
    sn   : Nat
]

\* Helper: Has this process already announced this command?
HasAnnounced(p, c) ==
    \E i \in 1..Len(mailbox[p]):
        /\ mailbox[p][i].type = "Announce"
        /\ mailbox[p][i].cmd  = c
        /\ mailbox[p][i].from = p

\* Helper: Has this process already replied to (c, q)?
HasReplied(p, c, q) ==
    \E i \in 1..Len(mailbox[p]):
        /\ mailbox[p][i].type = "Reply"
        /\ mailbox[p][i].cmd  = c
        /\ mailbox[p][i].to   = q

Deps(p, c) == { d \in CmdSet : 
    /\ Conflicts(d, c) 
    /\ \E i \in 1..Len(mailbox[p]) :         
        /\ mailbox[p][i].type = "Announce"
        /\ mailbox[p][i].cmd = d
    }

\* Only one announce per process/command
Announce(p, c, sn) ==
    /\ ~HasAnnounced(p, c)
    /\ mailbox' = [mailbox EXCEPT ![p] = Append(@, [type |-> "Announce", from |-> p, to |-> "all", cmd |-> c, deps |-> [cl \in ClientSet |-> 0], sn |-> sn])]
    /\ UNCHANGED <<announced, faulty>>

\* Only one reply per process/command/requester
Reply(p, c, q, sn) ==
    /\ ~HasReplied(p, c, q)    
    /\ \E i \in 1..Len(mailbox[p]):
        /\ mailbox[p][i].type = "Announce"
        /\ mailbox[p][i].cmd  = c
        /\ mailbox[p][i].from = q
    /\ LET d == Deps(p, c) IN
       IN mailbox' = [mailbox EXCEPT ![p] = Append(@, [type |-> "Reply", from |-> p, to |-> q, cmd |-> c, deps |-> d, sn |-> sn])]
    /\ UNCHANGED <<announced, faulty>>

\* Is Q a valid Wintermute quorum?
IsQuorum(Q) == Q \in BQS!WQSQuorums

\* Returns the threshold union of dependency vectors over a quorum Q (appearing at least F+1 times)
ThresholdUnion(depvecs, Q) ==
    [cl \in ClientSet |->
        LET counts == [v \in Nat |-> Cardinality({j \in Q : depvecs[j][cl] = v})]
            maxval == Max({v \in Nat : counts[v] >= F+1})
        IN IF {v \in Nat : counts[v] >= F+1} # {} THEN maxval ELSE 0
    ]

\* Returns TRUE iff all dependency vectors in depvecs agree
AllIdentical(depvecs) ==
    LET vals == {depvecs[j] : j \in DOMAIN depvecs}
    IN Cardinality(vals) = 1

\* Collect dependencies from a quorum, perform threshold union, record fast-path if all replies are identical
CollectDeps(p, c, Q) ==
    /\ IsQuorum(Q)
    /\ \A j \in Q:
        \E i \in 1..Len(mailbox[j]):
            /\ mailbox[j][i].type = "Reply"
            /\ mailbox[j][i].cmd  = c
            /\ mailbox[j][i].to   = p
    /\ LET idxs    == [j \in Q |-> CHOOSE i \in 1..Len(mailbox[j]):
                                        /\ mailbox[j][i].type = "Reply"
                                        /\ mailbox[j][i].cmd  = c
                                        /\ mailbox[j][i].to   = p ]
           depvecs == [j \in Q |-> mailbox[j][idxs[j]].deps]
           thUnion == ThresholdUnion(depvecs, Q)
           fast    == AllIdentical(depvecs)
       IN
         /\ announced' = [announced EXCEPT ![c] = [deps |-> thUnion, fast |-> fast]]
         /\ UNCHANGED <<mailbox, faulty>>

Init ==
    /\ announced = [c \in CmdSet |-> [deps |-> [cl \in ClientSet |-> 0], fast |-> FALSE]]
    /\ mailbox   = [p \in ProcSet |-> <<>>]
    /\ faulty    = {}

Next ==
    \/ \E p \in ProcSet, c \in CmdSet, sn \in Nat: Announce(p, c, sn)
    \/ \E p, q \in ProcSet, c \in CmdSet, sn \in Nat: Reply(p, c, q, sn)
    \/ \E p \in ProcSet, c \in CmdSet, Q \in BQS!WQSQuorums: CollectDeps(p, c, Q)

INV ==
    DDS!INV

Spec ==
    Init /\ [][Next]_<<announced, mailbox, faulty>>

=============================================================================