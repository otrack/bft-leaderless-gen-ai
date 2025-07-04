----------------------------- MODULE EPaxos -----------------------------
EXTENDS Service

CONSTANTS
    ProcSet,
    f

VARIABLES
    announced,
    mailbox,
    faulty

BQS == INSTANCE BQS WITH ProcSet <- ProcSet, f <- f, faulty <- faulty

DDS == INSTANCE DDS WITH announced <- announced

Message == [type : {"Announce", "Reply"}, from : ProcSet, to : ProcSet \cup {"all"}, cmd : CmdSet, deps : SUBSET CmdSet]

IsQuorum(Q) == Q \in BQS!DQSQuorums

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

Announce(p, c) ==
    /\ ~HasAnnounced(p, c)
    /\ mailbox' = [mailbox EXCEPT ![p] = Append(@, [type |-> "Announce", from |-> p, to |-> "all", cmd |-> c, deps |-> {}])]
    /\ UNCHANGED <<announced, faulty>>

Reply(p, c, q) ==
    /\ ~HasReplied(p, c, q)
    /\ \E i \in 1..Len(mailbox[p]):
        /\ mailbox[p][i].type = "Announce"
        /\ mailbox[p][i].cmd = c
        /\ mailbox[p][i].from = q
    /\ LET d == Deps(p, c) IN
        mailbox' = [mailbox EXCEPT ![p] = Append(@, [type |-> "Reply", from |-> p, to |-> q, cmd |-> c, deps |-> d])]
    /\ UNCHANGED <<announced, faulty>>

CollectDeps(p, c, Q) ==
    /\ IsQuorum(Q)
    /\ \A j \in Q:
        \E i \in 1..Len(mailbox[j]):
            /\ mailbox[j][i].type = "Reply"
            /\ mailbox[j][i].cmd = c
            /\ mailbox[j][i].to = p
    /\ LET idxs == [j \in Q |-> CHOOSE i \in 1..Len(mailbox[j]):
                                    /\ mailbox[j][i].type = "Reply"
                                    /\ mailbox[j][i].cmd = c
                                    /\ mailbox[j][i].to = p ]
           D == UNION { mailbox[j][idxs[j]].deps : j \in Q }           
       IN /\ announced' = [announced EXCEPT ![c] = [deps |-> D, fast |-> FALSE]]
          /\ UNCHANGED <<mailbox, faulty>>

Init ==
    /\ BQS!Init
    /\ DDS!Init
    /\ mailbox = [p \in ProcSet |-> <<>>]

Next ==
    \/ \E p \in ProcSet, c \in CmdSet: Announce(p, c)
    \/ \E p, q \in ProcSet, c \in CmdSet: Reply(p, c, q)
    \/ \E p \in ProcSet, c \in CmdSet, Q \in BQS!DQSQuorums: CollectDeps(p, c, Q)

INV == DDS!INV

Liveness ==
    \A c \in CmdSet : <> DDS!isAnnounced(c)

Spec ==
  /\ Init
  /\ [][Next]_<<announced, mailbox, faulty>>
  /\ \A p \in ProcSet:
       \A c \in CmdSet:
         WF_<<announced, mailbox, faulty>>(Announce(p, c))
  /\ \A p \in ProcSet:
       \A c \in CmdSet:
         \A q \in ProcSet:
           WF_<<announced, mailbox, faulty>>(Reply(p, c, q))
  /\ \A p \in ProcSet:
       \A c \in CmdSet:
         \A Q \in BQS!DQSQuorums:
           WF_<<announced, mailbox, faulty>>(CollectDeps(p, c, Q))
=============================================================================