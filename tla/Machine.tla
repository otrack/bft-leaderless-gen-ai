---- MODULE Machine ----
EXTENDS Service

CONSTANTS
  DEBUG,
  ProcSet      

VARIABLES
  ConsensusProposed,
  ConsensusDecided,
  DDSOutput,
  fd,          
  deps,        
  msgs          

DDS == INSTANCE DDS 
       WITH CmdSet <- CmdSet, 
            Output <-DDSOutput

Consensus == INSTANCE VectorConsensus 
             WITH Parameters <-CmdSet, 
                  Inputs <- SUBSET CmdSet,
                  proposed <- ConsensusProposed,
                  decided <- ConsensusDecided

BLSMR == INSTANCE BLSMR
         WITH ProcSet <- ProcSet,
              deps <- deps

Coord(cmd) == CHOOSE p \in ProcSet: TRUE

Submit(p, c) ==
  /\ (p = Coord(c) \/ (\E d \in CmdSet: c \in deps[p][d] /\ Coord(c) \in fd[p]))
  /\ BLSMR!StartPhase(p,c)
  /\ DDS!Announce(c)
  /\ LET out == DDSOutput'[c] IN
      IF ~out.fast 
      THEN /\ Consensus!Propose(c ,out.deps) 
           /\ msgs' = msgs \cup {<<c, Consensus!Decision(c), out.fast, p, ProcSet>>}                           
      ELSE 
           /\ msgs' = msgs \cup {<<c, out.deps, out.fast, p, ProcSet>>}
           /\ UNCHANGED <<ConsensusProposed, ConsensusDecided>>
  /\ deps' = [deps EXCEPT ![p][c] = {Bot}]
  /\ UNCHANGED <<fd>>

Commit(p, c, D) ==
  /\ p \in ProcSet
  /\ c \in CmdSet
  /\ D \in SUBSET CmdSet
  /\ ~ BLSMR!CommitPhase(p,c)     
  /\ \E sender \in ProcSet, b \in BOOLEAN, P \in SUBSET ProcSet: <<c, D, b, sender, P>> \in msgs /\ p \in P
  /\ deps' = [deps EXCEPT ![p][c] = D]
  /\ UNCHANGED <<DDSOutput, ConsensusProposed, ConsensusDecided, fd, msgs>>

Next ==
  \E p \in ProcSet:
    \E c \in CmdSet:
      \E D \in SUBSET CmdSet:
        \/ /\ Submit(p, c) 
           /\ DEBUG => Print(<<"Submit", p, c >> ,TRUE)
        \/ /\ Commit(p, c, D)
           /\ DEBUG => Print(<<"Commit", p, c, D, deps' >> ,TRUE)

Init ==
  /\ DDS!Init
  /\ Consensus!Init
  /\ fd = [p \in ProcSet |-> {}]
  /\ deps = [p \in ProcSet |-> [c \in CmdSet |-> {None}]]
  /\ msgs = {}

Spec ==
  Init /\ [][Next]_<<DDSOutput, ConsensusProposed, ConsensusDecided, fd, deps, msgs>>

Inv ==
  BLSMR!Validity /\ BLSMR!Agreement /\ BLSMR!Consistency

B == INSTANCE BLSMR

THEOREM Spec => B!Spec
============================