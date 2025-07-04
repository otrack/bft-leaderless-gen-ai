---------------------- MODULE SMR ----------------------

EXTENDS Service

CONSTANTS
    ProcSet           \* Set of processes

ASSUME ProcSet /= {} 

VARIABLES
    executed,          \* executed[p] = sequence of commands executed by process p
    submitted          \* submitted = set of commands submitted to the system

\* Each process holds a local copy of the state machine as a sequence of executed commands.
Vars == << executed, submitted >>

\* Initial state: nothing executed, nothing submitted
Init ==
    /\ executed = [p \in ProcSet |-> << >>]
    /\ submitted = {}

\* A process can submit a command if it has not already executed it.
Submit(cmd, p) ==
    /\ cmd \in CmdSet
    /\ p \in ProcSet
    /\ cmd \notin submitted
    /\ submitted' = submitted \cup {cmd}
    /\ UNCHANGED executed

isSafe(c, i) ==
    /\ c \in CmdSet
    /\ \A p \in ProcSet : 
        IF Len(executed[p]) < i 
        THEN TRUE 
        ELSE executed[p][i] = c 

isAtMostOnce(c, p) ==
    /\ ~ (\E i \in 1..Len(executed[p]): executed[p][i] = c)

\* A process can execute a command if it was submitted and has not already executed it.
Execute(cmd, p) ==
    /\ cmd \in submitted
    /\ p \in ProcSet    
    /\ isAtMostOnce(cmd, p)
    /\ isSafe(cmd, Len(executed[p])+1)
    /\ executed' = [executed EXCEPT ![p] = Append(@, cmd)]
    /\ UNCHANGED submitted

\* The system step: any process can submit or execute commands
Next ==
    \E p \in ProcSet, cmd \in CmdSet:
        Submit(cmd, p)
    \/ \E q \in ProcSet, cmd2 \in submitted:
        Execute(cmd2, q)

\* Safety and liveness properties:

\* 1. Validity: If a correct process executes a command, then it is a valid command.
Validity ==
    \A p \in ProcSet: \A i \in 1..Len(executed[p]): executed[p][i] \in CmdSet

\* 2. Integrity: Each process executes each command at most once.
Integrity ==
    \A p \in ProcSet: \A c \in CmdSet: Len(SelectSeq(executed[p], LAMBDA x: x = c)) <= 1

\* 3. Consistency: Correct processes execute conflicting commands in the same order.
Position(c, seq) ==
  IF \E i \in 1..Len(seq) : seq[i] = c
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = c
    ELSE Len(seq) + 1

Precedes(c, d) ==
  \E p \in ProcSet :
    /\ Conflicts(c, d)
    /\ \E i \in 1..Len(executed[p]) : executed[p][i] = c
    /\ Position(c, executed[p]) < Position(d, executed[p])

PrecedesPairs ==
  { <<c, d>> \in CmdSet \X CmdSet : Precedes(c, d) }

RECURSIVE Reaches(_,_)
Reaches(c, d) ==
  \/ <<c, d>> \in PrecedesPairs
  \/ \E e \in CmdSet : <<c, e>> \in PrecedesPairs /\ Reaches(e, d)

NoPrecedesCycle ==
  \A c \in CmdSet : ~Reaches(c, c)

Consistency == NoPrecedesCycle

\* 4. Liveness: If a command is submitted by a correct process or executed at some correct process, it is eventually executed at all correct processes.
Liveness ==
    \A cmd \in submitted:
      \A p \in ProcSet:
        <> (cmd \in executed[p])

\* Specification
Spec ==
    Init /\ [][Next]_Vars

=============================================================================
