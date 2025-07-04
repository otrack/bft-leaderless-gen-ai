-------------------- MODULE BQS --------------------
EXTENDS FiniteSets, Naturals, TLC

CONSTANTS
  ProcSet, \* Set of processes (should be integers 1..n for WQS)
  f        \* Fault threshold, integer

n == Cardinality(ProcSet)

\* Integer ceiling division
CeilDiv(x, y) == IF x % y = 0 THEN x \div y ELSE (x \div y) + 1

\* Integer ceiling sqrt
CeilSqrt(x) == CHOOSE s \in 0..n : s * s >= x /\ (s = 0 \/ (s-1)*(s-1) < x)

\* Adversary: All subsets of ProcSet of size at most f
Adversary == { B \in SUBSET ProcSet : Cardinality(B) <= f }

\* DQS: all subsets of ProcSet of size at least 2f+1 (n = 3f+1)
DQSQuorums == { Q \in SUBSET ProcSet : Cardinality(Q) >= 2*f + 1 }

DQS_Consistency ==
  \A Q1 \in DQSQuorums:
    \A Q2 \in DQSQuorums:
      \A B \in Adversary:
        ~( (Q1 \cap Q2) \subseteq B )

DQS_Availability ==
  \A B \in Adversary:
    \E Q \in DQSQuorums: (Q \cap B) = {}

\* MQS: all subsets of ProcSet of size at least CeilDiv(n + 2*f + 1, 2)
MQSQuorums == { Q \in SUBSET ProcSet : Cardinality(Q) >= CeilDiv(n + 2*f + 1, 2) }

MQS_Consistency ==
  \A Q1 \in MQSQuorums:
    \A Q2 \in MQSQuorums:
      \A B1 \in Adversary:
        \A B2 \in Adversary:
          ~(( (Q1 \cap Q2) \ B1 ) \subseteq B2)

MQS_Availability ==
  \A B \in Adversary:
    \E Q \in MQSQuorums: (Q \cap B) = {}

\* WQS: grid-based, parameterized by zeta = CeilSqrt(3*f \div 2 + 1)
Zeta == CeilSqrt((3*f) \div 2 + 1)
SqrtN == CeilSqrt(n)

\* For grid, assume ProcSet = 1..n
Rows == 
  [i \in 1..SqrtN |->
    { p \in ProcSet : 
        LET row == (i-1)*SqrtN + 1 .. i*SqrtN
        IN p \in row }
  ]
Cols == 
  [j \in 1..SqrtN |->
    { p \in ProcSet :
        LET col == { k \in 0..SqrtN-1 : p = k*SqrtN + j /\ p <= n }
        IN ( \E k \in 0..SqrtN-1 : p = k*SqrtN + j /\ p <= n ) }
  ]

ZetaSubsets(S) == { T \in SUBSET S : Cardinality(T) = Zeta }

WQSQuorums ==
  { UNION { Rows[i] : i \in pair[1] } \cup UNION { Cols[j] : j \in pair[2] } :
      pair \in ZetaSubsets(1..SqrtN) \X ZetaSubsets(1..SqrtN) }     

WQS_Consistency ==
  \A Q1 \in WQSQuorums:
    \A Q2 \in WQSQuorums:
      \A B1 \in Adversary:
        \A B2 \in Adversary:
          \A B3 \in Adversary:
            ~( ((Q1 \cap Q2) \ (B1 \cup B2)) \subseteq B3 )

WQS_Availability ==
  \A B \in Adversary:
    \E Q \in WQSQuorums: (Q \cap B) = {}

DQS_Correctness == DQS_Consistency /\ DQS_Availability
MQS_Correctness == MQS_Consistency /\ MQS_Availability
WQS_Correctness == WQS_Consistency /\ WQS_Availability

VARIABLE faulty

Inv ==  /\ (3*f + 1 = n) => DQS_Consistency
        /\ (CeilDiv(n + 2*f + 1, 2) + f <= n) => MQS_Correctness
        /\ (5*f + 1 <= n) => WQS_Correctness

Init == /\ faulty \in SUBSET ProcSet 
        /\ Cardinality(faulty) = f

Next == UNCHANGED <<faulty>>
======================================================