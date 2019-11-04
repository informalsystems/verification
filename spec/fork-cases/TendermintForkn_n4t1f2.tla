----------------------- MODULE TendermintForkn_n4t1f2 -----------------------
EXTENDS Integers

NInjected == 1 \* the number of injected faulty messages

N == 4 \* the total number of processes: correct and faulty
T == 1 \* an upper bound on the number of Byzantine processes
F == 1 \* the number of Byzantine processes
Heights == 0..1 \* the set of consensus instances
Rounds == 0..2  \* the set of possible rounds, give a bit more freedom to the solver
ValidValues == {0, 1}     \* e.g., picked by a correct process, or a faulty one
InvalidValues == {2}    \* e.g., sent by a Byzantine process

PValues == ValidValues \cup InvalidValues \* all values
PProcs == 1..N-F
PFaulty == N-F+1..N

FaultyMessages == \* the messages that can be sent by the faulty processes
    [type: {"PROPOSAL"}, src: PFaulty, h: Heights,
              round: Rounds, proposal: PValues, validRound: Rounds \cup {-1}]
       \cup
    [type: {"PREVOTE"}, src: PFaulty, h: Heights, round: Rounds, hash: PValues]
       \cup
    [type: {"PRECOMMIT"}, src: PFaulty, h: Heights, round: Rounds, hash: PValues]

\* the proposer is rotating 
PropFun == [<<ht, rd>> \in Heights \X Rounds |-> (ht + rd) % N]

\* the variables that are declared in TendermintFork
VARIABLES h, round, step, decision, lockedValue, lockedRound, validValue, validRound 
VARIABLES msgsPropose, msgsPrevote, msgsPrecommit,
          oldEvents, timeoutPropose, timeoutPrevote, timeoutPrecommit

INSTANCE TendermintFork


=============================================================================
\* Modification History
\* Last modified Mon Nov 04 14:59:54 CET 2019 by igor
\* Created Mon Nov 04 11:47:48 CET 2019 by igor
