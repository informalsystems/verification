----------------------------- MODULE TendermintAcc3 ---------------------------
(*
 A TLA+ specification of a simplified Tendermint consensus, tuned for
 fork accountability. The simplifications are as follows:

 - the procotol runs for one height, that is, one-shot consensus

 - this specification focuses on safety, so timeouts are modelled with
   with non-determinism

 - the proposer function is non-determinstic, no fairness is assumed

 - the messages by the faulty processes are injected right in the initial states

 - every process has the voting power of 1

 - hashes are modelled as identity

 Having the above assumptions in mind, the specification follows the pseudo-code
 of the Tendermint paper: https://arxiv.org/abs/1807.04938

 For the purposes of fork accountability, the faulty processes are partitioned
 into two sets: the Byzantine processes and the amnesic processes.
 While the Byzantine processes can demonstrate arbitrary behavior, including
 no communication, the amnesic processes send their messages but do not hold
 to the contract of locked values.

 * Version 3. Modular and parameterized definitions.
 * Version 2. Bugfixes in the spec and an inductive invariant.
 * Version 1. A preliminary specification.

 Zarko Milosevic, Igor Konnov, 2019-2020.
 *)

EXTENDS Integers, FiniteSets

(********************* PROTOCOL PARAMETERS **********************************)
CONSTANTS
    Corr,          \* the set of correct processes 
    Defective,     \* the set of processes that show defects, e.g, amnesia or equivocation
    Byzantine,     \* the set of Byzantine processes, may be empty
    N,             \* the total number of processes: correct, amnesic, and Byzantine
    T,             \* an upper bound on the number of Byzantine processes
    ValidValues,   \* the set of valid values, proposed both by correct and faulty
    InvalidValues, \* the set of invalid values, never proposed by the correct ones
    MaxRound,      \* the maximal round number
    Proposer       \* the proposer function from 0..NRounds to 1..N

ASSUME(N = Cardinality(Corr \union Defective \union Byzantine))

(*************************** DEFINITIONS ************************************)
Faulty == Defective \union Byzantine  \* the set of faulty processes
AllProcs == Corr \union Faulty      \* the set of all processes
Rounds == 0..MaxRound               \* the set of potential rounds
NilRound == -1   \* a special value to denote a nil round, outside of Rounds
RoundsOrNil == Rounds \union {NilRound}
Values == ValidValues \union InvalidValues \* the set of all values
NilValue == "None"  \* a special value for a nil round, outside of Values
ValuesOrNil == Values \union {NilValue}

\* a value hash is modeled as identity
Id(v) == v

\* The validity predicate
IsValid(v) == v \in ValidValues

\* the two thresholds that are used in the algorithm
THRESHOLD1 == T + 1     \* at least one process is not faulty
THRESHOLD2 == 2 * T + 1 \* a quorum when having N > 3 * T

(********************* TYPE ANNOTATIONS FOR APALACHE **************************)
\* the operator for type annotations
a <: b == a

\* the type of message records
MT == [type |-> STRING, src |-> STRING, round |-> Int,
       proposal |-> STRING, validRound |-> Int, id |-> STRING]
       
\* a type annotation for a message
AsMsg(m) == m <: MT
\* a type annotation for a set of messages
SetOfMsgs(S) == S <: {MT}       
\* a type annotation for an empty set of messages
EmptyMsgSet == SetOfMsgs({})

(********************* PROTOCOL STATE VARIABLES ******************************)
VARIABLES
  round,    \* a process round number: Corr -> Rounds
  step,     \* a process step: Corr -> { "PROPOSE", "PREVOTE", "PRECOMMIT", "DECIDED" }
  decision, \* process decision: Corr -> ValuesOrNil
  lockedValue,  \* a locked value: Corr -> ValuesOrNil
  lockedRound,  \* a locked round: Corr -> RoundsOrNil
  validValue,   \* a valid value: Corr -> ValuesOrNil
  validRound    \* a valid round: Corr -> RoundsOrNil

\* book-keeping variables
VARIABLES
  msgsPropose,   \* PROPOSE messages broadcast in the system, Rounds -> Messages
  msgsPrevote,   \* PREVOTE messages broadcast in the system, Rounds -> Messages
  msgsPrecommit, \* PRECOMMIT messages broadcast in the system, Rounds -> Messages
  evidence \* the messages that were used by the process that made a transition

(* to see a type invariant, check TendermintAccInv3 *)  
 
\* a handy definition used in UNCHANGED
vars == <<round, step, decision, lockedValue, lockedRound,
          validValue, validRound, evidence, msgsPropose, msgsPrevote, msgsPrecommit>>

(********************* PROTOCOL INITIALIZATION ******************************)
FaultyProposals(r) ==
    SetOfMsgs([type: {"PROPOSAL"}, src: Faulty,
               round: {r}, proposal: Values, validRound: RoundsOrNil])

FaultyPrevotes(r) ==
    SetOfMsgs([type: {"PREVOTE"}, src: Faulty, round: {r}, id: Values])

FaultyPrecommits(r) ==
    SetOfMsgs([type: {"PRECOMMIT"}, src: Faulty, round: {r}, id: Values])

\* The initial states of the protocol. The faults can be in the system already.
Init ==
    /\ round = [p \in Corr |-> 0]
    /\ step = [p \in Corr |-> "PROPOSE"]
    /\ decision = [p \in Corr |-> NilValue]
    /\ lockedValue = [p \in Corr |-> NilValue]
    /\ lockedRound = [p \in Corr |-> NilRound]
    /\ validValue = [p \in Corr |-> NilValue]
    /\ validRound = [p \in Corr |-> NilRound]
    /\ msgsPropose = [r \in Rounds |-> FaultyProposals(r)]
    /\ msgsPrevote = [r \in Rounds |-> FaultyPrevotes(r)]
    /\ msgsPrecommit = [r \in Rounds |-> FaultyPrecommits(r)]
    /\ evidence = EmptyMsgSet

(************************ MESSAGE PASSING ********************************)
BroadcastProposal(pSrc, pRound, pProposal, pValidRound) ==
  LET newMsg ==
    AsMsg([type |-> "PROPOSAL", src |-> pSrc, round |-> pRound,
           proposal |-> pProposal, validRound |-> pValidRound])
  IN
  msgsPropose' = [msgsPropose EXCEPT ![pRound] = msgsPropose[pRound] \cup {newMsg}]

BroadcastPrevote(pSrc, pRound, pId) ==
  LET newMsg == AsMsg([type |-> "PREVOTE",
                       src |-> pSrc, round |-> pRound, id |-> pId])
  IN
  msgsPrevote' = [msgsPrevote EXCEPT ![pRound] = msgsPrevote[pRound] \cup {newMsg}]

BroadcastPrecommit(pSrc, pRound, pId) ==
  LET newMsg == AsMsg([type |-> "PRECOMMIT",
                       src |-> pSrc, round |-> pRound, id |-> pId])
  IN
  msgsPrecommit' = [msgsPrecommit EXCEPT ![pRound] = msgsPrecommit[pRound] \cup {newMsg}]


(********************* PROTOCOL TRANSITIONS ******************************)
\* lines 12-13
StartRound(p, r) ==
   /\ step[p] /= "DECIDED" \* a decided process does not participate in consensus
   /\ round' = [round EXCEPT ![p] = r]
   /\ step' = [step EXCEPT ![p] = "PROPOSE"] 

\* lines 14-19, a proposal may be sent later
InsertProposal(p) == 
  LET r == round[p] IN
  /\ p = Proposer[r]
  /\ step[p] = "PROPOSE"
    \* if the proposer is sending a proposal, then there are no other proposals
    \* by the correct processes for the same round
  /\ \A m \in msgsPropose[r]: m.src /= p
  /\ \E v \in ValidValues: 
      LET proposal == IF validValue[p] /= NilValue THEN validValue[p] ELSE v IN
      BroadcastProposal(p, round[p], proposal, validRound[p])
  /\ evidence' = EmptyMsgSet
  /\ UNCHANGED <<round, decision, lockedValue, lockedRound,
                 validValue, step, validRound, msgsPrevote, msgsPrecommit>>

\* lines 22-27
UponProposalInPropose(p) ==
  \E v \in Values:
    /\ step[p] = "PROPOSE" (* line 22 *)
    /\ LET msg ==
        AsMsg([type |-> "PROPOSAL", src |-> Proposer[round[p]],
               round |-> round[p], proposal |-> v, validRound |-> NilRound]) IN
      /\ msg \in msgsPropose[round[p]] \* line 22
      /\ evidence' = {msg}
    /\ LET mid == (* line 23 *)
         IF IsValid(v) /\ (lockedRound[p] = NilRound \/ lockedValue[p] = v)
         THEN Id(v)
         ELSE NilValue
       IN
       BroadcastPrevote(p, round[p], mid) \* lines 24-26
    /\ step' = [step EXCEPT ![p] = "PREVOTE"]
    /\ UNCHANGED <<round, decision, lockedValue, lockedRound,
                   validValue, validRound, msgsPropose, msgsPrecommit>>

\* lines 28-33        
UponProposalInProposeAndPrevote(p) ==
  \E v \in Values, vr \in Rounds:
    /\ step[p] = "PROPOSE" /\ 0 <= vr /\ vr < round[p] \* line 28, the while part
    /\ LET msg ==
         AsMsg([type |-> "PROPOSAL", src |-> Proposer[round[p]],
                round |-> round[p], proposal |-> v, validRound |-> vr])
       IN
       /\ msg \in msgsPropose[round[p]] \* line 28
       /\ LET PV == { m \in msgsPrevote[vr]: m.id = Id(v) } IN
          /\ Cardinality(PV) >= THRESHOLD2 \* line 28
          /\ evidence' = PV \union {msg}
    /\ LET mid == (* line 29 *)
         IF IsValid(v) /\ (lockedRound[p] <= vr \/ lockedValue[p] = v)
         THEN Id(v)
         ELSE NilValue
       IN
       BroadcastPrevote(p, round[p], mid) \* lines 24-26
    /\ step' = [step EXCEPT ![p] = "PREVOTE"]
    /\ UNCHANGED <<round, decision, lockedValue, lockedRound,
                   validValue, validRound, msgsPropose, msgsPrecommit>>
                     
 \* lines 34-35 + lines 61-64 (onTimeoutPrevote)
UponQuorumOfPrevotesAny(p) ==
  /\ step[p] = "PREVOTE" \* line 34 and 61
  /\ Cardinality(msgsPrevote[round[p]]) >= THRESHOLD2 \* line 34
  \* multiple messages from a process may trigger this rule (no effect on safety)
  /\ evidence' = msgsPrevote[round[p]]
  /\ BroadcastPrecommit(p, round[p], NilValue)
  /\ step' = [step EXCEPT ![p] = "PRECOMMIT"]
  /\ UNCHANGED <<round, decision, lockedValue, lockedRound,
                 validValue, validRound, msgsPropose, msgsPrevote>>
                     
\* lines 36-46
UponProposalInPrevoteOrCommitAndPrevote(p) ==
  \E v \in ValidValues, vr \in RoundsOrNil:
    /\ step[p] \in {"PREVOTE", "PRECOMMIT"} \* line 36
    /\ LET msg ==
         AsMsg([type |-> "PROPOSAL", src |-> Proposer[round[p]],
                round |-> round[p], proposal |-> v, validRound |-> vr]) IN
        /\ msg \in msgsPropose[round[p]] \* line 36
        /\ LET PV == { m \in msgsPrevote[round[p]]: m.id = Id(v) } IN
          /\ Cardinality(PV) >= THRESHOLD2 \* line 36
          /\ evidence' = PV \union {msg}
    /\  IF step[p] = "PREVOTE"
        THEN \* lines 38-41:
          /\ lockedValue' = [lockedValue EXCEPT ![p] = v]
          /\ lockedRound' = [lockedRound EXCEPT ![p] = round[p]]
          /\ BroadcastPrecommit(p, round[p], Id(v))
          /\ step' = [step EXCEPT ![p] = "PRECOMMIT"]
        ELSE
          UNCHANGED <<lockedValue, lockedRound, msgsPrecommit, step>>
      \* lines 42-43
    /\ validValue' = [validValue EXCEPT ![p] = v]
    /\ validRound' = [validRound EXCEPT ![p] = round[p]]
    /\ UNCHANGED <<round, decision, msgsPropose, msgsPrevote>>

\* lines 47-48 + 65-67 (onTimeoutPrecommit)
UponQuorumOfPrecommitsAny(p) ==
  /\ Cardinality(msgsPrecommit[round[p]]) >= THRESHOLD2 \* line 47
  /\ evidence' = msgsPrecommit[round[p]]
  /\ round[p] + 1 \in Rounds
  /\ StartRound(p, round[p] + 1)   
  /\ UNCHANGED <<decision, lockedValue, lockedRound, validValue,
                 validRound, msgsPropose, msgsPrevote, msgsPrecommit>>
                     
\* lines 49-54        
UponProposalInPrecommitNoDecision(p) ==
  /\ decision[p] = NilValue \* line 49
  /\ \E v \in ValidValues (* line 50*) , r \in Rounds, vr \in RoundsOrNil:
    /\ LET msg == AsMsg([type |-> "PROPOSAL", src |-> Proposer[r],
                           round |-> r, proposal |-> v, validRound |-> vr]) IN
       /\ msg \in msgsPropose[r] \* line 49
       /\ LET PV == { m \in msgsPrecommit[r]: m.id = Id(v) } IN
           /\ Cardinality(PV) >= THRESHOLD2 \* line 49
           /\ evidence' = PV \union {msg}
    /\ decision' = [decision EXCEPT ![p] = v] \* update the decision, line 51
    \* The original algorithm does not have 'DECIDED', but it increments the height.
    \* We introduced 'DECIDED' here to prevent the process from changing its decision.
    /\ step' = [step EXCEPT ![p] = "DECIDED"]
    /\ UNCHANGED <<round, lockedValue, lockedRound, validValue,
                     validRound, msgsPropose, msgsPrevote, msgsPrecommit>>
                                                          
\* the actions below are not essential for safety, but added for completeness

\* lines 20-21 + 57-60
OnTimeoutPropose(p) ==
  /\ step[p] = "PROPOSE"
  /\ p /= Proposer[round[p]]
  /\ BroadcastPrevote(p, round[p], NilValue)
  /\ step' = [step EXCEPT ![p] = "PREVOTE"]
  /\ UNCHANGED <<round, lockedValue, lockedRound, validValue,
                 validRound, decision, evidence, msgsPropose, msgsPrecommit>>

\* lines 44-46
OnQuoromOfNilPrevotes(p) ==
  /\ step[p] = "PREVOTE"
  /\ LET PV == { m \in msgsPrevote[round[p]]: m.id = Id(NilValue) } IN
      /\ Cardinality(PV) >= THRESHOLD2 \* line 36
      /\ evidence' = PV
  /\ BroadcastPrecommit(p, round[p], Id(NilValue))
  /\ step' = [step EXCEPT ![p] = "PREVOTE"]
  /\ UNCHANGED <<round, lockedValue, lockedRound, validValue,
                 validRound, decision, msgsPropose, msgsPrevote>>

\* lines 55-56
OnRoundCatchup(p) ==
  \E r \in {rr \in Rounds: rr > round[p]}:
    /\ LET RM == msgsPropose[r] \union msgsPrevote[r] \union msgsPrecommit[r] IN
      /\ Cardinality(RM) >= THRESHOLD1
      /\ evidence' = RM
    /\ StartRound(p, r)
    /\ UNCHANGED <<decision, lockedValue, lockedRound, validValue,
                   validRound, msgsPropose, msgsPrevote, msgsPrecommit>>

(*
 * A system transition. In this specificatiom, the system may eventually deadlock,
 * e.g., when all processes decide. This is expected behavior, as we focus on safety.
 *)
Next ==
  \E p \in Corr:
    \/ InsertProposal(p)
    \/ UponProposalInPropose(p)
    \/ UponProposalInProposeAndPrevote(p)
    \/ UponQuorumOfPrevotesAny(p)
    \/ UponProposalInPrevoteOrCommitAndPrevote(p)
    \/ UponQuorumOfPrecommitsAny(p)
    \/ UponProposalInPrecommitNoDecision(p)
    \* the actions below are not essential for safety, but added for completeness
    \/ OnTimeoutPropose(p)
    \/ OnQuoromOfNilPrevotes(p)
    \/ OnRoundCatchup(p) 
  
(**************************** FORK SCENARIOS  ***************************)
\* a state that has at least one equivocation
Equivocation ==
  \E r \in Rounds:
    \/ \E m1, m2 \in msgsPropose[r]:
      m1 /= m2 /\ m1.src = m2.src
    \/ \E m1, m2 \in msgsPrevote[r]:
      m1 /= m2 /\ m1.src = m2.src
    \/ \E m1, m2 \in msgsPrecommit[r]:
      m1 /= m2 /\ m1.src = m2.src

\* equivocation by amnesic processes
EquivocationBy(p) ==
  \E r \in Rounds:
    \/ \E m1, m2 \in msgsPropose[r]:
      m1.proposal /= m2.proposal /\ m1.src = p /\ m2.src = p
    \/ \E m1, m2 \in msgsPrevote[r]:
      m1.id /= m2.id /\ m1.src = p /\ m2.src = p
    \/ \E m1, m2 \in msgsPrecommit[r]:
      m1.id /= m2.id /\ m1.src = p /\ m2.src = p

\* amnesic behavior by a process p
AmnesiaBy(p) ==
    \E r1, r2 \in Rounds:
      /\ r1 < r2
      /\ \E v1, v2 \in ValidValues:
        /\ v1 /= v2
        /\ AsMsg([type |-> "PRECOMMIT", src |-> p,
                  round |-> r1, id |-> Id(v1)]) \in msgsPrecommit[r1]    
        /\ AsMsg([type |-> "PREVOTE", src |-> p,
                  round |-> r2, id |-> Id(v2)]) \in msgsPrecommit[r2]
        /\ \A r \in { rnd \in Rounds: r1 <= rnd /\ rnd <= r2 }:
            LET prevotes ==
                { m \in msgsPrevote[r]:
                  m.type = "PREVOTE" /\ m.round = r /\ m.id = Id(v2) }
            IN
            Cardinality(prevotes) < THRESHOLD2

\* Exclude the equivocation states, that is,
\* exclude the equivocal messages by the faulty processes
InitNoEquivocation ==
    Init /\ ~Equivocation

(******************************** PROPERTIES  ***************************************)

\* the safety property -- agreement
Agreement == \A p, q \in Corr:
    \/ decision[p] = NilValue
    \/ decision[q] = NilValue
    \/ decision[p] = decision[q]

\* the protocol validity
Validity ==
    \A p \in Corr: decision[p] \in ValidValues \union {NilValue}
 
\* either agreement holds, or the amnesic processes indeed have amnesia
AgreementOrAmnesia ==
    Agreement \/ (\A p \in Defective: AmnesiaBy(p))
 
\* the strong agreement property that also assumes no amnesia
AgreementNoAmnesia ==
    Agreement /\ \A p \in Defective: ~AmnesiaBy(p)

(*
  The protocol safety. Three cases are possible:
     1. There is no fork, that is, Agreement holds true.
     2. The amnesic processes have sent equivocal messages.
     3. The amnesic processes have sent messages that prove amnesia.
 *)    
AgreementOrEquivocationOrAmnesia ==
    \/ Agreement
    \/ \A p \in Defective: EquivocationBy(p)
    \/ \A p \in Defective: AmnesiaBy(p)

=============================================================================    
 
