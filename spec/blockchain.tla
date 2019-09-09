----------------------------- MODULE blockchain -----------------------------
(*
 * This is a sequential specification of a blockchain. There is neither consensus algorithm,
 * nor there is any distributed computation. We only describe how a tendermint blockchain
 * should evolve. The non-trivial part here is the relation between the validators, their voting power,
 * and the commiters of the previous block.
 *
 * This is a specification that was quickly written in Novi Sad in May 2019.
 *)

EXTENDS Integers, Sequences

CONSTANTS
  MaxHeight,        \* an upper bound on the blockchain height (to bound the chain for model checking) 
  MaxN,             \* an upper bound one the number of validators
  MaxPower,         \* an upper bound on the voting power per validator
  initValidators,   \* an initial set of validators
  initAppState      \* an initial state of the application

\* visible state
VARIABLES blocks

\* state internal to the application
VARIABLES
    appState, \* the application state
    prevValidatorSet, validatorSet, nextValidatorSet,   \* the sets of validators: before, now, and after
    prevVotingPower, votingPower, nextVotingPower       \* the voting power of the validators: before, now, and after
    
\* auxilliary variables, which are hidden in the Tendermint consensus
VARIABLES prevCommiters \* commiters of the previous block

vars == <<blocks, appState, prevValidatorSet, validatorSet, nextValidatorSet,
          prevVotingPower, votingPower, nextVotingPower, prevCommiters>>

\* The set of potential validator ids, e.g., public keys
Id == 1..MaxN

\* A hash function. For the moment, it is identity.
Hash(s) == s

\* A nil block record
None == [ header |-> [height |-> -1], lastCommit |-> {} ]

\* A sum of set elements
RECURSIVE Sum(_)
Sum(S) ==
    IF S = {}
    THEN 0
    ELSE
      LET elem == CHOOSE x \in S: TRUE IN
      elem + Sum(S \ {elem})

\* The initial block in the blockchain
GenesisBlock == [
    header |-> [
        height |-> 0,
        validatorsH |-> Hash(initValidators),
        nextValidatorsH |-> Hash(initValidators),
        appH |-> Hash(initAppState),
        lastBlockId |-> Hash(None)
    ],
    \* txs |-> A LIST OF TRANSACTIONS,
    lastCommit |-> {}
]

\* The next application state, a function of an application state and the current block
NextAppState(as, blk) == as

\* A predicate that defines whether a validator set is good
IsValidValidatorSet(vs) == vs /= {}

\* a predicate that defines whether the voting power is correct
IsCorrectVotingPower(vp) == TRUE

\* Compute the set of next validators and its voting power
NextValidators(as, blk) ==
    /\ nextValidatorSet' \in SUBSET Id \* in the implementation, it is a function of transactions
    /\ IsValidValidatorSet(nextValidatorSet')
    /\ nextVotingPower' \in [nextValidatorSet' -> 1..MaxPower]
    /\ IsCorrectVotingPower(nextVotingPower')

\* The transition defined by the application
ABCI(blk) ==
    /\ appState' = NextAppState(appState, blk)
    /\ NextValidators(appState, blk)

\* a signature
Sign(key, payload) == payload 

\* Computing the next block
NextBlock(as, pvs, vs, nvs, pvp, prevComm, blk) == [
    header |-> [
        height |-> blk.header.height + 1,
        validatorsH |-> Hash(vs),
        nextValidatorsH |-> Hash(nvs),
        appH |-> Hash(as),
        lastBlockId |-> Hash(blk)
    ],
    \* txs |-> A LIST OF TRANSACTIONS,
    lastCommit |-> { <<v, pvp[v], Sign(v, blk.header.lastBlockId)>> : v \in prevComm }
]

\* There must have been more than two thirds of validators voting on the previous commit
MoreThanTwoThirds(pvs, commiters, vp) ==
    LET sum == Sum({vp[v] : v \in commiters}) IN
    LET totalSum == Sum({vp[v] : v \in pvs}) IN
    3 * sum > 2 * totalSum

\* Non-deterministically chosing the commiters for the previous block
\*  among the validators of the previous block 
NextPrevCommiters ==
    /\ prevCommiters' \in SUBSET prevValidatorSet
    /\ MoreThanTwoThirds(prevValidatorSet, prevCommiters', prevVotingPower)

\* The initial states
Init ==
    /\ blocks = <<GenesisBlock>>
    /\ appState = initAppState
    /\ prevValidatorSet = initValidators
    /\ validatorSet = initValidators
    /\ nextValidatorSet = initValidators
    /\ prevVotingPower \in [initValidators -> 1..MaxPower]
    /\ IsCorrectVotingPower(prevVotingPower)
    /\ votingPower \in [initValidators -> 1..MaxPower]
    /\ IsCorrectVotingPower(votingPower)
    /\ nextVotingPower \in [initValidators -> 1..MaxPower]
    /\ IsCorrectVotingPower(nextVotingPower)
    /\ prevCommiters = {}

\* The system transitions: at every step, add one more block until the limit is reached
Next ==
    \/ Len(blocks) >= MaxHeight /\ UNCHANGED vars \* do not grow the blockchain anymore
    \/  /\ Len(blocks) < MaxHeight  \* add one more block
        /\ LET lastBlock == blocks[Len(blocks)] IN
            /\ ABCI(lastBlock)
            /\ NextPrevCommiters
            /\ prevValidatorSet' = validatorSet
            /\ validatorSet' = nextValidatorSet
            /\ prevVotingPower' = votingPower
            /\ votingPower' = nextVotingPower
            /\ LET nextBlock ==
                 NextBlock(appState', prevValidatorSet, validatorSet,
                           nextValidatorSet, prevVotingPower, prevCommiters', lastBlock)
               IN
                 blocks' = Append(blocks, nextBlock)

\* Properties
BlockchainInv ==
    \A i \in 1..Len(blocks) - 1:
        blocks[i + 1].header.lastBlockId = Hash(blocks[i]) 

=============================================================================
\* Modification History
\* Last modified Mon Sep 09 15:56:59 CEST 2019 by igor
\* Created Thu May 09 11:01:03 CEST 2019 by igor
