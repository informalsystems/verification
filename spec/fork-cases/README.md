# Synopsis
 
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

# TLA+ modules
 
 - [TendermintAcc3](TendermintAcc3.tla) is the protocol specification,

 - [TendermintAccDebug3](TendermintAccDebug3.tla) contains the useful definitions
   for debugging the protocol specification with TLC and Apalache,

 - [TendermintAccInv3](TendermintAccInv3.tla) contains an inductive invariant
   for establishing the protocol safety as well as the forking cases,

 - `MC_n<n>_f<f>`, e.g., [MC_n4_f1](MC_n4_f1.tla), contains fixed constants
   for model checking with Apalache

# Model checking results   

TODO

# Running the experiments

TODO

