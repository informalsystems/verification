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
 into two sets: the Byzantine processes and the defective processes.
 While the Byzantine processes can demonstrate arbitrary behavior, including
 no communication, the defective processes send their messages but deviate
 from the protocol in two ways:

   - Equivocation: a defective process may send two different values
     in the same round.

   - Amnesia: a defective process may lock a value, although it has locked
     another value in the past.

# TLA+ modules
 
 - [TendermintAcc3](TendermintAcc3.tla) is the protocol specification,

 - [TendermintAccDebug3](TendermintAccDebug3.tla) contains the useful definitions
   for debugging the protocol specification with TLC and Apalache,

 - [TendermintAccInv3](TendermintAccInv3.tla) contains an inductive invariant
   for establishing the protocol safety as well as the forking cases,

 - `MC_n<n>_f<f>`, e.g., [MC_n4_f1](MC_n4_f1.tla), contains fixed constants
   for model checking with Apalache

# Reasoning about fork scenarios

The theorem statements can be found in
[TendermintAccInv3.tla](TendermintAccInv3.tla).

First, we would like to show that `TypedInv` is an inductive invariant.
Formally, the statement looks as follows:

```tla
THEOREM TypedInvIsInductive ==
    \/ FaultyQuorum
    \//\ Init => TypedInv
      /\ TypedInv /\ [Next]_vars => TypedInv
```

When over two-thirds of processes are faulty, `TypedInv` is not inductive.
However, there is no hope to repair the protocol in this case. We run Apalache
to prove this theorem only for fixed instances of 4 to 10 processes.  Apalache
does not parse theorem statements at the moment, so we ran Apalache using a
shell script. To find a parameterized argument, one has to use a theorem
prover, e.g., TLAPS.

Second, we would like to show that the invariant implies `Agreement`, that is,
no fork, provided that less than one third of processes is faulty. By combining
this theorem with the previous theorem, we conclude that the protocol indeed
satisfies Agreement under the condition `LessThanThirdFaulty`.

```tla
THEOREM AgreementWhenLessThanThirdFaulty ==
    LessThanThirdFaulty /\ TypedInv => Agreement
```

Third, in the general case, we either have no fork, or two fork scenarios:

```tla
THEOREM AgreementOrFork ==
    ~FaultyQuorum /\ TypedInv => AgreementOrEquivocationOrAmnesia
```

# Model checking results   

TODO

# Running the experiments

Run the experiments by using the script:

```console
./run.sh
```

This script assumes that apalache builds are available in:

 * `~/devl/apalache-card` contains the build for the branch `ik/card`,
 * `~/devl/apalache-unstable` contains the build for branch `unstable`.


