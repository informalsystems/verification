---------------------------- MODULE Lightclient ----------------------------
EXTENDS Integers, Sequences, Bags

CONSTANT
  Corr,     (* a set of correct nodes, which can act as validators *)
  Faulty,   (* a set of faulty nodes, which can act as validators *)  
  ULTIMATE_HEIGHT,
    (* The maximal height that can be ever reached (modelling artifact) *)
  MAX_POWER
    (* The maximal voting power of a single node *)  
    
Heights == 0..ULTIMATE_HEIGHT

AllNodes == Corr \union Faulty

Powers == 1..MAX_POWER

(* A commit is just a set of nodes who have committed the block *)
Commits == SUBSET AllNodes

(* The set of all block headers that can be on the blockchain.
   This is a simplified version of the Block data structure in the actual implementation. *)
BlockHeaders == [
  height: Heights,
    \* the block height
  lastCommit: Commits,
    \* the nodes who have voted on the previous block, the set itself instead of a hash
  (* in the implementation, only the hashes of V and NextV are stored in a block,
     as V and NextV are stored in the application state *) 
  V: [AllNodes -> Powers],
    \* the validators of this block together with their voting powers,
    \* i.e., a multi-set. We store the validators instead of the hash.
  NextV: [AllNodes -> Powers]
    \* the validators of the next block together with their voting powers,
    \* i.e., a multi-set. We store the next validators instead of the hash.
]

SignedHeaders == BlockHeaders \X Commits

VARIABLES
    height,
    (* the height of the blockchain, starting with 0 *)
    minTrustedHeight,
    (* The global height of the oldest block that is younger than
       the trusted period (AKA the almost rotten block).
       In the implementation, this is the oldest block,
       where block.bftTime + trustingPeriod >= globalClock.now. *)
    blockchain
    (* A sequence of BlockHeaders,
       which gives us the God's (or Daemon's) view of the blockchain. *)

(* Compute the total voting power of a subset of validators Nodes,
   whose individual voting powers are given by a function vp *)  
RECURSIVE PowerOfSet(_, _)
PowerOfSet(vp, Nodes) ==
    IF Nodes = {}
    THEN 0
    ELSE LET node == CHOOSE n \in Nodes: TRUE IN
        (* ASSERT(node \in DOMAIN vp) *)
        vp[node] + PowerOfSet(vp, Nodes \ {node})

(* Is the voting power correct,
   that is, more than 2/3 of the voting power belongs to the correct processes? *)
IsCorrectPower(vp) ==
    LET CV == Corr \intersect DOMAIN vp
        FV == Faulty \intersect DOMAIN vp
        CP == PowerOfSet(vp, CV)
        FP == PowerOfSet(vp, FV)
    IN
    CP > 0 /\ CP > 2 * FP
    

(* Append a new block on the blockchain.
   Importantly, more than 2/3 of voting power in the next set of validators
   belongs to the correct processes. *)       
AppendBlock ==
  LET last == blockchain[Len(blockchain)] IN
  \E lastCommit \in Commits,
     NextV \in SUBSET AllNodes \ {}:
     \E NextVP \in [NextV -> Powers]:
    LET new == [ height |-> height + 1, lastCommit |-> lastCommit,
                 VP |-> last.NextVP, NextVP |-> NextVP ] IN
    /\ IsCorrectPower(NextVP) \* the correct validators have >2/3 of power
    /\ blockchain' = Append(blockchain, new)
    /\ height' = height + 1                   

Init ==
  /\ height = 0
  /\ minTrustedHeight \in 1..ULTIMATE_HEIGHT
  (* pick a genesis block of all nodes where next correct validators have >2/3 of power *)
  /\ \E NextV \in SUBSET AllNodes \ {}:
       \E NextVP \in [NextV -> Powers]:
      /\ IsCorrectPower(NextVP)
      /\  LET VP == [n \in Corr |-> 1] 
              genesis == [ height |-> 0, lastCommit |-> {},
                           VP |-> VP, NextVP |-> NextVP]
          IN
          blockchain = <<genesis>>

Next ==
  (* the blockchain may progress by adding one more block,
     provided that the ultimate height has not been reached yet *)
  /\ \/ height < ULTIMATE_HEIGHT /\ AppendBlock
     \/ height = ULTIMATE_HEIGHT /\ UNCHANGED <<height, blockchain>> 
  (* as time is passing, the minimal trusted height may increase *)
  /\ minTrustedHeight' \in minTrustedHeight..ULTIMATE_HEIGHT

=============================================================================
\* Modification History
\* Last modified Thu Oct 03 12:11:30 CEST 2019 by igor
\* Created Wed Oct 02 16:39:42 CEST 2019 by igor
