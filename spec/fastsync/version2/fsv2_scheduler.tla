------------------------------- MODULE fsv2_scheduler ---------------------------------------------
(*
 A specification of the fast sync scheduler that is introduced in blockchain/v2:
 
 https://github.com/tendermint/tendermint/blockchain/v2
 
 The model includes:
    - a scheduler that maintains the peers and blocks that it receives from the peers, and
    - one environment simulating a correct peer
    
 This specification focuses on the events that are received and produced by the scheduler.
 Communication between the scheduler and the other fastsync components is not specified.
*)

EXTENDS Integers, FiniteSets, TLC

\* the protocol parameters
CONSTANTS
    PeerIDs,        \* potential peer ids, a set of integers, e.g., 0..2
    ultimateHeight, \* the maximum height of the blockchain, an integer, e.g., 3
    numRequests     \* the number of requests made per batch, e.g., 2

\* a few definitions
None == -1                      \* an undefined value
Heights == 1..ultimateHeight    \* potential heights
noErr == "errNone"
Errors == { noErr, "errPeerNotFound", "errDelRemovedPeer", "errAddDuplicatePeer", "errUpdateRemovedPeer", "errAfterPeerRemove"}
PeerStates == {"peerStateUnknown", "peerStateNew", "peerStateReady", "peerStateRemoved"}
BlockStates == {"blockStateUnknown", "blockStateNew", "blockStatePending", "blockStateReceived", "blockStateProcessed"}

\* basic stuff
Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

\* the state of the scheduler:
VARIABLE  turn          \* who makes a step: the scheduler or the environment

\* the state of the reactor: 
VARIABLES inEvent,       \* an event from the environment to the scheduler
          envRunning \* a Boolean, negation of stopProcessing in the implementation
                    
\* the state of the scheduler:
VARIABLES outEvent,       \* an event from the scheduler to the environment
          scRunning

\* the block pool: 
VARIABLE scheduler
    (*
       scheduler is a record that contains: 
         height: Int,
            height of the next block to collect
         peers: PeerIDs,
            the set of active peers, not known to be faulty
         peerHeights: [PeerIDs -> Heights],
            a map to collect the peer responses about their heights 
         peerStates: [PeerIDs -> PeerStates],
            a map to record the peer states 
         blockStates: [Heights -> BlockStates]
            a set of heights for which blocks are to be scheduled, pending or received
         pendingBlocks: [Heights -> PeerIDs],
            a set of heights for which blocks are to be scheduled or pending
         receivedBlocks: [Heights -> PeerIDs],
            a set of heights for which blocks were received but not yet processed
    *)
    
vars == <<turn, envRunning, inEvent, scRunning, outEvent, scheduler>>    

(* For the scheduler a block is completely abstract, it only knows if it is wellFormed or not. *)
Blocks == [ wellFormed: BOOLEAN ]
BadBlock == [ wellFormed |-> FALSE]

noEvent == [type |-> "NoEvent"] 

InEvents == 
  {noEvent} \cup
  [type: {"rTrySchedule", "tNoAdvanceExp", "rTryPrunePeer"}] \cup
  [type: {"bcStatusResponse"},    peerID: PeerIDs, height: Heights] \cup
  [type: {"bcBlockResponse"},     peerID: PeerIDs, height: Heights, block: Blocks] \cup
  [type: {"bcNoBlockResponse"},   peerID: PeerIDs, height: Heights] \cup
  [type: {"pcBlockProcessed"},    peerId: PeerIDs, height: Heights] \cup
  [type: {"pcBlockVerificationFailure"}, firstPeerID: PeerIDs, secondPeerID: PeerIDs] \cup
  [type: {"bcAddNewPeer"},        peerID: PeerIDs] \cup
  [type: {"bcRemovePeer"},        peerID: PeerIDs]

\* Output events produced by the scheduler.
\* Note: in v2 the status request is done by the reactor/ environment
OutEvents == 
  {noEvent} \cup
  [type: {"scPeerError"}, peerID: PeerIDs, reason: Errors] \cup
  [type: {"scSchedulerFail"}, reason: Errors] \cup
  [type: {"scBlockRequest"}, peerID: PeerIDs, height: Heights] \cup
  [type: {"scBlockReceived"}, peerID: PeerIDs, block: Blocks] \cup
  [type: {"scPeersPruned"}, pruned: SUBSET [peerID: PeerIDs]] \cup 
  [type: {"scFinishedEv"},  reason: Errors]
                        
(* ----------------------------------------------------------------------------------------------*)
(* The behavior of the scheduler that keeps track of peers, block requests and responses, etc.   *)
(* See scheduler.go                                                                              *)
(* https://github.com/tendermint/tendermint/blockchain/v2/scheduler.go                           *)
(* ----------------------------------------------------------------------------------------------*)

addPeer(sc, peerID) == 
  IF peerID \in sc.peers THEN
    [err |-> "errAddDuplicatePeer", res |-> sc]
  ELSE
    LET newPeers == sc.peers \cup { peerID } IN
    LET newPeerHeights == [sc.peerHeights EXCEPT ![peerID] = None] IN
    LET newPeerStates == [sc.peerStates EXCEPT ![peerID] = "peerStateNew"] IN
    LET newSc == [sc EXCEPT 
      !.peers = newPeers,
      !.peerHeights = newPeerHeights, 
      !.peerStates = newPeerStates] IN
    [err |-> noErr, res |-> newSc]

maxPeer(states, heights) ==
 LET activePeers == {p \in DOMAIN states: states[p] = "peerStateReady"} IN
 IF activePeers = {} THEN 
   0 \* no peers, just return 0
 ELSE 
   CHOOSE max \in { heights[p] : p \in activePeers }:
        \A p \in activePeers: heights[p] <= max \* max is the maximum

removePeer(sc, peerID) ==
  IF peerID \notin sc.peers THEN
    [err |-> "errPeerNotFound", res |-> sc]
  ELSE IF sc.peerStates[peerID] = "peerStateRemoved" THEN
    [err |-> "errDelRemovedPeer", res |-> sc]
  ELSE
    LET newPeerHeights == [sc.peerHeights EXCEPT ![peerID] = None] IN
    LET newPeerStates == [sc.peerStates EXCEPT ![peerID] = "peerStateRemoved"] IN
    LET newMph == maxPeer(newPeerStates, newPeerHeights) IN
    
    \* remove all blocks from peerID and block requests to peerID, see scheduler.removePeer
    LET newBlockStates == [h \in Heights |-> IF sc.pendingBlocks[h] = peerID THEN "blockStateNew" ELSE sc.blockStates[h]] IN
    LET newPendingBlocks == [h \in Heights |-> IF sc.pendingBlocks[h] = peerID THEN None ELSE sc.pendingBlocks[h]] IN
    LET newReceivedBlocks == [h \in Heights |-> IF sc.receivedBlocks[h] = peerID THEN None ELSE sc.receivedBlocks[h]] IN

    LET newSc == [sc EXCEPT 
      !.peers = sc.peers \ {peerID},
      !.peerHeights = newPeerHeights, !.peerStates = newPeerStates,
      !.blockStates = newBlockStates,
      !.pendingBlocks = newPendingBlocks
      \*!.receviedBlocks = newReceivedBlocks
      ] IN                 
    [err |-> noErr, res |-> newSc]  
      
addNewBlocks(sc, newMph) ==
  \* add new blocks in blockStates if required (i.e. if the peer changed the max peer height 
  IF FALSE THEN
    LET newBlockStatesDomain == {h \in sc.height..numRequests+sc.height: h <= newMph} IN
    LET newBlocks == {h \in newBlockStatesDomain: sc.blockStates[h] = "blockStateUnknown"} \cup sc.blocks IN
    LET newBlockStates == [h \in newBlockStatesDomain |-> 
              IF sc.blockStates[h] = "blockStateUnknown" THEN "blockStateNew" ELSE sc.blockStates[h]] IN
    [newBlocks |-> newBlocks, newBlockStates |-> newBlockStates]
  ELSE
    [newBlocks |-> sc.blocks, newBlockStates |-> sc.blockStates]
 

\* Update the peer height (the peer should have been previously added)                    
setPeerHeight(sc, peerID, height) ==
  IF peerID \notin sc.peers THEN
    [err |-> "errPeerNotFound", res |-> sc]
  ELSE IF sc.peerStates[peerID] = "peerStateRemoved" THEN
    [err |-> "errUpdateRemovedPeer", res |-> sc]
  ELSE IF height < sc.peerHeights[peerID] THEN (* The peer is corrupt? Remove the peer. *)
    LET res == removePeer(sc, peerID) IN
    [err |-> res.err, res |-> res.res]     
  ELSE
    LET newPeerHeights == [sc.peerHeights EXCEPT ![peerID] = height] IN \* set the peer's height
    LET newPeerStates == [sc.peerStates EXCEPT ![peerID] = "peerStateReady"] IN \* set the peer's state
    LET newMph == maxPeer(newPeerStates, newPeerHeights) IN
    LET res == addNewBlocks(sc, newMph) IN
    LET newSc == [sc EXCEPT 
      !.peerHeights = newPeerHeights, !.peerStates = newPeerStates, 
      !.blocks = res.newBlocks, !.blockStates = res.newBlockStates] IN
    [err |-> noErr, res |-> newSc]              

\* Experiment with CASE
\* same as above, seems ok but the model checker outputs:
\* "CostModel lookup failed for expression <line ...>. 
\* Reporting costs into <line ...> instead 
\* (Safety and Liveness checking is unaffected. Please report a bug.)"
\* Running also seems to be slower
setPeerHeight1(sc, peerID, height) ==
  CASE peerID \notin sc.peers ->
        [err |-> "errPeerNotFound", res |-> sc]
  
    [] sc.peerStates[peerID] = "peerStateRemoved" ->
        [err |-> "errUpdateRemovedPeer", res |-> sc]
    
    [] height < sc.peerHeights[peerID] -> (* The peer is corrupt? Remove the peer. *)
        LET res == removePeer(sc, peerID) IN
        [err |-> res.err, res |-> res.res]     
        
    [] OTHER ->
        LET newPeerHeights == [sc.peerHeights EXCEPT ![peerID] = height] IN \* set the peer's height
        LET newPeerStates == [sc.peerStates EXCEPT ![peerID] = "peerStateReady"] IN \* set the peer's state
        LET newMph == maxPeer(newPeerStates, newPeerHeights) IN
        LET res == addNewBlocks(sc, newMph) IN
        LET newSc == [sc EXCEPT 
          !.peerHeights = newPeerHeights, !.peerStates = newPeerStates, 
          !.blocks = res.newBlocks, !.blockStates = res.newBlockStates] IN
        [err |-> noErr, res |-> newSc]
    
nextHeightToSchedule(sc) ==
  LET toBeScheduled ==  {h \in DOMAIN sc.blockStates: sc.blockStates[h] = "blockStateNew"} \cup {ultimateHeight+1} IN
  CHOOSE minH \in toBeScheduled: \A h \in toBeScheduled: h >= minH

getStateAtHeight(sc, h) ==
  IF h < sc.height THEN
    "blockStateProcessed"
  ELSE IF h \in DOMAIN sc.blockStates THEN
    sc.blockStates[h]
  ELSE 
    "blockStateUnknown"

setStateAtHeight(sc, h, blState) ==
    LET newBlockStates ==  [sc.blockStates EXCEPT ![h] = blState] IN
    sc' = [sc EXCEPT !.blockStates = newBlockStates]
    
markPending(sc, peerID, h) ==
  LET blState == getStateAtHeight(sc, h) IN
  IF blState /= "blockStateNew" THEN
    [err |-> "errBadBlockState", res |-> sc]
  ELSE IF peerID \notin DOMAIN sc.peers THEN
    "errPeerNotFound"
  ELSE IF sc.peerStates[peerID] /= "peerStateReady" THEN
    "errBadPeerState"
  ELSE IF h > sc.peerHeights[peerID] THEN
    "errPeerTooShort"
  ELSE
    LET err == setStateAtHeight(sc, h, "blockStatePending") IN \* no idea how to handle functions that don't return anything
    LET newPendingBlocks ==  [sc.pendingBlocks EXCEPT ![h] = peerID] IN
    LET newSc == [sc EXCEPT !.pendingBlocks = newPendingBlocks] IN 
    [err |-> noErr, res |-> newSc]
    
    
allBlocksProcessed(sc) ==
  IF Cardinality(sc.peers) = 0 THEN
    FALSE
  ELSE
    sc.height > maxPeer(sc.peerStates, sc.peerHeights)
           
(* ----------------------------------------------------------------------------------------------*)
(* The behavior of the environment.                                                              *)
(* ----------------------------------------------------------------------------------------------*)

InitEnv ==
  /\ inEvent = noEvent
  /\ envRunning = TRUE

OnGlobalTimeoutTicker ==
  /\ inEvent' = [type |-> "tNoAdvanceExp"]
  /\ envRunning' = FALSE
    
OnTrySchedule == 
  /\ inEvent' = [type |-> "rTrySchedule"]
  /\ UNCHANGED envRunning

OnAddPeerEv ==
  /\ inEvent' \in [type: {"bcAddNewPeer"}, peerID: PeerIDs]
  /\ UNCHANGED envRunning
    
OnStatusResponseEv ==
  \* any status response can come from the blockchain, pick one non-deterministically
  /\ inEvent' \in [type: {"bcStatusResponse"}, peerID: PeerIDs, height: Heights]
  /\ UNCHANGED envRunning
    
OnBlockResponseEv ==
  \* any block response can come from the blockchain, pick one non-deterministically
  /\ inEvent' \in [type: {"bcBlockResponse"}, peerID: PeerIDs, height: Heights, block: Blocks]
  /\ UNCHANGED envRunning

OnRemovePeerEv ==
  \* although peerRemoveEv admits an arbitrary set, we produce just a singleton
  /\ inEvent' \in [type: {"bcRemovePeer"}, peerID: PeerIDs]
  /\ UNCHANGED envRunning
    
OnPcBlockProcessed == 
  /\ inEvent' \in [type: {"pcBlockProcessed"}, peerID: PeerIDs, height: Heights]
  /\ UNCHANGED envRunning

OnPcBlockVerificationFailure == 
  /\ inEvent' \in [type: {"pcBlockVerificationFailure"}, firstPeerID: PeerIDs, secondPeerID: PeerIDs]
  /\ UNCHANGED envRunning

\* messages from scheduler
OnScFinishedEv ==
  /\ inEvent' = [type |-> "tNoAdvanceExp"]
  /\ envRunning' = FALSE \* stop the env
  
NextEnv ==
  \/ OnScFinishedEv
  \/ OnGlobalTimeoutTicker
  \/ OnAddPeerEv
  \*\/ OnTrySchedule
  \/ OnStatusResponseEv
  \*\/ OnBlockResponseEv
  \/ OnRemovePeerEv
  \*\/ OnPcBlockProcessed
  \*\/ OnPcBlockVerificationFailure

(* ----------------------------------------------------------------------------------------------*)
(* The behavior of the scheduler state machine                                                   *)
(* See scheduler.go                                                                              *)
(* https://github.com/tendermint/tendermint/blockchain/v2/scheduler.go                           *)
(* ----------------------------------------------------------------------------------------------*)
InitSc ==
  /\ scRunning = TRUE
  /\ outEvent = noEvent
  /\ \E startHeight \in Heights:
    scheduler = [
      height |-> startHeight,
      peers |-> {},
      peerHeights |-> [p \in PeerIDs |-> None],
      peerStates |-> [p \in PeerIDs |-> "peerStateUnknown"],
      blocks |-> {},
      blockStates |-> [h \in Heights |-> "blockStateUnknown"],
      pendingBlocks |-> [h \in Heights |-> None],
      receivedBlocks |-> [h \in Heights |-> None]]
     
handleAddNewPeer ==
  /\ inEvent.type = "bcAddNewPeer"
  /\ LET res == addPeer(scheduler, inEvent.peerID) IN
     IF res.err /= noErr THEN
       /\ outEvent' = [type |-> "scSchedulerFail", reason |-> res.err]
       /\ UNCHANGED <<scheduler>>
     ELSE
       /\ scheduler' = res.res
       /\ UNCHANGED outEvent
  /\ UNCHANGED scRunning
       
handleRemovePeer ==
  /\ inEvent.type = "bcRemovePeer"
  /\ LET res == removePeer(scheduler, inEvent.peerID) IN
     IF res.err /= noErr THEN
       /\ outEvent' = [type |-> "scSchedulerFail", reason |-> res.err]
       /\ UNCHANGED scheduler
     ELSE
       /\ scheduler' = res.res
       /\ IF allBlocksProcessed(scheduler') THEN
            outEvent' = [type |-> "scFinishedEv", reason |-> "errAfterPeerRemove"]
          ELSE 
            UNCHANGED outEvent
  /\ UNCHANGED scRunning
           
handleStatusResponse ==
  /\ inEvent.type = "bcStatusResponse"
  /\ LET res == setPeerHeight(scheduler, inEvent.peerID, inEvent.height) IN
     IF res.err /= noErr THEN
       /\ outEvent' = [type |-> "scPeerError", peerID |-> inEvent.peerID, reason |-> res.err]
       /\ UNCHANGED scheduler
     ELSE
       /\ scheduler' = res.res
       /\ outEvent' = noEvent
  /\ UNCHANGED scRunning
  
handleTrySchedule == \* every 10 ms, but our spec is asynchronous
    /\ inEvent.type = "rTrySchedule"
    /\ numRequests > Cardinality(DOMAIN scheduler.blockStates)
    /\ LET minH == nextHeightToSchedule(scheduler) IN
       IF minH = None THEN
         outEvent'.type = noEvent
       ELSE
         IF minH = ultimateHeight+1 THEN
           outEvent' = noEvent
         ELSE 
           LET bestPeerID == {p \in scheduler.peers \cup {None}: scheduler.peerHeights[p] >= minH} IN
           IF bestPeerID = None THEN
             outEvent' = noEvent
           ELSE
             LET err == markPending(scheduler, bestPeerID, minH) IN
             IF err /= noErr THEN
               outEvent' = noEvent \* should send some other event here
             ELSE
               outEvent' = [type |-> "scBlockRequest", peerID |-> bestPeerID, height |-> minH]
    
    /\ UNCHANGED scRunning
      
onNoAdvanceExp ==
    /\ inEvent.type = "tNoAdvanceExp"
    /\ scRunning' = FALSE
    /\ UNCHANGED <<outEvent, scheduler>>
       
NextSc ==
  \/ handleStatusResponse
  \/ handleAddNewPeer
  \/ handleRemovePeer
  \/ onNoAdvanceExp

(* ----------------------------------------------------------------------------------------------*)
(* The system is the composition of the environment and the schedule                             *)
(* ----------------------------------------------------------------------------------------------*)
Init == turn = "environment" /\ InitEnv /\ InitSc

FlipTurn == 
  turn' = (
    IF turn = "scheduler" THEN 
      "environment" 
    ELSE
      "scheduler"
  ) 

Next == \* scheduler and environment alternate their steps (synchronous composition introduces more states)
  /\ FlipTurn
  /\ IF turn = "scheduler" THEN 
       /\ NextSc
       /\ inEvent' = noEvent
       /\ UNCHANGED envRunning
     ELSE
       /\ NextEnv
       /\ outEvent' = noEvent
       /\ UNCHANGED <<scRunning, scheduler>>  

(* ----------------------------------------------------------------------------------------------*)
(* Expected properties                                                                           *)
(* ----------------------------------------------------------------------------------------------*)

TypeOK ==
    /\ turn \in {"scheduler", "environment"}
    /\ inEvent \in InEvents
    /\ envRunning \in BOOLEAN
    /\ outEvent \in OutEvents
    /\ scheduler \in [
         height: Heights \cup {ultimateHeight + 1},
         peers: SUBSET PeerIDs,
         peerHeights: [PeerIDs -> Heights \cup {None}],
         peerStates: [PeerIDs -> PeerStates],
         blocks: SUBSET Heights,
         blockStates: [Heights -> BlockStates],
         pendingBlocks: [Heights -> PeerIDs \cup {None}],
         receivedBlocks: [Heights -> PeerIDs \cup {None}]
       ]
       
TerminationWhenNoAdvance ==
  (WF_turn(FlipTurn) /\ <> (inEvent.type = "tNoAdvanceExp"))
    => <> ~scRunning
    
=============================================================================
