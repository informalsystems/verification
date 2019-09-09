-------------------------------- MODULE fastsync --------------------------------
(*
 A specification of the fast sync finite-state machine that is introduced in:
 
 https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/docs/spec/reactors/block_sync/bcv1/impl-v1.md
 
 We are modeling three important ingredients:
    - a non-faulty FSM that does fast sync
    - a block pool that maintains the blocks that FSM receives from the peers, and
    - two reactors: a chaotic one and one which does some checks as in the implementation
    
 This specification focuses on the events that are received and produced by the FSM from the reactor.
 Importantly, we do not specify neither communication between the FSM and the peers,
 nor communication between the reactor and the peers.
*)

EXTENDS Integers, FiniteSets

\* the protocol parameters
CONSTANTS
    PeerIDs,        \* potential peer ids, a set of integers, e.g., 0..2
    maxHeight,      \* the maximum height, an integer, e.g., 3
    numRequests     \* the number of requests made per batch, e.g., 2

\* a few values
None == -1          \* an undefined value
Heights == 1..maxHeight \* potential heights

\* basic stuff
Min(a, b) == IF a < b THEN a ELSE b

VARIABLE  turn          \* who makes a step: the FSM or the Reactor

\* the state of the reactor: 
VARIABLES inEvent,       \* an event from the reactor to the FSM
          reactorRunning \* a Boolean, negation of stopProcessing in the implementation
                    
\* the state of the FSM: https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/blockchain/v1/reactor_fsm.go
VARIABLES state,         \* an FSM state
          outEvent       \* an event from the FSM to the reactor

\* the block pool: https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/blockchain/v1/pool.go
VARIABLE blockPool
    (*
       blockPool is a record that contains: 
         height: Int,
            height of the next block to collect
         peers: {Int},
            the set of active peers, not known to be faulty
         peerHeights: [PeerId -> Height],
            a map to collect the peer responses about their heights 
         maxPeerHeight: Int,
            the maximal height among all active peers
         blocks: [Height -> PeerID],
            a map to collect the peers that have to deliver the blocks (one peer per block)
         nextRequestHeight: Int,
            the height at which the next request is going to be made
         ghostReceivedBlocks: {Int},
            a set of the heights for which the correct blocks were received, not in the implementation 
         ghostProcessedHeights:
            {Int}, a set of the heights that have been processed successfully, not in the implementation 
         \* the implementation contains plannedRequests that we omit here
    *)
    
vars == <<turn, inEvent, reactorRunning, state, outEvent, blockPool>>    

(* The control states of the FSM *)
States == { "init", "waitForPeer", "waitForBlock", "finished" }

(* From the FSM's point of view, a block is completely abstract. We only know whether it is valid or not. *)
Blocks == [ valid: BOOLEAN ]
InvalidBlock == [ valid |-> FALSE]

\* These are the types of input events that can be produced by the reactor to the FSM
InEventTypes == { "startFSMEv", "statusResponseEv", "blockResponseEv", "stateTimeoutEv",
                  "peerRemoveEv", "processedBlockEv", "makeRequestsEv", "stopFSMEv" }

\* These are all possible events that can be produced by the reactor as the input to FSM.
\* Mimicking a combination of bReactorEvent and bReactorEventData.
InEvents ==
    [ type: {"startFSMEv", "stopFSMEv"} ]
    \cup
    [ type: {"statusResponseEv"}, peerID: PeerIDs, height: Heights]
    \cup
    [ type: {"blockResponseEv"}, peerID: PeerIDs, height: Heights, block: Blocks ]
    \cup
    [ type: {"stateTimeoutEv"}, stateName: States ]
    \cup
    [ type: {"peerRemoveEv"}, peerIDs: SUBSET PeerIDs \ {} ] \* NOTE: peerIDs is a set of ids
    \cup
    [ type: {"processedBlockEv"}, err: BOOLEAN ]
    \cup
    [ type: {"makeRequestsEv"}, maxNumRequests: {numRequests} ]
    
\* These are the types of the output events that can be produced by the FSM to the reactor
OutEventTypes == { "NoEvent", "sendStatusRequest", "sendBlockRequest",
                   "sendPeerError", "resetStateTimer", "switchToConsensus" }
                   
\* These are all possible events that can be produced by the FSM to reactor, reactor_fsm.go:354-360
\* In contrast to the implementation, we group the requests together.
OutEvents ==
    [ type: {"NoEvent", "sendStatusRequest", "switchToConsensus"}]
    \cup
    [ type: {"sendBlockRequest"}, reqs: [peerID: PeerIDs, height: Heights]]
    \cup
    [ type: {"sendPeerError"}, peerID: SUBSET PeerIDs] \* we omit the error field 
    \cup
    [ type: {"resetStateTimer"}] \* we omit the timer and timeout fields

\* When FSM produces no event, it emits NoEvent    
NoEvent == [type |-> "NoEvent"]                       


(* ------------------------------------------------------------------------------------------------*)
(* The behavior of the block pool, which keeps track of peers, block requests, and block responses *)
(* See pool.go                                                                                     *)
(* ------------------------------------------------------------------------------------------------*)

\* Find the maximal height among the (known) heights of the active peers
FindMaxPeerHeight(activePeers, heights) ==
    IF activePeers = {}
    THEN 0 \* no peers, just return 0
    ELSE CHOOSE max \in { heights[p] : p \in activePeers }:
            \A p \in activePeers: heights[p] <= max \* max is the maximum

\* remove several peers at once, e.g., see pool.removeShortPeers
RemovePeers(pool, ids) ==
    \* remove the peers
    LET newPeers == pool.peers \ ids IN
    \* remove all block requests to peerId, see pool.RemovePeer and pool.rescheduleRequest(peerId, h)
    LET newBlocks == [h \in Heights |-> IF pool.blocks[h] \in ids THEN None ELSE pool.blocks[h]] IN
    \* update the maximum height 
    LET newMph == FindMaxPeerHeight(newPeers, pool.peerHeights) IN
    \* adjust the height of the next request, if it has lowered
    LET newNrh == Min(newMph + 1, pool.nextRequestHeight) IN
    [ pool EXCEPT !.peers = newPeers, !.blocks = newBlocks,
                  !.maxPeerHeight = newMph, !.nextRequestHeight = newNrh]

\* pool.removeShortPeers
RemoveShortPeers(pool, h) ==
    LET ShortPeers ==
        {p \in PeerIDs: pool.peerHeights[p] /= None /\ pool.peerHeights[p] < h}
    IN
    RemovePeers(pool, ShortPeers)

\* pool.removeBadPeers calls removeShortPeers and removes the peers whose rate is bad.
\* As we are not checking the rate here, we are just removing the short peers.
\* Alternatively, we could drop the short peers and an arbitrary subset of the peers.
RemoveBadPeers(pool) == RemoveShortPeers(pool, pool.height)

\* The peer has not been removed, nor invalid, nor the block is corrupt
IsPeerAtHeight(pool, p, h) ==
    /\ p \in pool.peers                 \* the peer is active
    /\ h \in DOMAIN pool.blocks         \* the height has been assigned a peer
    /\ p = pool.blocks[h]               \* the block should have been sent by the peer p
    /\ h \in pool.ghostReceivedBlocks   \* the block has been received
       
\* A summary of InvalidateFirstTwoBlocks
InvalidateFirstTwoBlocks(pool, p1, p2) ==
    LET atHeightOrNone(p, ph) ==
        \/ IsPeerAtHeight(pool, p, ph)
        \/ p = None /\ \A q \in PeerIDs: ~IsPeerAtHeight(pool, q, ph)
    IN
    IF (atHeightOrNone(p1, pool.height) /\ atHeightOrNone(p2, pool.height + 1))
    THEN RemovePeers(pool, {p1, p2})
    ELSE pool

\* Update the peer height (and add the peer if it is not in the set yet)                    
UpdatePeer(pool, peerId, height) ==
    IF peerId \notin pool.peers
    THEN IF height < pool.height
        THEN pool (* peer height too small. Ignore. *)
        ELSE (* the common case. Add the peer and set its height. *)
            LET newPeers == pool.peers \cup { peerId } \* add the peer, if it does not exist
                newPh == [pool.peerHeights EXCEPT ![peerId] = height] \* set the peer's height
                newMph == FindMaxPeerHeight(newPeers, newPh)  \* find max peer height
            IN
            [pool EXCEPT !.peers = newPeers, !.peerHeights = newPh, !.maxPeerHeight = newMph]
    ELSE IF height < pool.peerHeights[peerId]
        THEN (* The peer is corrupt? Remove the peer. *)
            RemovePeers(pool, {peerId}) \* may lower nextRequestHeight and update blocks
        ELSE (* Update the peer height *)
            LET newPh == [pool.peerHeights EXCEPT ![peerId] = height] IN \* set the peer's height
            LET newMph == FindMaxPeerHeight(pool.peers, newPh) IN \* find max peer height
            [pool EXCEPT !.peerHeights = newPh, !.maxPeerHeight = newMph]

(* ------------------------------------------------------------------------------------------------ *)
(* The behavior of the reactor.See reactor.go                                                       *)
(*                                                                                                  *)
(* There are two kinds of reactors:                                                                 *)
(*   1. NextChaosReactor produces all possible events in any order.                                 *) 
(*   2. NextReactor follows the logic of reactor.go.                                                *) 
(* ------------------------------------------------------------------------------------------------ *)

\* both reactors start by producing the event for FSM to start
InitReactor ==
    /\ inEvent = [type |-> "startFSMEv"]
    /\ reactorRunning = TRUE

(* The chaotic reactor *)
NextChaosReactor ==
    /\ reactorRunning' \in BOOLEAN \* the reactor can stop and start again any time
    /\  IF reactorRunning
        THEN inEvent' \in InEvents \* the reactor produces an arbitrary input event to FSM
        ELSE inEvent' = NoEvent

(* The benigh reactor that tries to follow the logic of reactor.go *)
\* the following actions are defined in reactor.poolRoutine
OnSendBlockRequestTicker == \* every 10 ms, but our spec is asynchronous
    /\  LET unprocessedBlocks ==
            { h \in DOMAIN blockPool.blocks: blockPool.blocks[h] /= None}
        IN
        \* reactor_fsm.NeedsBlocks
        state = "waitForBlock" /\ numRequests > Cardinality(unprocessedBlocks)
    /\ inEvent' = [ type |-> "makeRequestsEv", maxNumRequests |-> numRequests ]
    /\ UNCHANGED reactorRunning
    
OnStatusResponseEv ==
    \* any status response can come from the blockchain, pick one non-deterministically
    /\ inEvent' \in [ type: {"statusResponseEv"}, peerID: PeerIDs, height: Heights ]
    /\ UNCHANGED reactorRunning
    
OnBlockResponseEv ==
    \* any block response can come from the blockchain, pick one non-deterministically
    /\ inEvent' \in [ type: {"blockResponseEv"}, peerID: PeerIDs, height: Heights, block: Blocks ]
    /\ UNCHANGED reactorRunning

OnRemovePeerEv ==
    \* although peerRemoveEv admits an arbitrary set, we produce just a singleton
    /\ inEvent' \in [ type: {"peerRemoveEv"}, peerIDs: { {p} : p \in PeerIDs } ]
    /\ UNCHANGED reactorRunning

OnPeerErrorEv ==
    \* XXX: we would need a queue instead of a single outEvent.
    \* However, this is compensated by OnPeerRemoveEv.
    /\ outEvent.type = "peerErrorEv"
    /\ inEvent' = [ type |-> "peerRemoveEv", peerIDs |-> {outEvent.peerIDs} ]
    /\ UNCHANGED reactorRunning
    
\* reactor.processBlocksRoutine
OnProcessReceivedBlockTicker == \* every 10 ms, again, no precise time here
    \* a block could be processed only if there are two blocks to do verification
    /\ LET h == blockPool.height IN
        /\ { h, h + 1 } \subseteq DOMAIN blockPool.blocks
        /\ blockPool.blocks[h] /= None /\ h \in blockPool.ghostReceivedBlocks
        /\ blockPool.blocks[h + 1] /= None /\ h + 1 \in blockPool.ghostReceivedBlocks
    /\ inEvent' \in [ type: {"processedBlockEv"}, err: BOOLEAN ]
    /\ UNCHANGED reactorRunning

OnStateTimeoutEv == \* after XXX ms if the FSM resides in the same state, no precise time
    /\ inEvent' = [type |-> "stateTimeoutEv", stateName |-> state]
    /\ UNCHANGED reactorRunning

\* messages from FSM
OnSyncFinishedEv ==
    /\ outEvent.type = "switchToConsensus"
    /\ inEvent' = NoEvent
    /\ reactorRunning' = FALSE \* stop the reactor

\* We omit reaction on StatusUpdateTicker, as it is supposed to send a message to the blockchain, not FSM    
\* OnStatusUpdateTicker == \* every 10 ms
\*    TRUE \* the implementation broadcasts the request to blockchain, we do nothing

NextReactor ==
    \/ OnSendBlockRequestTicker
    \/ OnStatusResponseEv
    \/ OnBlockResponseEv
    \/ OnRemovePeerEv
    \/ OnPeerErrorEv
    \/ OnProcessReceivedBlockTicker
    \/ OnStateTimeoutEv
    \/ OnSyncFinishedEv

(* ------------------------------------------------------------------------------------------------ *)
(* The behavior of the fast-sync state machine                                                      *)
(* See reactor_fsm.go                                                                               *)
(* ------------------------------------------------------------------------------------------------ *)
InitFSM ==
    /\ state = "init"
    /\ outEvent = NoEvent
    /\ \E startHeight \in Heights:
         blockPool = [
            height |-> startHeight,
            peers |-> {},
            peerHeights |-> [ p \in PeerIDs |-> None ],     \* no peer height is known
            maxPeerHeight |-> 0,
            blocks |-> [ h \in Heights |-> None ],          \* no peer has sent a block
            nextRequestHeight |-> startHeight,
            ghostReceivedBlocks |-> 0 .. (startHeight - 1),
            ghostProcessedHeights |-> 0 .. (startHeight - 1)
         ]

    
\* the actions that are shared among several states

\* stop the FSM
OnStopFSM ==
    /\ state' = "finished"
    /\ inEvent.type = "stopFSMEv"
    /\ outEvent' = NoEvent
    /\ UNCHANGED blockPool
    \* stateTimer.Stop() ?   

\* respond to a timeout that is generated for a state different from the current one
OnTimeoutOtherState ==
    /\ inEvent.type = "stateTimeoutEv"
    /\ inEvent.stateName /= state
    /\ outEvent' = NoEvent
    /\ UNCHANGED <<state, blockPool>>

\* how to respond to an event that should not occur in the current state    
OnUnprocessedEvent(EventTypes) ==
    /\ inEvent.type \notin EventTypes
    /\ outEvent' = NoEvent
    /\ UNCHANGED <<state, blockPool>>

\* when in state init
InInit ==
    /\ state = "init"
    /\  IF inEvent.type = "startFSMEv"
        THEN  /\ state' = "waitForPeer"
              /\ outEvent' = [type |-> "sendStatusRequest"]
              /\ UNCHANGED blockPool
        ELSE  /\ outEvent' = NoEvent
              /\ UNCHANGED <<state, blockPool>>

(* What happens in the state waitForPeer *)
\* the only interesting event -- a peer has responded
OnStatusResponseInWaitForPeer ==
    /\ inEvent.type = "statusResponseEv"
    /\ blockPool' = UpdatePeer(blockPool, inEvent.peerID, inEvent.height)
    /\ state' = IF blockPool'.peers /= {} THEN "waitForBlock" ELSE state
    /\ outEvent' = NoEvent 
    \* TODO: StopTimer? 

OnTimeoutInWaitForPeer ==
    /\ inEvent.type = "stateTimeoutEv"
    /\ state' = "finished"
    /\ outEvent' = NoEvent \* TODO: resetTimer instead? 
    /\ UNCHANGED blockPool
    
InWaitForPeer ==
    /\ state = "waitForPeer"
    /\  \/ OnStatusResponseInWaitForPeer
        \/ OnStopFSM
        \/ OnTimeoutInWaitForPeer
        \/ OnTimeoutOtherState
        \/ OnUnprocessedEvent({"stopFSMEv", "statusResponseEv", "stateTimeoutEv"})

(* What happens in the state waitForBlock *)

\* this logic is common to several actions
ChooseStateInWaitForBlock(pool) ==
      IF pool.peers = {}
      THEN "waitForPeer"
      ELSE IF pool.height >= pool.maxPeerHeight
           THEN "finished"
           ELSE "waitForBlock"


\* Produce requests for blocks. See pool.MakeNextRequests and pool.MakeRequestBatch     
OnMakeRequestsInWaitForBlock ==
    /\ inEvent.type = "makeRequestsEv"
    \* pool.MakeRequestBatch calls removeBadPeers first
    /\  LET cleanPool == RemoveBadPeers(blockPool) IN
        LET pendingBlocks == {h \in DOMAIN cleanPool.blocks: cleanPool.blocks[h] /= None} IN
        LET numPendingBlocks == Cardinality(pendingBlocks) IN \* len(blocks) in pool.go   
        \*  compute the next request height, see pool.go:194-201
        LET newNrh == Min(cleanPool.maxPeerHeight,
                          cleanPool.nextRequestHeight + inEvent.maxNumRequests - numPendingBlocks) IN
        LET heights == cleanPool.nextRequestHeight..newNrh - 1 IN
        \* for each height h, assign a peer whose height is not lower than h
        LET newBlocks ==
              [h \in Heights |->
                IF h \in heights
                THEN CHOOSE p \in cleanPool.peers: cleanPool.peerHeights[p] >= h
                ELSE cleanPool.blocks[h] \* keep the old value
              ]
        IN
           \* group all block requests into one output event
        /\ outEvent' = [type |-> "sendBlockRequest",
                        reqs |-> { [peerID |-> newBlocks[h],
                                    height |-> h] : h \in heights }]
        /\ blockPool' =
            [cleanPool EXCEPT !.blocks = newBlocks, !.nextRequestHeight = newNrh]                            
        /\ state' = "waitForBlock"
        \* TODO: the implementation requires !(peer.NumPendingBlockRequests >= maxRequestsPerPeer)
        \* TODO: the implementation may report errSendQueueFull
        \* TODO: peer.RequestSent(height)
             
\* a peer responded with its height
OnStatusResponseInWaitForBlock ==
    /\ inEvent.type = "statusResponseEv"
    /\ blockPool' = UpdatePeer(blockPool, inEvent.peerID, inEvent.height)
    /\ state' = ChooseStateInWaitForBlock(blockPool')
    /\ outEvent' = NoEvent

\* a peer responded with a block
OnBlockResponseInWaitForBlock ==
    /\ inEvent.type = "blockResponseEv"
    /\  IF (~inEvent.block.valid
            \/ inEvent.height \notin DOMAIN blockPool.blocks
            \/ inEvent.peerID /= blockPool.blocks[inEvent.height]
            \/ inEvent.peerID \notin blockPool.peers)
        \* A block was received that was unsolicited, from unexpected peer, or that we already have it
        THEN  /\ blockPool' = RemovePeers(blockPool, {inEvent.peerID})
              /\ outEvent' = [type |-> "sendPeerError", peerIDs |-> {inEvent.peerID}]
        \* an OK block, the implementation adds it to the store
        ELSE  /\ outEvent' = NoEvent
              /\ blockPool' = [blockPool EXCEPT !.ghostReceivedBlocks = @ \cup {inEvent.height}]
    /\ state' = IF blockPool'.peers = {} THEN "waitForPeer" ELSE "waitForBlock"

\* the block at the current height has been processed
OnProcessedBlockInWaitForBlock ==
    /\ inEvent.type = "processedBlockEv"
    /\  IF blockPool.blocks[blockPool.height] = None
            \/ (blockPool.height + 1 \in DOMAIN blockPool.blocks
                 /\ blockPool.blocks[blockPool.height + 1] = None)
        THEN outEvent' = NoEvent /\ UNCHANGED blockPool
        ELSE IF inEvent.err
            THEN \* invalidate the blocks at heights h and h+1, if possible
              \E p1, p2 \in PeerIDs \cup {None}:
                /\ blockPool' = InvalidateFirstTwoBlocks(blockPool, p1, p2)
                /\ outEvent' = [ type |-> "sendPeerError",
                                 peerIDs |-> { p \in {p1, p2}: p /= None } ]
            ELSE \* pool.ProcessedCurrentHeightBlock
              /\ outEvent' = NoEvent
                 \* remove the block at the pool height
              /\ LET newBlocks == [blockPool.blocks EXCEPT ![blockPool.height] = None] IN
                 LET newHeight == blockPool.height + 1 IN       \* advance the pool height
                 \* record the processed height for checking the temporal properties
                 LET newGph == blockPool.ghostProcessedHeights \cup {blockPool.height} IN
                 LET newPool == [blockPool EXCEPT
                    !.blocks = newBlocks, !.height = newHeight, !.ghostProcessedHeights = newGph ]
                 IN
                 blockPool' = RemoveShortPeers(newPool, newHeight)
              \* pool.peers[peerID].RemoveBlock(pool.Height)
              \* TODO: resetStateTimer?
    /\ state' = IF blockPool'.height >= blockPool'.maxPeerHeight THEN "finished" ELSE "waitForBlock"

\* a peer was disconnected or produced an error    
OnPeerRemoveInWaitForBlock ==
    /\ inEvent.type = "peerRemoveEv"
    /\ blockPool' = RemovePeers(blockPool, inEvent.peerIDs)
    /\ state' = ChooseStateInWaitForBlock(blockPool')
    /\ outEvent' = NoEvent

\* a timeout when waiting for a block
OnTimeoutInWaitForBlock ==
    /\ inEvent.type = "stateTimeoutEv"
    /\ inEvent.stateName = state
    \* below we summarize pool.RemovePeerAtCurrentHeights
    /\ \/ \E p \in blockPool.peers:
          /\ IsPeerAtHeight(blockPool, p, blockPool.height)
          /\ blockPool' = RemovePeers(blockPool, {p}) \* remove the peer at current height
       \/ /\ \A p \in blockPool.peers: ~IsPeerAtHeight(blockPool, p, blockPool.height)
          /\ \/ \E q \in blockPool.peers:
                /\ IsPeerAtHeight(blockPool, q, blockPool.height + 1)
                /\ blockPool' = RemovePeers(blockPool, {q})    \* remove the peer at height + 1
             \* remove no peers, are we stuck here?
             \/ /\ \A q \in blockPool.peers: ~IsPeerAtHeight(blockPool, q, blockPool.height + 1)
                /\ UNCHANGED blockPool 
    \* resetStateTimer?
    /\ outEvent' = NoEvent
    /\ state' = ChooseStateInWaitForBlock(blockPool')
        
\* when in state waitForBlock        
InWaitForBlock ==
    /\ state = "waitForBlock"
    /\  \/ OnMakeRequestsInWaitForBlock
        \/ OnStatusResponseInWaitForBlock             
        \/ OnBlockResponseInWaitForBlock 
        \/ OnProcessedBlockInWaitForBlock
        \/ OnPeerRemoveInWaitForBlock
        \/ OnTimeoutInWaitForBlock
        \/ OnTimeoutOtherState
        \/ OnStopFSM
        \/ OnUnprocessedEvent(InEventTypes \ {"startFSMEv"})
       
\* when finished        
InFinished ==
    /\ state = "finished"
    /\ outEvent' = [type |-> "switchToConsensus"]
    /\ UNCHANGED <<state, blockPool>>

\* Finally, this is how a transition by FSM looks like
NextFSM ==
    \/ InInit
    \/ InWaitForPeer
    \/ InWaitForBlock
    \/ InFinished

(* ------------------------------------------------------------------------------------------------*)
(* The system is the composition of the non-deterministic reactor and the FSM                      *)
(* ------------------------------------------------------------------------------------------------*)
Init == turn = "FSM" /\ InitReactor /\ InitFSM

FlipTurn == turn' = (IF turn = "FSM" THEN "Reactor" ELSE "FSM") 

Next == \* FSM and Reactor alternate their steps (synchronous composition introduces more states)
    /\ FlipTurn
    /\  IF turn = "FSM"
        THEN /\ NextFSM
             /\ inEvent' = NoEvent /\ UNCHANGED reactorRunning
        ELSE /\ NextReactor
             /\ outEvent' = NoEvent /\ UNCHANGED <<state, blockPool>>  

(* ------------------------------------------------------------------------------------------------*)
(* Expected properties *)
(* ------------------------------------------------------------------------------------------------*)
\* a sample property that triggers a counterexample in TLC
NeverFinishAtMax == [] (state = "finished" => blockPool.height < blockPool.maxPeerHeight)

\* always finish at maximum height (we exclude timeouts that trivially violate the property)
AlwaysFinishAtMax ==
   ([] (inEvent.type \notin {"stopFSMEv", "stateTimeoutEv"}))
     => [] (state = "finished" => blockPool.height = blockPool.maxPeerHeight)

\* always finish at the height below or equal to the maximum height (timeouts excluded)
NeverFinishAbovePeerHeight ==
   ([] (inEvent.type \notin {"stopFSMEv", "stateTimeoutEv"}))
    => [] (state = "finished" => (blockPool.height <= blockPool.maxPeerHeight))

\* This seems to be the safety requirement:
\*   all blocks up to poolHeight have been processed 
Safety == 0..blockPool.height - 1 \subseteq blockPool.ghostProcessedHeights

\* before specifying liveness, we have to write constraints on the reactor events
\* a good event
NoFailuresAndTimeouts ==
    \* no timeouts, no peer removal
    /\ inEvent.type \notin { "stateTimeoutEv", "peerRemoveEv" }
    \* no invalid blocks
    /\ inEvent.type = "blockResponseEv" => inEvent.block.valid
    /\ inEvent.type = "processedBlockEv" => ~inEvent.err
    
\* the reactor can always kill progress by sending updates or useless messages
FiniteResponse ==
    <>[] (inEvent.type
         \notin { "statusResponseEv", "startFSMEv", "stopFSMEv", "blockResponseEv",
                  "processedBlockEv", "makeRequestsEv"})
    
\* A liveness property that tells us that the protocol should terminate in the good case.
\* (This property holds but it seems to be quite restrictive.)
\* WF_turn(FlipTurn) makes sure that FSM and Reactor keep alternating.
GoodTermination ==
  (WF_turn(FlipTurn) /\ []NoFailuresAndTimeouts /\ FiniteResponse)
     => <>(state = "finished" /\ blockPool.height = blockPool.maxPeerHeight)

(* ------------------------------------------------------------------------------------------------*)
(* Questions in the back of my head *)
(* ------------------------------------------------------------------------------------------------*)

(*
  Q1. What if a faulty peer is reporting a very large height? The protocol is stuck forever?
  
  Q2. I do not see why pool.makeRequestBatch cannot produce duplicate heights in pool.plannedRequests.
  
  Q3. Why don't you clean up pool.plannedRequests in pool.go:180?  
 *)


=============================================================================
\* Modification History
\* Last modified Mon Sep 09 22:39:58 CEST 2019 by igor
\* Last modified Thu Aug 01 13:06:29 CEST 2019 by widder
\* Created Fri Jun 28 20:08:59 CEST 2019 by igor
