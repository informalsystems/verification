-------------------------------- MODULE fastsync --------------------------------
(*
 A specification of the fast sync finite-state machine that is introduced in:
 
 https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/docs/spec/reactors/block_sync/bcv1/impl-v1.md
 
 We are modeling three important ingredients:
    - a non-faulty FSM that does fast sync
    - a block pool that maintains the blocks that FSM receives from the peers, and
    - the reactor, which may be completely chaotic.
    
 This specification focuses on the events that are received and produced by the FSM from the reactor.
*)

EXTENDS Integers, FiniteSets

(*
 Constants that are introduced for model checking purposes.
 In the future, we may want to introduce them as CONSTANTS.
 *)
None == -1          \* an undefined value
PeerIDs == 0..2     \* potential peer ids
maxHeight == 5      \* the maximum height
Heights == 0..maxHeight \* potential heights
NumRequests == 3    \* the number of requests made per batch

\* basic stuff
Min(a, b) == IF a < b THEN a ELSE b

\* the state of the reactor: 
VARIABLES inEvent       \* an event from the reactor to the FSM
                    
\* the state of the FSM: https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/blockchain/v1/reactor_fsm.go
VARIABLE state,         \* an FSM state
         outEvent       \* an event from the FSM to the reactor

\* the block pool: https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/blockchain/v1/pool.go
VARIABLE peers,         \* the set of active peers, not known to be faulty
         peerHeights,   \* PeerId -> Height to collect the peer responses about their heights 
         blocks,        \* Height -> PeerID to collect the peers that have to deliver the blocks (one peer per block)
         poolHeight,    \* height of the next block to collect
         maxPeerHeight, \* maximum height of all peers
         nextRequestHeight,     \* the height at which the next request is going to be made
         ghostProcessedHeights   \* a ghost variable to collect the heights that have been processed successfully 
         \* the implementation contains plannedRequests that we omit here
         
\* the variables of the block pool, to be used as UNCHANGED poolVars
poolVars == <<peers, peerHeights, blocks,
              poolHeight, maxPeerHeight, nextRequestHeight, ghostProcessedHeights>>

(* The potential states of the FSM *)
States == { "init", "waitForPeer", "waitForBlock", "finished" }

(* Currently, a block is completely abstract. We only know whether it is valid or not. *)
Blocks == [ valid: BOOLEAN ]
InvalidBlock == [ valid |-> FALSE]

\* These are the types of input events that can be produced by the reactor to the FSM
InEventTypes == { "startFSMEv", "statusResponseEv", "blockResponseEv", "stateTimeoutEv",
                "peerRemoveEv", "processedBlockEv", "makeRequestEv", "stopFSMEv" }

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
    [ type: {"peerRemoveEv"}, peerID: PeerIDs, err: BOOLEAN ]
    \cup
    [ type: {"processedBlockEv"}, err: BOOLEAN ]
    \cup
    [ type: {"makeRequestEv"}, maxNumRequests: {NumRequests} ]
    
\* These are the types of the output events that can be produced by the FSM to the reactor
OutEventTypes == { "NoEvent", "sendStatusRequest", "sendBlockRequest",
                   "sendPeerError", "resetStateTimer", "switchToConsensus" }
                   
\* These are all possible events that can be produced by the FSM to reactor.
\* In contrast to the implementation, we group the requests together.
OutEvents ==
    [ type: {"NoEvent", "sendStatusRequest", "switchToConsensus"}]
    \cup
    \* 
    [ type: {"sendBlockRequest"}, reqs: [peerID: PeerIDs, height: Heights]]
    \cup
    [ type: {"sendPeerError"}, peerID: SUBSET PeerIDs] \* we omit the error field 
    \cup
    [ type: {"resetStateTimer"}] \* we omit the timer and timeout fields
    
NoEvent == [type |-> "NoEvent"]                       

(* ------------------------------------------------------------------------------------------------ *)
(* The behavior of the reactor. In this specification, the reactor keeps generating events.         *)
(* See reactor.go                                                                                   *)
(* ------------------------------------------------------------------------------------------------ *)
InitReactor ==
    inEvent = [type |-> "startFSMEv"]
    
NextReactor ==
    inEvent' \in InEvents \* the reactor produces an arbitrary input event to FSM

(* ------------------------------------------------------------------------------------------------*)
(* The behavior of the block pool, which keeps track of peers, block requests, and block responses *)
(* See pool.go                                                                                     *)
(* ------------------------------------------------------------------------------------------------*)
NoPeers == peers = {}
SomePeers == peers /= {}

\* Find the maximal height among the (known) heights of the active peers
UpdateMaxPeerHeight(activePeers, heights) ==
    maxPeerHeight' =
        IF activePeers = {}
        THEN 0 \* no peers, just return 0
        ELSE CHOOSE max \in { heights[p] : p \in activePeers }:
                \A p \in activePeers: heights[p] <= max \* max is the maximum

\* remove several peers at once, e.g., see pool.removeShortPeers
RemoveManyPeers(ids) ==
    /\ peers' = peers \ ids         \* remove the peers
    /\ UNCHANGED peerHeights        \* keep the heights, as the height of the removed peers is never used
    \* remove all block requests to peerId, see pool.RemovePeer and pool.rescheduleRequest(peerId, h)
    /\ blocks' = [h \in Heights |-> IF blocks[h] \in ids THEN None ELSE blocks[h]]
    \* update the maximum height 
    /\ UpdateMaxPeerHeight(peers', peerHeights) \* the maximum height may lower
    \* adjust the height of the next request, if it has lowered
    /\ nextRequestHeight' = Min(maxPeerHeight' + 1, nextRequestHeight)

\* pool.removeShortPeers
RemoveShortPeers(h) ==
    RemoveManyPeers({p \in PeerIDs: peerHeights[p] /= None /\ peerHeights[p] < h})

\* pool.removeBadPeers calls removeShortPeers and removes the peers whose rate is bad.
\* As we are not checking the rate here, we are just removing the short peers.
RemoveBadPeers(h) == RemoveShortPeers(h)

\* Remove a peer from the set of active peers, see pool.RemovePeer                
RemovePeer(peerId) == RemoveManyPeers({peerId})

\* The peer has not been removed, nor invalid, nor the block is corrupt
IsPeerAtHeight(p, h) ==
    p \in peers /\ h \in DOMAIN blocks /\ p = blocks[h]
       
\* A summary of InvalidateFirstTwoBlocks
InvalidateFirstTwoBlocks(p1, p2) ==
    \* find the peers at height and height + 1, if possible
    /\ \/ IsPeerAtHeight(p1, poolHeight)
       \/ p1 = None /\ \A q \in PeerIDs: ~IsPeerAtHeight(q, poolHeight)
    /\ \/ IsPeerAtHeight(p2, poolHeight + 1)
       \/ p2 = None /\ \A q \in PeerIDs: ~IsPeerAtHeight(q, poolHeight + 1)
    /\ RemoveManyPeers({p1, p2})

\* Update the peer height (and add if it is not in the set)                    
UpdatePeer(peerId, height) ==
    CASE height >= poolHeight
        -> (* the common case. Add or keep the peer and update its height. *)
        /\ peers' = peers \cup { peerId } \* add the peer, if it does not exist
        /\ peerHeights' = [peerHeights EXCEPT ![peerId] = height] \* set the peer's height
        /\ UpdateMaxPeerHeight(peers', peerHeights')
        /\ UNCHANGED <<nextRequestHeight, blocks>>
        
      [] peerId \notin peers /\ height < poolHeight
        -> (* peer height too small. Ignore. *)
        UNCHANGED <<peers, peerHeights, maxPeerHeight, nextRequestHeight, blocks>>
        
      [] peerId \in peers /\ height < poolHeight
        -> (* the peer is corrupt? Remove the peer. *)
        RemovePeer(peerId)  \* may lower nextRequestHeight and updates blocks


(* ------------------------------------------------------------------------------------------------ *)
(* The behavior of the fast-sync state machine                                                      *)
(* See reactor_fsm.go                                                                               *)
(* ------------------------------------------------------------------------------------------------ *)
InitFsm ==
    /\ state = "init"
    /\ outEvent = NoEvent
    /\ peers = {}
    /\ poolHeight = 0
    /\ maxPeerHeight = 0
    /\ peerHeights = [ p \in PeerIDs |-> None ]     \* no peer height is known
    /\ blocks = [ h \in Heights |-> None ]          \* no peer has sent a block
    /\ nextRequestHeight = 0
    /\ ghostProcessedHeights = {}

\* when in state init
InInit ==
    /\ state = "init"
    /\ \/ /\ inEvent.type = "startFSMEv"
          /\ state' = "waitForPeer"
          /\ outEvent' = [type |-> "sendStatusRequest"]
          /\ UNCHANGED poolVars
          
       \/ /\ inEvent.type /= "startFSMEv"
          /\ outEvent' = NoEvent
          /\ UNCHANGED <<state, poolVars>>

(* What happens in the state waitForPeer *)

InWaitForPeer ==
    /\ state = "waitForPeer"
    /\  CASE inEvent.type = "statusResponseEv"
             -> /\ UpdatePeer(inEvent.peerID, inEvent.height)
                /\ state' = IF SomePeers' THEN "waitForBlock" ELSE state
                /\ outEvent' = NoEvent 
                /\ UNCHANGED <<poolHeight, ghostProcessedHeights>>
                \* TODO: StopTimer? 
                
          [] inEvent.type = "stateTimeoutEv"
             -> /\ state' = IF inEvent.stateName = state THEN "finished" ELSE state
                /\ outEvent' = NoEvent \* TODO: resetTimer instead? 
                /\ UNCHANGED poolVars
             
          [] inEvent.type = "stopFSMEv"
             -> /\ state' = "finished"
                /\ outEvent' = NoEvent \* TODO: resetTimer instead? 
                /\ UNCHANGED poolVars
             
          [] OTHER
             -> UNCHANGED <<state, poolVars>> /\ outEvent' = NoEvent

(* What happens in the state waitForBlock *)

\* Produce requests for blocks. See pool.MakeNextRequests and pool.MakeRequestBatch     
OnMakeRequestsInWaitForBlock ==
    /\ state = "waitForBlock" /\ inEvent.type = "makeRequestsEv"
    \* TODO: pool.makeRequestBatch calls removeBadPeers first, which is hard to implement in one step
    /\ LET pendingBlocks == {h \in DOMAIN blocks: blocks[h] /= None} IN
       LET numPendingBlocks == Cardinality(pendingBlocks) IN \* len(blocks) in pool.go   
       \*  compute the next request height, see pool.go:194-201
       nextRequestHeight' =
         Min(nextRequestHeight + inEvent.maxNumRequests - numPendingBlocks, maxPeerHeight)
    /\ LET heights == nextRequestHeight..nextRequestHeight' - 1 IN
        \* for each height h, assign a peer whose height is not lower than h
        /\ blocks' =
              [h \in Heights |->
                IF h \in heights
                THEN CHOOSE p \in peers: peerHeights[p] >= h
                ELSE InvalidBlock
              ]
           \* group all block requests into one output event
        /\ outEvent' = [type |-> "sendBlockRequest",
                        reqs |-> { [peerID |-> blocks'[h],
                                    height |-> h] : h \in heights }]
    \* TODO: the implementation requires !(peer.NumPendingBlockRequests >= maxRequestsPerPeer)
    \* TODO: the implementation may report errSendQueueFull
    \* TODO: peer.RequestSent(height)
    /\ state' = "waitForBlock"
    /\ UNCHANGED <<poolHeight, blocks, ghostProcessedHeights>>
             
\* a peer responded with its height
OnStatusResponseInWaitForBlock ==
    /\ state = "waitForBlock" /\ inEvent.type = "statusResponseEv"
    /\ UpdatePeer(inEvent.peerID, inEvent.height)
    /\ state' =
          IF poolHeight >= maxPeerHeight'
            THEN "finished"
            ELSE IF NoPeers' THEN "waitForPeer" ELSE "waitForBlock"
    /\ outEvent' = NoEvent
    /\ UNCHANGED <<poolHeight, ghostProcessedHeights>>

\* a peer responded with a block
OnBlockResponseInWaitForBlock ==
    /\ state = "waitForBlock"
    /\ inEvent.type = "blockResponseEv"
    /\  IF (~inEvent.block.valid \/ inEvent.height \notin DOMAIN blocks
            \/ inEvent.peerID /= blocks[inEvent.height] \/ inEvent.peerID \notin peers)
        \* A block was received that was unsolicited, from unexpected peer, or that we already have it
        THEN  /\ RemovePeer(inEvent.peerID)
              /\ outEvent' = [type |-> "sendPeerError", peerIDs |-> {inEvent.peerID}]
        \* an OK block, the implementation adds it to the store
        ELSE  /\ outEvent' = NoEvent
              /\ UNCHANGED <<peers, blocks, nextRequestHeight>>
    /\ state' = IF NoPeers' THEN "waitForPeer" ELSE "waitForBlock"
    /\ UNCHANGED <<poolHeight, ghostProcessedHeights>>

\* the block at the current height has been processed
OnProcessedBlockInWaitForBlock ==
    /\ state = "waitForBlock" /\ inEvent.type = "processedBlockEv"
    /\  IF inEvent.err
        THEN
          \E p1, p2 \in PeerIDs \cup {None}:
            /\ InvalidateFirstTwoBlocks(p1, p2)
            /\ outEvent' = [ type |-> "sendPeerError",
                             peerIDs |-> { p \in {p1, p2}: p /= None } ]
            /\ UNCHANGED <<poolHeight, ghostProcessedHeights>>
        ELSE \* pool.ProcessedCurrentHeightBlock
          /\ blocks' = [blocks EXCEPT ![poolHeight] = None] \* remove the block at the pool height
          /\ poolHeight' = poolHeight + 1                   \* advance the pool height
          /\ outEvent' = NoEvent
          /\ ghostProcessedHeights' = ghostProcessedHeights \cup {poolHeight} \* record the height
          /\ RemoveShortPeers(poolHeight')
          /\ UNCHANGED nextRequestHeight
          \* pool.peers[peerID].RemoveBlock(pool.Height)
          \* TODO: resetStateTimer?
    /\ state' = IF poolHeight' >= maxPeerHeight' THEN "finished" ELSE "waitForBlock"

\* a peer was disconnected or produced an error    
OnPeerRemoveInWaitForBlock ==
    /\ state = "waitForBlock" /\ inEvent.type = "peerRemoveEv"
    /\ RemovePeer(inEvent.peerID)
    /\ state' =
          IF poolHeight >= maxPeerHeight'
            THEN "finished"
            ELSE IF NoPeers' THEN "waitForPeer" ELSE "waitForBlock"
    /\ outEvent' = NoEvent
    /\ UNCHANGED <<poolHeight, ghostProcessedHeights>>

\* a timeout when waiting for a block
OnStateTimeoutInWaitForBlock ==
    /\ state = "waitForBlock" /\ inEvent.type = "stateTimeoutEv"
    /\ inEvent.stateName = state
    \* below we summarize pool.RemovePeerAtCurrentHeights
    /\ \/ \E p \in peers:
          /\ IsPeerAtHeight(p, poolHeight)
          /\ RemovePeer(p)      \* remove the peer at current height
       \/ /\ \A p \in peers: ~IsPeerAtHeight(p, poolHeight)
          /\ \/ \E q \in peers:
                /\ IsPeerAtHeight(q, poolHeight + 1)
                /\ RemovePeer(q)    \* remove the peer at height + 1
             \* remove no peers, are we stuck here?
             \/ /\ \A q \in peers: ~IsPeerAtHeight(q, poolHeight + 1)
                /\ UNCHANGED <<maxPeerHeight, blocks, nextRequestHeight, peerHeights>> 
    \* resetStateTimer?
    /\ UNCHANGED <<peers, poolHeight, ghostProcessedHeights>>
    /\ outEvent' = NoEvent
    /\ state' =
          IF poolHeight >= maxPeerHeight'
            THEN "finished"
            ELSE IF NoPeers' THEN "waitForPeer" ELSE "waitForBlock"
    
\* a stop event
OnStopFSMInWaitForBlock ==
    /\ state = "waitForBlock" /\ state' = "finished"
    /\ inEvent.type = "stopFSMEv" /\ outEvent' = NoEvent
    /\ UNCHANGED poolVars
    \* stateTimer.Stop() ?   
        
\* when in state waitForBlock        
InWaitForBlock ==
    \/ OnMakeRequestsInWaitForBlock
    \/ OnStatusResponseInWaitForBlock             
    \/ OnBlockResponseInWaitForBlock 
    \/ OnProcessedBlockInWaitForBlock
    \/ OnPeerRemoveInWaitForBlock
    \/ OnStateTimeoutInWaitForBlock
    \/ /\ state = "waitForBlock" /\ inEvent.type = "stateTimeoutEv"
       /\ inEvent.stateName = state /\ outEvent' = NoEvent
       /\ UNCHANGED <<state, poolVars>>
    \/ OnStopFSMInWaitForBlock
    \/ /\ state = "waitForBlock" /\ inEvent.type = "startFSMEv"
       /\ outEvent' = NoEvent
       /\ UNCHANGED <<state, poolVars>> 

NextFsm ==
    \/ InInit
    \/ InWaitForPeer
    \/ InWaitForBlock
    \/ UNCHANGED <<state, poolVars, outEvent>>

(* ------------------------------------------------------------------------------------------------*)
(* The system is the composition of the non-deterministic reactor and the FSM *)
(* ------------------------------------------------------------------------------------------------*)
Init == InitReactor /\ InitFsm

Next == NextReactor /\ NextFsm

(* ------------------------------------------------------------------------------------------------*)
(* Expected properties *)
(* ------------------------------------------------------------------------------------------------*)
\* a sample property that triggers a counterexample in TLC
NeverFinishAtMax == [] (state = "finished" => poolHeight < maxHeight)

\* This seems to be the safety requirement:
\*   all blocks up to poolHeight have been processed 
Safety == 0..poolHeight - 1 \subseteq ghostProcessedHeights

\* before specifying liveness, we have to write constraints on the reactor events
\* a good event
GoodEvent ==
    \* no timeouts, no peer removal
    /\ inEvent.type \notin { "stateTimeoutEv", "peerRemoveEv" }
    \* no invalid blocks
    /\ inEvent.type = "blockResponseEv" => inEvent.block.valid
    /\ inEvent.type = "processedBlockEv" => ~inEvent.err
    
\* the reactor can always kill progress by sending updates or useless messages
NoSpam == inEvent.type \notin
     { "statusResponseEv", "startFSMEv",
       "stopFSMEv", "processedBlockEv", "makeRequestEv"}

\* we cannot get a response for the same height infinitely often
NoInfiniteResponse ==
  \A h \in Heights:
     [](inEvent.type = "blockResponseEv" /\ inEvent.height = h
         => <>[](inEvent.type /= "blockResponseEv" \/ inEvent.height /= h))   
    
\* A liveness property that tells us that the protocol should terminate in the good case
GoodTermination ==
  ([]GoodEvent /\ <>[] NoSpam /\ NoInfiniteResponse)
     => <>(state = "finished" /\ poolHeight = maxHeight)

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
\* Last modified Fri Jul 12 21:36:19 CEST 2019 by igor
\* Created Fri Jun 28 20:08:59 CEST 2019 by igor
