-------------------------------- MODULE fastsync --------------------------------
(*
 A specification of the fast sync finite-state machine that is introduced in:
 
 https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/docs/spec/reactors/block_sync/bcv1/impl-v1.md
 
 We are modeling three important ingredients:
    - a non-faulty FSM that does fast sync
    - a block pool that maintains the blocks that FSM receives from the peers, and
    - the reactor, which may be completely chaotic.
    
 This specification focuses on the events that are received by the FSM from the reactor.
 The events that are emitted by the FSM are currently ignored.
 We may extend the spec in the future.
*)

EXTENDS Integers, FiniteSets

(*
 Constants that are introduced for model checking purposes.
 In the future, we may want to introduce them as CONSTANTS.
 *)
None == -1          \* an undefined value
PeerIDs == 0..2     \* potential peer ids
maxHeight == 4      \* the maximum height
Heights == 0..maxHeight \* potential heights
NumRequests == 3    \* the number of requests made per batch

\* basic stuff
Min(a, b) == IF a < b THEN a ELSE b

\* the state of the reactor: https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/blockchain/v1/reactor.go
VARIABLES event                     \* an incoming event
          
\* the state of the FSM: https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/blockchain/v1/reactor_fsm.go
VARIABLE state

\* the block pool: https://github.com/tendermint/tendermint/blob/ancaz/blockchain_reactor_reorg/blockchain/v1/pool.go
VARIABLE peers,         \* the set of active peers, not known to be faulty
         peerHeights,   \* PeerId -> Height to collect the peer responses about their heights 
         blocks,        \* Height -> PeerID to collect the peers that have delivered the blocks
         poolHeight,    \* height of the next block to collect
         maxPeerHeight, \* maximum height of all peers
         nextRequestHeight,     \* the height at which the next request is going to be made
         ghostProcessedHeights   \* a ghost variable to collect the heights that have been processed successfully 
         \* the implementation contains plannedRequests that we omit here
         
\* the variables of the block pool, to be used as UNCHANGED poolVars
poolVars == <<peers, peerHeights, blocks, poolHeight, maxPeerHeight, nextRequestHeight, ghostProcessedHeights>>

(* The potential states of the FSM *)
States == { "init", "waitForPeer", "waitForBlock", "finished" }

(* Currently, a block is completely abstract. We only know whether it is valid or not. *)
Blocks == [ valid: BOOLEAN ]
InvalidBlock == [ valid |-> FALSE]

\* These are the types of input events that can be produced by the reactor to the FSM
EventTypes == { "startFSMEv", "statusResponseEv", "blockResponseEvent", "stateTimeoutEv",
                "peerRemoveEv", "processedBlockEv", "makeRequestEv", "stopFSMEv" }

\* These are all possible events that can be produced by the reactor.
\* Mimicking a combination of bReactorEvent and bReactorEventData.
Events ==
    [ type: {"startFSMEv"} ]
    \cup
    [ type: {"statusResponseEv"}, peerID: PeerIDs, height: Heights]
    \cup
    [ type: {"blockResponseEvent"}, peerID: PeerIDs, height: Heights, block: Blocks ]
    \cup
    [ type: {"stateTimeoutEv"}, stateName: States ]
    \cup
    [ type: {"peerRemoveEv"}, peerID: PeerIDs, err: BOOLEAN ]
    \cup
    [ type: {"processedBlockEv"}, err: BOOLEAN ] 
    \cup
    [ type: {"makeRequestEv"}, maxNumRequests: {NumRequests} ]
    \cup
    [ type: {"stopFSMEv"} ]

(* ------------------------------------------------------------------------------------------------*)
(* The behavior of the reactor. In this specification, the reactor keeps generating events *)
(* ------------------------------------------------------------------------------------------------*)
InitReactor ==
    event = [type |-> "startFSMEv"]
    
NextReactor ==
    event' \in Events \* the reactor produces an arbitrary event

(* ------------------------------------------------------------------------------------------------*)
(* The behavior of the block pool, which keeps track of peers, block requests, and block responses *)
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

\* Remove a peer from the set of active peers                
RemovePeer(peerId) ==
    /\ peers' = peers \ { peerId }  \* remove the peer
    /\ UNCHANGED peerHeights        \* keep the heights, as the height of the removed peer is never used
    /\ UpdateMaxPeerHeight(peers', peerHeights) \* the maximum height may lower
       \* adjust the height of the next request, if it has lowered
    /\ nextRequestHeight' = Min(maxPeerHeight' + 1, nextRequestHeight)

IsPeerAtHeight(p, h) ==
    \* the peer has not been removed, nor invalid, nor the block is corrupt
    p \in peers /\ h \in DOMAIN blocks /\ p = blocks[h]
       
\* A summary of InvalidateFirstTwoBlocks
InvalidateFirstTwoBlocks ==
    \E p1, p2 \in PeerIDs \cup {None}:
        \* find the peers at height and height + 1, if possible
        /\ \/ IsPeerAtHeight(p1, poolHeight)
           \/ p1 = None /\ \A q \in PeerIDs: ~IsPeerAtHeight(q, poolHeight)
        /\ \/ IsPeerAtHeight(p2, poolHeight + 1)
           \/ p2 = None /\ \A q \in PeerIDs: ~IsPeerAtHeight(q, poolHeight + 1)
        \* remove the peers (unless they are None)
        /\ peers' = peers \ { p1, p2 }
        \* keep the heights, as the height of the removed peer is ignored
        /\ UNCHANGED peerHeights
        \* the maximum height may lower
        /\ UpdateMaxPeerHeight(peers', peerHeights)
        \* adjust the height of the next request, if it has lowered
        /\ nextRequestHeight' = Min(maxPeerHeight' + 1, nextRequestHeight)

\* Update the peer height (and add if it is not in the set)                    
UpdatePeer(peerId, height) ==
    CASE height >= poolHeight
        -> (* the common case. Add or keep the peer and update its height. *)
        /\ peers' = peers \cup { peerId } \* add the peer, if it does not exist
        /\ peerHeights' = [peerHeights EXCEPT ![peerId] = height] \* set the peer's height
        /\ UpdateMaxPeerHeight(peers', peerHeights')
        /\ UNCHANGED nextRequestHeight
        
      [] peerId \notin peers /\ height < poolHeight
        -> (* peer height too small. Ignore. *)
        UNCHANGED <<peers, peerHeights, maxPeerHeight, nextRequestHeight>>
        
      [] peerId \in peers /\ height < poolHeight
        -> (* the peer is corrupt? Remove the peer. *)
        RemovePeer(peerId)  \* may lower nextRequestHeight


(* ------------------------------------------------------------------------------------------------*)
(* The behavior of the fast-sync state machine *)
(* ------------------------------------------------------------------------------------------------*)
InitFsm ==
    /\ state = "init"
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
    /\ CASE event.type = "startFSMEv"
             -> /\ state' = "waitForPeer"
                /\ UNCHANGED poolVars
                \* TODO: SendStatusRequest?
         [] OTHER
             -> UNCHANGED <<state, poolVars>> 

(* What happens in the state waitForPeer *)

InWaitForPeer ==
    /\ state = "waitForPeer"
    /\  CASE event.type = "statusResponseEv"
             -> /\ UpdatePeer(event.peerID, event.height)
                /\ state' = IF SomePeers' THEN "waitForBlock" ELSE state
                /\ UNCHANGED <<poolHeight, blocks, ghostProcessedHeights>>
                \* TODO: StopTimer? 
                
          [] event.type = "stateTimeoutEv"
             -> /\ state' = IF event.stateName = state THEN "finished" ELSE state
                /\ UNCHANGED poolVars
                \* TODO: StopTimer? 
             
          [] event.type = "stopFSMEv"
             -> /\ state' = "finished"
                /\ UNCHANGED poolVars
                \* TODO: StopTimer? 
             
          [] OTHER
             -> UNCHANGED <<state, poolVars>>

(* What happens in the state waitForBlock *)

\* Produce requests for blocks. See pool.MakeNextRequests and pool.MakeRequestBatch     
OnMakeRequestsInWaitForBlock ==
    /\ state = "waitForBlock" /\ event.type = "makeRequestsEv"
    /\ nextRequestHeight' = Min(event.numRequests - 1, maxPeerHeight) \* see pool.go:194-201
    /\ LET heights == 0..nextRequestHeight' IN
        \* pool.SendRequest(height)
        \* for each height h, assign a peer whose height is not lower than h
        blocks' =
          [h \in Heights |->
            IF h \in heights
            THEN CHOOSE p \in peers: peerHeights[p] >= h
            ELSE InvalidBlock
          ]
    \* TODO: the implementation requires !(peer.NumPendingBlockRequests >= maxRequestsPerPeer)
    \* TODO: the implementation may report errSendQueueFull
    \* TODO: pool.toBcR.sendBlockRequest(peer.ID, height)
    \* TODO: peer.RequestSent(height)
    /\ state' = "waitForBlock"
    /\ UNCHANGED <<poolHeight, blocks, ghostProcessedHeights>>
             
\* a peer responded with its height
OnStatusResponseInWaitForBlock ==
    /\ state = "waitForBlock" /\ event.type = "statusResponseEv"
    /\ UpdatePeer(event.peerID, event.height)
    /\ state' =
          IF poolHeight >= maxPeerHeight'
            THEN "finished"
            ELSE IF NoPeers' THEN "waitForPeer" ELSE "waitForBlock"
    /\ UNCHANGED <<poolHeight, blocks, ghostProcessedHeights>>

\* a peer responded with a block
OnBlockResponseInWaitForBlock ==
    /\ state = "waitForBlock"
    /\ event.type = "blockResponseEv"
    /\  IF (~event.block.valid \/ event.peerID /= blocks[event.height] \/ event.peerID \notin peers)
        \* A block was received that was unsolicited, from unexpected peer, or that we already have it
        THEN RemovePeer(event.peerID)
        \* an OK block, the implementation adds it to the store
        ELSE UNCHANGED <<peers, nextRequestHeight>>
    /\ state' = IF NoPeers' THEN "waitForPeer" ELSE "waitForBlock"
    /\ UNCHANGED <<poolHeight, blocks, ghostProcessedHeights>>

\* the block at the current height has been processed
OnProcessedBlockInWaitForBlock ==
    /\ state = "waitForBlock" /\ event.type = "processedBlockEv"
    /\  IF event.err
        THEN
          /\ InvalidateFirstTwoBlocks
          /\ UNCHANGED <<poolHeight, blocks, ghostProcessedHeights>>
        ELSE \* pool.ProcessedCurrentHeightBlock
          /\ blocks' = [blocks EXCEPT ![poolHeight] = None] \* remove the block at the pool height
          /\ poolHeight' = poolHeight + 1                   \* advance the pool height
          /\ ghostProcessedHeights' = ghostProcessedHeights \cup {poolHeight} \* record the height
          /\ UNCHANGED <<peers, peerHeights, maxPeerHeight, nextRequestHeight>>
          \* pool.peers[peerID].RemoveBlock(pool.Height)
            \* TODO: resetStateTimer?
            \* TODO: removeShortPeers?
    /\ state' = IF poolHeight' >= maxPeerHeight' THEN "finished" ELSE "waitForBlock"

\* a peer was disconnected or produced an error    
OnPeerRemoveInWaitForBlock ==
    /\ state = "waitForBlock" /\ event.type = "peerRemoveEv"
    /\ RemovePeer(event.peerID)
    /\ state' =
          IF poolHeight >= maxPeerHeight'
            THEN "finished"
            ELSE IF NoPeers' THEN "waitForPeer" ELSE "waitForBlock"
    /\ UNCHANGED <<poolHeight, blocks, ghostProcessedHeights>>

\* a timeout when waiting for a block
OnStateTimeoutInWaitForBlock ==
    /\ state = "waitForBlock" /\ event.type = "stateTimeoutEv"
    /\ event.stateName = state
    \* pool.RemovePeerAtCurrentHeights
    /\ \/ \E p \in peers:
          /\ IsPeerAtHeight(p, poolHeight)
          /\ RemovePeer(p)      \* remove the peer at current height
       \/ /\ \A p \in peers: ~IsPeerAtHeight(p, poolHeight)
          /\ \/ \E q \in peers:
                /\ IsPeerAtHeight(q, poolHeight + 1)
                /\ RemovePeer(q)    \* remove the peer at height + 1
             \* remove no peers, are we stuck here?
             \/ /\ \A q \in peers: ~IsPeerAtHeight(q, poolHeight + 1)
                /\ UNCHANGED <<maxPeerHeight, nextRequestHeight, peerHeights>> 
    \* resetStateTimer?
    /\ UNCHANGED <<peers, blocks, poolHeight, ghostProcessedHeights>>
    /\ state' =
          IF poolHeight >= maxPeerHeight'
            THEN "finished"
            ELSE IF NoPeers' THEN "waitForPeer" ELSE "waitForBlock"
    
\* a stop event
OnStopFSMInWaitForBlock ==
    /\ state = "waitForBlock"
    /\ state' = "finished"
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
    \/ /\ state = "waitForBlock" /\ event.type = "stateTimeoutEv"
       /\ event.stateName = state /\ UNCHANGED <<state, poolVars>>
    \/ OnStopFSMInWaitForBlock
    \/ /\ state = "waitForBlock" /\ event.type = "startFSMEv"
       /\ UNCHANGED <<state, poolVars>> 

NextFsm ==
    \/ InInit
    \/ InWaitForPeer
    \/ InWaitForBlock
    \/ UNCHANGED <<state, poolVars>>

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

(* ------------------------------------------------------------------------------------------------*)
(* Questions in the back of my head *)
(* ------------------------------------------------------------------------------------------------*)

(*
  Q1. What if a faulty peer is reporting a very large height? The protocol is stuck forever?
  
  Q2. Can we ever collect over maxNumRequests (=64) blocks.
      It seems to be an upper bound on the pool height. See pool.go:194
      
  Q3. I do not see why pool.makeRequestBatch cannot produce duplicate heights in pool.plannedRequests.
  
  Q4. Why don't you clean up pool.plannedRequests in pool.go:180?  
 *)


=============================================================================
\* Modification History
\* Last modified Wed Jul 10 15:21:41 CEST 2019 by igor
\* Created Fri Jun 28 20:08:59 CEST 2019 by igor
