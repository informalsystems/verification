----------------------------- MODULE fastsyncL2 -----------------------------
(*
 In this document we give the high level specification of the fast sync
 protocol as implemented here:
 https://github.com/tendermint/tendermint/tree/master/blockchain/v2.
 
 We assume a system in which one node is trying to sync with the blockchain 
(replicated state machine) by downloading blocks and executing transactions 
(part of the block) agaings the application, and the set of full nodes 
(we call them peers) that are block providers.

Peers can be faulty, and we don't make any assumption about the rate of correct/faulty 
nodes in the node peerset (i.e., they can all be faulty). Correct peers are part 
of the replicated state machine, i.e., they manage blockchain and execute 
transactions against the same deterministic application. We don't make any 
assumptions about the behavior of faulty processes. Processes (client and peers) 
communicate by message passing. 
 
 In this specification, we model this system with two parties:
    - the node (state machine) that is doing fastsync and 
    - the environment with which node interacts.

The environment constists of the set of (correct and faulty) peers with
which node interacts as part of fast sync protocol, but also contains some 
aspects (adding/removing peers, timeout mechanism) that are part of the node
local environment (could be seen as part of the runtime in which node
executes). 

As part of the fast sync protocols node and the peers exchange the following messages:   
    
- StatusRequest
- StatusReply
- BlockRequest
- BlockReply

A node is peridically issuing StatusRequets to query peers for their current height (to decide what 
blocks to ask from what peers). Based on StatusReplies (that are sent by peers), the node queries 
blocks for some height(s) by sending them BlockRequest messages. A peer provides a requested block by
BlockResponse message. In addition to those messages, a node in this spec receives additional
input messages (events):

- AddPeer
- RemovePeer
- SyncTimeout.

These are the control messages that are provided to the node by its execution enviornment. AddPeer 
is for the case when a connection is established with a peer; similarly RemovePeer is for the case
a connection with the peer is terminated. Finally SyncTimeout is used to model a timeout trigger.

We assume that fast sync protocol starts when connections with some number of peers
are established. Therefore, peer set is initialised with non-empty set of peer ids. Note however
that node does not know initially the peer heights.

English specification of the fast sync protocol can be found here: TODO[Add correct link]. 
*)

EXTENDS Integers, FiniteSets, Sequences 

CONSTANTS MAX_HEIGHT, 
          CORRECT,                   \* set of correct peers
          FAULTY,                    \* set of faulty peers 
          TARGET_PENDING,            \* maximum number of pending requests + downloaded blocks that are not yet processed 
          PEER_MAX_REQUESTS          \* maximum number of pending requests per peer

ASSUME CORRECT \intersect FAULTY = {}
ASSUME TARGET_PENDING > 0
ASSUME PEER_MAX_REQUESTS > 0


\* the set of potential heights
Heights == 1..MAX_HEIGHT

\* simplifies execute blocks logic. Used only in block store. 
HeightsPlus == 1..MAX_HEIGHT+1

\* the set of all peer ids the node can receive a message from
AllPeerIds == CORRECT \union FAULTY

\* the set of potential blocks ids. For simplification, correct blocks are equal to block height.
BlockIds == Heights

LastCommits == [blockId: BlockIds, enoughVotingPower: BOOLEAN]

\* Correct last commit have enough voting power, i.e., +2/3 of the voting power of 
\* the corresponding validator set (enoughVotingPower = TRUE) that signs blockId.
\* BlockId defines correct previous block (in reality it is the hash of the block). 
\* For simplicity, we model blockId as the height of the previous block.  
CorrectLastCommit(h) == [blockId |-> h-1, enoughVotingPower |-> TRUE]

NilCommit == [blockId |-> 0, enoughVotingPower |-> TRUE]

Blocks == [height: Heights, lastCommit: LastCommits, wellFormed: BOOLEAN]

\* correct node will create always valid blocks, i.e., wellFormed = true and lastCommit is correct. 
CorrectBlock(h) == [height |-> h, lastCommit |-> CorrectLastCommit(h), wellFormed |-> TRUE]

NilBlock == [height |-> 0, lastCommit |-> NilCommit, wellFormed |-> TRUE]

\* a special value for an undefined height
NilHeight == 0

\* a special value for an undefined peer
NilPeer == 0

States == { "running", "finished", "aborted" }

NoMsg == [type |-> "None"]

\* the variables of the node running fastsync
VARIABLES
  state,                                     \* running or finished                              
  blockPool
  (*
  blockPool [
    height,                                 \* current height we are trying to sync. Last block executed is height - 1
    peerIds,                                \* set of peers node is connected to      
    peerHeights,                            \* map of peer ids to its (stated) height
    blockStore,                             \* map of heights to (received) blocks
    receivedBlocks,                         \* map of heights to peer that has sent us the block (stored in blockStore)
    pendingBlocks,                          \* map of heights to peer to which block request has been sent
    syncHeight,                             \* height at the point syncTimeout was triggered last time 
    syncedBlocks                            \* number of blocks synced since last syncTimeout
  ]
  *)

\* the variables of the peers providing blocks
VARIABLES                                   
  peersState
  (*
  peersState [
    peerHeights,                             \* track peer heights
    statusRequested,                         \* boolean set to true when StatusRequest is received. Models periodic sending of StatusRequests. 
    blocksRequested                          \* set of BlockRequests received that are not answered yet 
  ]
  *) 
 
 \* the variables for the network and scheduler
 VARIABLES
  turn,                                     \* who is taking the turn: "Peers" or "Node" 
  inMsg,                                    \* a node receives message by this variable
  outMsg,                                   \* a node sends a message by this variable
  nonDetFlag                                \* variable that non-deterministically takes values from the set BOOLEAN    
  
  
(* the variables of the node *)  
nvars == <<state, blockPool>>
  
\* Control messages
ControlMsgs ==
    [type: {"addPeer"}, peerId: AllPeerIds]
        \union
    [type: {"removePeer"}, peerId: AllPeerIds] 
        \union
    [type: {"syncTimeout"}]        

\* All messages (and events) received by a node
InMsgs ==
    {NoMsg}
        \union
    [type: {"blockResponse"}, peerId: AllPeerIds, block: Blocks]
        \union
    [type: {"statusResponse"}, peerId: AllPeerIds, height: Heights]
        \union
    ControlMsgs    

\* Messages sent by a node and received by peers (environment in our case)          
OutMsgs ==
    {NoMsg}
        \union
    [type: {"statusRequest"}]           \* StatusRequest is broadcast to the set of connected peers.     
        \union  
    [type: {"blockRequest"}, peerId: AllPeerIds, height: Heights]  
        

(********************************** NODE ***********************************)

InitNode == 
     \E pIds \in SUBSET AllPeerIds \ {{}}:                   \* set of peers node established initial connections with
        /\ blockPool = [
                height |-> 1,
                peerIds |-> pIds, 
                peerHeights |-> [p \in AllPeerIds |-> NilHeight],     \* no peer height is known
                blockStore |-> [h \in HeightsPlus |-> NilBlock],        
                receivedBlocks |-> [h \in Heights |-> NilPeer],         
                pendingBlocks |-> [h \in Heights |-> NilPeer],
                syncedBlocks |-> 0,
                syncHeight |-> 1
           ]
       /\ state = "running" 
           
\* Remove a faulty peer.
\* Returns new block pool. If the peer is alredy removed, returns input value.  
RemovePeer(peer, bPool) ==       
    LET pIds == bPool.peerIds \ {peer} IN
    LET pHeights == [bPool.peerHeights EXCEPT ![peer] = NilHeight] IN
    
    LET failedRequests == 
        {h \in Heights: /\ h >= bPool.height 
                        /\ bPool.pendingBlocks[h] = peer
                        /\ bPool.receivedBlocks[h] = peer} IN
    LET pBlocks == 
        [h \in Heights |-> IF h \in failedRequests THEN NilPeer ELSE bPool.pendingBlocks[h]] IN  
    LET rBlocks == 
        [h \in Heights |-> IF h \in failedRequests THEN NilPeer ELSE bPool.receivedBlocks[h]] IN
    LET bStore == 
        [h \in Heights |-> IF h \in failedRequests THEN NilBlock ELSE bPool.blockStore[h]] IN  
    
    IF peer \in bPool.peerIds     
    THEN [bPool EXCEPT 
            !.peerIds = pIds,
            !.peerHeights = pHeights,
            !.pendingBlocks = pBlocks,
            !.receivedBlocks = rBlocks,
            !.blockStore = bStore
          ]                              
    ELSE bPool

\* Remove faulty peers.
\* Returns new block pool. 
RemoveManyPeers(peers, bPool) ==       
    LET pIds == bPool.peerIds \ peers IN
    LET pHeights == 
        [p \in AllPeerIds |-> IF p \in peers THEN NilHeight ELSE bPool.peerHeights[p]] IN 
    
    LET failedRequests == 
        {h \in Heights: /\ h >= bPool.height 
                        /\ bPool.pendingBlocks[h] \in peers
                        /\ bPool.receivedBlocks[h] \in peers} IN
    LET pBlocks == 
        [h \in Heights |-> IF h \in failedRequests THEN NilPeer ELSE bPool.pendingBlocks[h]] IN  
    LET rBlocks == 
        [h \in Heights |-> IF h \in failedRequests THEN NilPeer ELSE bPool.receivedBlocks[h]] IN
    LET bStore == 
        [h \in Heights |-> IF h \in failedRequests THEN NilBlock ELSE bPool.blockStore[h]] IN  
    
    IF pIds /= bPool.peerIds     
    THEN [bPool EXCEPT 
            !.peerIds = pIds,
            !.peerHeights = pHeights,
            !.pendingBlocks = pBlocks,
            !.receivedBlocks = rBlocks,
            !.blockStore = bStore
          ]                              
    ELSE bPool

\* Add a peer.
AddPeer(peer, bPool) == 
    [bPool EXCEPT !.peerIds = bPool.peerIds \union {peer}]
             
     
(* 
Handle StatusResponse message.
If valid status response, update peerHeights.
If invalid (height is smaller than the current), then remove peer.
Returns new block pool.
*)                              
HandleStatusResponse(msg, bPool) == 
    LET peerHeight == bPool.peerHeights[msg.peerId] IN     
    
    IF /\ msg.peerId \in bPool.peerIds 
       /\ msg.height >= peerHeight  
    THEN    \* a correct response 
        LET pHeights == [bPool.peerHeights EXCEPT ![msg.peerId] = msg.height] IN
        [bPool EXCEPT !.peerHeights = pHeights]                   
    ELSE RemovePeer(msg.peerId, bPool)   \* the peer has sent us message with smaller height or peer is not in our peer list
        
        
(* 
Handle BlockResponse message.
If valid block response, update blockStore, pendingBlocks and receivedBlocks.
If invalid (unsolicited response or malfored block), then remove peer.
Returns new block pool.
*)  
HandleBlockResponse(msg, bPool) ==      
    LET h == msg.block.height IN
    
    IF /\ msg.peerId \in bPool.peerIds
       /\ bPool.blockStore[h] = NilBlock 
       /\ bPool.pendingBlocks[h] = msg.peerId
       /\ msg.block.wellFormed   
    THEN  
        [bPool EXCEPT 
            !.blockStore = [bPool.blockStore EXCEPT ![h] = msg.block],
            !.receivedBlocks = [bPool.receivedBlocks EXCEPT![h] = msg.peerId],
            !.pendingBlocks = [bPool.pendingBlocks EXCEPT![h] = NilPeer]         
         ]  
    ELSE RemovePeer(msg.peerId, bPool)
                       
\* Compute max peer height.
MaxPeerHeight(bPool) == 
    IF bPool.peerIds = {}
    THEN 0 \* no peers, just return 0
    ELSE CHOOSE max \in { bPool.peerHeights[p] : p \in bPool.peerIds }:
            \A p \in bPool.peerIds: bPool.peerHeights[p] <= max \* max is the maximum
    

(* Returns next height for which request should be sent.
   Returns NilHeight in case there is no height for which request can be sent.  *)
FindNextRequestHeight(bPool) == 
    LET S == {i \in Heights:  
                /\ i >= bPool.height  
                /\ i <= MaxPeerHeight(bPool)   
                /\ bPool.blockStore[i] = NilBlock 
                /\ bPool.pendingBlocks[i] = NilPeer} IN
    IF S = {} 
        THEN NilHeight
    ELSE      
        CHOOSE min \in S:  \A h \in S: h >= min

\* Returns number of pending requests for a given peer.
NumOfPendingRequests(bPool, peer) == 
    LET peerPendingRequests == 
        {h \in Heights: 
            /\ h >= bPool.height 
            /\ bPool.pendingBlocks[h] = peer
        }
    IN 
    Cardinality(peerPendingRequests)

(* Returns peer that can serve block for a given height. 
   Returns NilPeer in case there are no such peer.  *)
FindPeerToServe(bPool, h) == 
    LET peersThatCanServe == { p \in bPool.peerIds: 
                /\ bPool.peerHeights[p] >= h 
                /\ NumOfPendingRequests(bPool, p) < PEER_MAX_REQUESTS } IN
    
    LET pendingBlocks == 
        {i \in Heights: 
            /\ i >= bPool.height 
            /\ \/ bPool.pendingBlocks[i] /= NilPeer
               \/ bPool.blockStore[i] /= NilBlock
        } IN
    
    IF \/ peersThatCanServe = {} 
       \/ Cardinality(pendingBlocks) >= TARGET_PENDING 
    THEN NilPeer 
    \* pick a peer that can serve request for height h that has minimum number of pending requests
    ELSE CHOOSE p \in peersThatCanServe: \A q \in peersThatCanServe:       
            /\ NumOfPendingRequests(bPool, p) <= NumOfPendingRequests(bPool, q) 
            \*/\ p <= q \* otherwise, TLC reports an error in CHOOSE
    
       
\* Make a request for a block (if possible) and returns a request message and block poool.
CreateRequest(bPool) ==
    LET nextHeight == FindNextRequestHeight(bPool) IN
    
    IF nextHeight = NilHeight THEN [msg |-> NoMsg, pool |-> bPool]
    ELSE
     LET peer == FindPeerToServe(bPool, nextHeight) IN
     IF peer = NilPeer THEN [msg |-> NoMsg, pool |-> bPool]
     ELSE 
        LET m == [type |-> "blockRequest", peerId |-> peer, height |-> nextHeight] IN
        LET newPool == [bPool EXCEPT 
                          !.pendingBlocks = [bPool.pendingBlocks EXCEPT ![nextHeight] = peer]
                        ] IN
        [msg |-> m, pool |-> newPool]   
        

\* Returns node state, i.e., defines termination condition. 
GetState(bPool) == 
    IF bPool.syncedBlocks = 0 /\ bPool.syncHeight /= 1 \* corresponds to the syncTimeout in case no progress has been made for a period of time.
    THEN "finished"
    ELSE IF /\ bPool.height > 1 
            /\ bPool.height >= MaxPeerHeight(bPool) \* see https://github.com/tendermint/tendermint/blob/61057a8b0af2beadee106e47c4616b279e83c920/blockchain/v2/scheduler.go#L566
         THEN "finished" 
         ELSE "running"      
         
(* Verify if commit is for the given block id and if commit has enough voting power. 
   See https://github.com/tendermint/tendermint/blob/61057a8b0af2beadee106e47c4616b279e83c920/blockchain/v2/processor_context.go#L12 *)
VerifyCommit(block, lastCommit) == 
    /\ lastCommit.enoughVotingPower     
    /\ lastCommit.blockId = block.height 


(* Tries to execute next block in the pool, i.e., defines block validation logic. 
   Returns new block pool (peers that has send invalid blocks are removed).  *)
ExecuteBlocks(bPool) ==  
    LET bStore == bPool.blockStore IN
    LET block1 == bStore[bPool.height] IN
    LET block2 == bStore[bPool.height+1] IN
    
    IF block1 = NilBlock \/ block2 = NilBlock \* we don't have two next consequtive blocks
    THEN bPool   
    ELSE IF bPool.height > 1 /\ ~VerifyCommit(block1, block2.lastCommit) 
         THEN RemoveManyPeers({bPool.receivedBlocks[block1.height], bPool.receivedBlocks[block2.height]}, bPool)
         ELSE  \* all good, execute block at position height
            [bPool EXCEPT !.height = bPool.height + 1]
              
              
\* Defines logic for pruning peers. 
TryPrunePeer(bPool, nonDetSet) ==    
    (* -----------------------------------------------------------------------------------------------------------------------*)
    (* Corresponds to function prunablePeers the in scheduler.go file. Note that this function only checks if block has been  *)
    (* received from a peer during peerTimeout period.                                                                        *)
    (* Note that in case no request has been scheduled to a correct peer, or a request has been scheduled                     *)
    (* recently, so the peer hasn't responded yet, a peer will be removed as no block is received within peerTimeout.         *)
    (* In case of faulty peers, we don't have any guarantee that they will respond.                                           *)
    (* Therefore, we model this with nondeterministic behavior as it could lead to peer removal, for both correct and faulty. *)
    (* See scheduler.go                                                                                                       *)
    (* https://github.com/tendermint/tendermint/blob/4298bbcc4e25be78e3c4f21979d6aa01aede6e87/blockchain/v2/scheduler.go#L335 *)
    LET toRemovePeers == bPool.peerIds \intersect nonDetSet IN
       
    (*
      Corresponds to logic for pruning a peer that is responsible for delivering block for the next height.
      If a peer responsible for next height is correct, we don't remove it as logic is based on difference between pending time
      and current time. In the synchronous system model, correct peer will always respond timely. 
      See scheduler.go     
      https://github.com/tendermint/tendermint/blob/4298bbcc4e25be78e3c4f21979d6aa01aede6e87/blockchain/v2/scheduler.go#L617    
    *)
    LET nextHeightPeer == bPool.pendingBlocks[bPool.height] IN
    LET prunablePeers == 
        IF /\ nextHeightPeer /= NilPeer
           /\ nextHeightPeer \in FAULTY
           /\ nonDetFlag 
        THEN toRemovePeers \union {nextHeightPeer} 
        ELSE toRemovePeers
    IN
    RemoveManyPeers(prunablePeers, bPool)
    

\* Handle SyncTimeout. It models if progress has been made (height has increased) since the last SyncTimeout event.
HandleSyncTimeout(bPool) ==    
    [bPool EXCEPT 
            !.syncedBlocks = bPool.height - bPool.syncHeight, 
            !.syncHeight = bPool.height
    ]      


\* Handle control messages.
HandleControlMsg(msg, bPool) == 
    IF msg.type = "statusResponse" 
    THEN HandleStatusResponse(msg, bPool)
    ELSE IF msg.type = "addPeer" 
         THEN AddPeer(msg.peerId, bPool)
         ELSE IF msg.type = "removePeer"
         THEN RemovePeer(msg.peerId, bPool)  
         ELSE IF msg.type = "syncTimeout"
              THEN HandleSyncTimeout(bPool)  
              ELSE bPool 

HandleResponse(msg, bPool) == 
    IF msg = NoMsg 
    THEN bPool
    ELSE IF msg.type = "blockResponse" 
         THEN HandleBlockResponse(msg, bPool) 
         ELSE HandleControlMsg(msg, bPool)  
    
(*
   At every node step we executed the following steps (atomically):
    1) input message is consumed and the corresponding handler is called,
    2) pruning logic is called
    3) block execution is triggered (we try to execute block at next height)
    4) a request to a peer is made (if possible) and 
    5) we decide if termination condition is satisifed so we stop. 
*)
NodeStep ==
   \E nonDetSet \in SUBSET AllPeerIds:                        \* nonDetSet is a nondeterministic set of peers
        LET bPool == HandleResponse(inMsg, blockPool) IN
        LET bp == TryPrunePeer(bPool, nonDetSet) IN
        LET nbPool == ExecuteBlocks(bp) IN
        LET msgAndPool == CreateRequest(nbPool) IN 
        LET nstate == GetState(msgAndPool.pool) IN
   
        /\ state' = nstate
        /\ blockPool' = msgAndPool.pool
        /\ outMsg' = msgAndPool.msg
        /\ inMsg' = NoMsg
                            
                
\* If node is running, then in every step we try to create blockRequest.
\* In addition, input message (if exists) is consumed and processed. 
NextNode ==
    \/ /\ state = "running" 
       /\ NodeStep  
              
    \/ /\ state = "finished"
       /\ UNCHANGED <<nvars, inMsg, outMsg>>
    

(********************************** Peers ***********************************)

InitPeers ==
    \E pHeights \in [AllPeerIds -> Heights]: 
        peersState = [
         peerHeights |-> pHeights,
         statusRequested |-> FALSE,
         blocksRequested |-> {}
    ]
            
HandleStatusRequest(msg, pState) == 
    [pState EXCEPT 
        !.statusRequested = TRUE
    ]    

HandleBlockRequest(msg, pState) == 
    [pState EXCEPT 
        !.blocksRequested = pState.blocksRequested \union {msg}    
    ]  

HandleRequest(msg, pState) ==  
    IF msg = NoMsg 
    THEN pState
    ELSE IF msg.type = "statusRequest" 
         THEN HandleStatusRequest(msg, pState)
         ELSE HandleBlockRequest(msg, pState)               

CreateStatusResponse(peer, pState, anyHeight) ==  
    LET m == 
        IF peer \in CORRECT 
        THEN [type |-> "statusResponse", peerId |-> peer, height |-> pState.peerHeights[peer]]
        ELSE [type |-> "statusResponse", peerId |-> peer, height |-> anyHeight] IN
    
    [msg |-> m, peers |-> pState] 
             
CreateBlockResponse(msg, pState, anyBlock) == 
    LET m == 
        IF msg.peerId \in CORRECT
        THEN [type |-> "blockResponse", peerId |-> msg.peerId, block |-> CorrectBlock(msg.height)]
        ELSE [type |-> "blockResponse", peerId |-> msg.peerId, block |-> anyBlock] IN
    LET npState == 
        [pState EXCEPT 
            !.blocksRequested = pState.blocksRequested \ {msg}      
        ] IN
    [msg |-> m, peers |-> npState]   
         
GrowBlockchain(pState) == 
    LET newPeerState == 
        [pState EXCEPT !.peerHeights = [p \in AllPeerIds |-> pState.peerHeights[p] + 1]] 
    IN
    /\ peersState' = newPeerState
    /\ inMsg' = NoMsg        


SendStatusResponseMessage(pState) == 
    /\ \E h \in Heights: 
        \E peer \in AllPeerIds:   
            LET msgAndPeers == CreateStatusResponse(peer, pState, h) IN
               /\ peersState' = msgAndPeers.peers
               /\ inMsg' = msgAndPeers.msg   


SendAddPeerMessage == 
   \E peer \in AllPeerIds:
     /\ inMsg' = [type |-> "addPeer", peerId |-> peer]
     /\ UNCHANGED peersState    

SendRemovePeerMessage == 
   \E peer \in AllPeerIds:
     /\ inMsg' = [type |-> "removePeer", peerId |-> peer]
     /\ UNCHANGED peersState    

SendSyncTimeoutMessage == 
    /\ inMsg' = [type |-> "syncTimeout"]
    /\ UNCHANGED peersState    


SendControlMessage(pState) == 
    \/ SendStatusResponseMessage(pState)
    \/ SendAddPeerMessage
    \/ SendRemovePeerMessage
    \/ SendSyncTimeoutMessage
        

SendBlockResponseMessage(pState) == 
    \/  /\ pState.blocksRequested /= {}
        /\ \E msg \in pState.blocksRequested:
             \E block \in Blocks:
                LET msgAndPeers == CreateBlockResponse(msg, pState, block) IN      
                 /\ peersState' = msgAndPeers.peers
                 /\ inMsg' = msgAndPeers.msg      
    
    
    \/  /\ peersState' = pState
        /\ inMsg' \in [type: {"blockResponse"}, peerId: FAULTY, block: Blocks]    

NextEnvStep(pState) == 
    \/  SendBlockResponseMessage(pState)
    \/  GrowBlockchain(pState)
    \/  SendControlMessage(pState)
                         
    
\* Peers consume a message and update it's local state. It then makes a single step, i.e., it sends at most single message.
\* Message sent could be either a response to a request or faulty message (sent by faulty processes). 
NextPeers ==
    LET pState == HandleRequest(outMsg, peersState) IN
    
    \/  /\ outMsg' = NoMsg                    
        /\ NextEnvStep(pState) 
    

\* the composition of the node, the peers, the network and scheduler
Init ==
    /\ InitNode
    /\ InitPeers
    /\ turn = "Peers"
    /\ inMsg = NoMsg
    /\ outMsg = [type |-> "statusRequest"]
    /\ nonDetFlag \in BOOLEAN
        
Next ==
    IF turn = "Peers"
    THEN
        /\ NextPeers
        /\ turn' = "Node"
        /\ nonDetFlag' \in BOOLEAN
        /\ UNCHANGED nvars
    ELSE
        /\ NextNode
        /\ turn' = "Peers"
        /\ nonDetFlag' \in BOOLEAN
        /\ UNCHANGED peersState  



FlipTurn == 
 turn' = (
  IF turn = "Peers" THEN 
   "Node" 
  ELSE
   "Peers"
 ) 
        
 

\* properties to check
TypeOK ==
    /\ state \in States
    /\ inMsg \in InMsgs 
    /\ outMsg \in OutMsgs
    /\ turn \in {"Peers", "Node"}
    /\ peersState \in [
         peerHeights: [AllPeerIds -> Heights \union {NilHeight}],
         statusRequested: BOOLEAN,
         blocksRequested: SUBSET [type: {"blockResponse"}, peerId: AllPeerIds, block: Blocks]
        ]
    /\ blockPool \in [
                height: Heights,
                peerIds: SUBSET AllPeerIds, 
                peerHeights: [AllPeerIds -> Heights \union {NilHeight}],     
                blockStore: [HeightsPlus -> Blocks \union {NilBlock}],
                receivedBlocks: [Heights -> AllPeerIds \union {NilPeer}],
                pendingBlocks: [Heights -> AllPeerIds \union {NilPeer}],
                syncedBlocks: Heights,
                syncHeight: Heights
           ] 
           

\* Compute max peer height.
MaxCorrectPeerHeight(bPool) == 
    LET correctPeers == {p \in bPool.peerIds: p \in CORRECT} IN
    IF correctPeers = {}
    THEN 0 \* no peers, just return 0
    ELSE CHOOSE max \in { bPool.peerHeights[p] : p \in correctPeers }:
            \A p \in correctPeers: bPool.peerHeights[p] <= max \* max is the maximum

              
Correctness1 == state = "finished" => 
    blockPool.height >= MaxCorrectPeerHeight(blockPool)


Correctness2 == 
   \A p \in CORRECT: 
        \/ p \notin blockPool.peerIds 
        \/ [] (state = "finished" => blockPool.height >= blockPool.peerHeights[p] - 1)
          

Termination == WF_turn(FlipTurn) => <>(state = "finished") 
     
\* a few simple properties that trigger counterexamples

\* Shows execution in which peer set is empty
PeerSetIsNeverEmpty == blockPool.peerIds /= {}

\* Shows execution in which state = "finished" and MaxPeerHeight is not equal to 1
StateNotFinished == 
    state /= "finished" \/ MaxPeerHeight(blockPool) = 1
        
=============================================================================
          
\*=============================================================================
\* Modification History
\* Last modified Tue Apr 07 23:49:10 CEST 2020 by igor
\* Last modified Tue Apr 07 15:58:26 CEST 2020 by zarkomilosevic
\* Created Tue Feb 04 10:36:18 CET 2020 by zarkomilosevic
