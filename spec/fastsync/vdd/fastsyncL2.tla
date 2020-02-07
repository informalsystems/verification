----------------------------- MODULE fastsyncL2 -----------------------------
(*
 L2 specification of the fast sync protocol.
 
 In this specification, we have two parties:
    - the node (state machine) that is doing fastsync
    - the environment (the peers with which node interacts to download blocks)

We assume a system in which one node is trying to sync with the blockchain 
(replicated state machine) by downloading blocks and executing transactions 
(part of the block) agaings the application, and the set of full nodes 
(we call them peers) that are block providers.

Peers can be faulty, and we don't make any assumption about rate of correct/faulty nodes in the
node peerset (i.e., they can all be faulty). Processes (client and peers) communicate
by message passing. They exchange the following messages:

- StatusRequest
- StatusReply
- BlockRequest
- BlockReply
 
Correct peers are part of the replicated state machine, i.e., they manage
blockchain and execute transactions against the same deterministic application A.
We assume Tendermint failure model, i.e., given a trusted header h, we assume that >2/3 of voting power will behave
correctly until time h.Time + TRUSTED_PERIOD. We don't make any assumptions about behavior of faulty processes.

In this spec we assume a simpler problem (compared to complete fast-sync) defined with the following assumptions: 

- we are given fixed set of peers with various distribution of heights
- peers can be removed (in case they misbehave) but they cannot be added
- some numbers of peers is faulty (input parameter)
- peers do not modify its height, i.e., we take a snaphsot of the system and try to sync as much as we can
within that shapshot; therefore StatusRequest is sent only once
- we assume synchronous communication between correct processes (node and correct peers) and model communication
with asycnhronous rpc calls, i.e, every request receives corresponding reply 
- faulty processes can send arbitrary messages (even if they are not requested)
- fast sync should terminate with at least a block height that is equal to the maximum height of the correct peer
- termination should happen during the period when node is not under DDoS, i.e., we assume that 
response is generated only if the node asked by sending a request          
*)

EXTENDS Integers, FiniteSets, Sequences 

CONSTANTS MAX_HEIGHT, NPEERS, F, TARGET_PENDING, PEER_MAX_REQUESTS

\* the set of potential heights
Heights == 1..MAX_HEIGHT
\* the set of all peer ids the node can receive a message from
AllPeerIds == 1..NPEERS

Correct == 1..NPEERS-F
Faulty == NPEERS-F+1..NPEERS


\* correct node will create always valid blocks, i.e., wellFormed = true and lastCommit = true. 
Blocks == [height: Heights, wellFormed: BOOLEAN, lastCommit: BOOLEAN]

CorrectBlock(h) == [height |-> h, wellFormed |-> TRUE, lastCommit |-> TRUE]

NilBlock == [height |-> 0, wellFormed |-> TRUE, lastCommit |-> TRUE]

\* a special value for an undefined height
NilHeight == 0

\* a special value for an undefined peer
NilPeer == 0

States == { "running", "finished" }

NoMsg == [type |-> "None"]

\* the variables of the node running fastsync
VARIABLES
  state,                                  \* running or finished
  blockPool
  (*
  blockPool [
      height,                                 \* current height we are trying to sync. Last block executed is height - 1
      peerIds,                                \* set of peers node is connected to      
      peerHeights,                            \* map of peer ids to its (stated) height
      blockStore,                             \* map of heights to (received) blocks
      receivedBlocks,                         \* map of heights to peer that has sent us the block (stored in blockStore)
      pendingBlocks                           \* map of heights to peer to which block request has been sent
  ]
  *)

\* the variables of the environment
VARIABLES                                   
  envPeerHeights,                          \* track peer heights
  statusRequested,                         \* true if environment received statusRequest and not all peers responded
  statusResponseSentBy,                    \* set of peers that responded to the latest statusRequest
  blocksRequested                          \* set of blockRequests received that are not answered yet 
  
 \* the variables for the network and scheduler
 VARIABLES
  turn,                                     \* who is taking the turn: "Environment" or "Node" 
  inMsg,
  outMsg   
  
  
(* the variables of the node *)  
nvars == <<state, blockPool>>

(* the variables of the environment *)
envvars == <<envPeerHeights, statusRequested, statusResponseSentBy, blocksRequested>>    

InMsgs ==
    {NoMsg}
        \union
    [type: {"statusResponse"}, peerId: AllPeerIds, height: Heights]
        \union
    [type: {"blockResponse"}, peerId: AllPeerIds, block: Blocks]

OutMsgs ==
    {NoMsg}
        \union
    [type: {"statusRequest"}]    
        \union  
    [type: {"blockRequest"}, peerId: AllPeerIds, height: Heights]  
        

(********************************** NODE ***********************************)

InitNode ==
    /\ state = "running"
    /\ \E startHeight \in Heights: 
            blockPool = [
                height |-> startHeight,
                peerIds |-> {},
                peerHeights |-> [p \in AllPeerIds |-> NilHeight],     \* no peer height is known
                blockStore |-> [h \in Heights |-> NilBlock],
                receivedBlocks |-> [h \in Heights |-> NilPeer],
                pendingBlocks |-> [h \in Heights |-> NilPeer] 
            ]
       

\* using this operator we capture assumption that correct processes always respond timely
MsgOnTime(msg) == 
    IF msg.peerId \in Correct 
    THEN TRUE 
    ELSE \E res \in BOOLEAN: res  
    
\* remove faulty peer.
\* returns new bPool. If peer is alredy removed, return input value.  
RemovePeer(peer, bPool) ==       
    LET pIds == bPool.peerIds \ {peer} IN
    LET pHeights == [bPool.peerHeights EXCEPT ![peer] = NilHeight] IN
    LET failedRequests == {h \in Heights: bPool.pendingBlocks[h] = peer} IN
    LET pBlocks == 
    [h \in Heights |-> IF h \in failedRequests THEN NilPeer ELSE bPool.pendingBlocks[h]] IN  
    LET bStore == 
    [h \in Heights |-> IF h \in failedRequests THEN NilBlock ELSE bPool.blockStore[h]] IN
    
    IF peer \in bPool.peerIds     
    THEN [bPool EXCEPT 
            !.peerIds = pIds,
            !.peerHeights = pHeights,
            !.pendingBlocks = pBlocks,
            !.blockStore = bStore
          ]                              
    ELSE bPool
     
\* if valid (and timely) status response, update peerIds and peerHeights.
\* if invalid message, then remove peer (update nPeerVars)
\* returns <<newPeerSet, newPeerHeights, newBlockStore, newReceivedBlocks, newPendingBlocks>>                                     
HandleStatusResponse(msg, bPool) == 
    IF /\ msg.peerId \notin bPool.peerIds /\ MsgOnTime(msg) 
    THEN    \* a new peer and a timely response 
        LET pIds == bPool.peerIds \union {msg.peerId} IN
        LET pHeights == [bPool.peerHeights EXCEPT ![msg.peerId] = msg.height] IN
        [bPool EXCEPT 
            !.peerIds = pIds,
            !.peerHeights = pHeights
         ]                   
    ELSE RemovePeer(msg.peerId, bPool)   \* the peer has sent us duplicate status message or not on time
        
        
HandleBlockResponse(msg, bPool) == 
    LET h == msg.block.height IN
    IF /\ msg.peerId \in bPool.peerIds
       /\ bPool.blockStore[h] = NilBlock 
       /\ bPool.pendingBlocks[h] = msg.peerId 
    THEN LET bStore == [bPool.blockStore EXCEPT ![h] = msg.block] IN 
         LET rBlocks == [bPool.receivedBlocks EXCEPT![h] = msg.peerId] IN   
         [bPool EXCEPT 
            !.blockStore = bStore,
            !.receivedBlocks = rBlocks
         ]  
    ELSE RemovePeer(msg.peerId, bPool)
                       

\* returns next height for which request should be sent.
\* returns NilHeight in case there is no height for which request can be sent.
FindNextRequestHeight(bPool) == 
    LET S == {i \in Heights:  
                /\ i >= bPool.height 
                /\ bPool.blockStore[i] = NilBlock 
                /\ bPool.pendingBlocks[i] = NilPeer} IN
    IF S = {} 
        THEN NilHeight
    ELSE      
        CHOOSE min \in S:  \A h \in S: h >= min

FindPeerToServe(bPool) == 
    LET S == {p \in bPool.peerIds: 
                /\ bPool.peerHeights[p] >= bPool.height 
                /\ LET peerPendingRequests == 
                    {i \in Heights: i >= bPool.height /\ bPool.pendingBlocks[i] = p}
                   IN Cardinality(peerPendingRequests) < PEER_MAX_REQUESTS } IN
    
    IF S = {} THEN NilPeer ELSE CHOOSE p \in S: TRUE
    
       
(*
OnStatusResponse == 
    LET newPeerSetAndHeights == HandleStatusResponse(inMsg, peerIds, peerHeights) IN
    LET minHeight == FindNextRequestHeight(height, pendingBlocks) IN
    LET peer == FindPeerToServe(minHeight, newPeerSetAndHeights[1], newPeerSetAndHeights[2], pendingBlocks) IN
    LET msg == [type |-> "blockRequest", peerId |-> peer, height |-> minHeight] IN
    
    /\ peer /= NilPeer
    
    /\ peerIds' = newPeerSetAndHeights[1] 
    /\ peerHeights' = newPeerSetAndHeights[2]
    /\ outMsg' = msg 
    /\ pendingBlocks' = [pendingBlocks EXCEPT ![minHeight] = peer]  
    
    /\ UNCHANGED <<state, height, blockStore, receivedBlocks>>  
*)
              



CreateRequest(bPool) ==
    LET minHeight == FindNextRequestHeight(bPool) IN
    IF minHeight = NilHeight THEN [msg |-> NoMsg, pool |-> bPool]
    ELSE
     LET peer == FindPeerToServe(bPool) IN
     IF peer = NilPeer THEN [msg |-> NoMsg, pool |-> bPool]
     ELSE 
        LET m == [type |-> "blockRequest", peerId |-> peer, height |-> minHeight] IN
        LET newPool == [bPool EXCEPT 
                          !.pendingBlocks = [bPool.pendingBlocks EXCEPT ![m.height] = m.peerId]
                        ] IN
        [msg |-> m, pool |-> newPool]   
        


(*
OnBlockResponse == 
    \* compute next block store
    LET bStore == HandleBlockResponse(inMsg.block.height, inMsg.peerId, inMsg.block) IN
    IF bStore /= blockStore  \* try to execute blocks  
    THEN ProcessBlocks(bStore)
    ELSE \* bad response; remove peer 
        LET peerIdsHeightsBlocks == RemovePeer(inMsg.peerId) IN
        LET msg == 
        CreateRequest(peerIdsHeightsBlocks[1], peerIdsHeightsBlocks[2], peerIdsHeightsBlocks[3]) IN
      
        /\ peerIds' = peerIdsHeightsBlocks[1] 
        /\ peerHeights' = peerIdsHeightsBlocks[2]
        /\ outMsg' = msg 
        /\ pendingBlocks' = [peerIdsHeightsBlocks EXCEPT ![msg.height] = msg.PeerId]     
    
    /\ inMsg.type = "blockResponse"
    /\ inMsg' = NoMsg             
*)        

(*
ProcessStatusResponse(msg) == 
    LET newPeersState == HandleStatusResponse(inMsg, peerIds, peerHeights) IN
    LET minHeight == FindNextRequestHeight(height, pendingBlocks) IN
    LET peer == FindPeerToServe(minHeight, newPeerSetAndHeights[1], newPeerSetAndHeights[2], pendingBlocks) IN
    LET msg == [type |-> "blockRequest", peerId |-> peer, height |-> minHeight] IN    
*)

GetState(bPool) == 
    LET maxPeerHeight == 
        CHOOSE max \in Heights: 
            \A p \in bPool.peerIds: bPool.peerHeights[p] <= max IN
    
    IF bPool.height = maxPeerHeight - 1 THEN "finished" ELSE "running"


ExecuteBlocks(bPool) ==  
    LET bStore == bPool.blockStore IN
    LET block1 == bStore[bPool.height] IN
    LET block2 == bStore[bPool.height+1] IN
    
    IF block1 = NilBlock \/ block2 = NilBlock \* we don't have two next consequtive blocks
    THEN bPool   
    ELSE IF ~block2.lastCommit 
         THEN RemovePeer(bPool.receivedBlocks[bPool.height+1], bPool)
         ELSE IF block1.wellFormed 
              THEN \* all good, execute block at position height
                 [bPool EXCEPT !.height = bPool.height + 1]
              ELSE  
                 RemovePeer(bPool.receivedBlocks[bPool.height], bPool)        
          

HandleResponse(msg, bPool) == 
    LET nbPool == 
        IF msg.type = "statusResponse" 
        THEN HandleStatusResponse(msg, bPool)
        ELSE HandleBlockResponse(msg, bPool) IN
                
    /\ LET nnbPool == ExecuteBlocks(nbPool) IN
       LET msgAndPool == CreateRequest(nnbPool) IN 
      
        /\ state' = GetState(msgAndPool.pool)
        /\ blockPool' = msgAndPool.pool
        /\ outMsg' = msgAndPool.msg
        /\ inMsg' = NoMsg
    
NodeStep ==
    \/ /\ inMsg /= NoMsg 
       /\ HandleResponse(inMsg, blockPool)
              
    \/ /\ inMsg = NoMsg  
       /\ LET bPool == ExecuteBlocks(blockPool) IN
          LET msgAndPool == CreateRequest(bPool) IN 
      
          /\ state' = GetState(msgAndPool.pool)
          /\ blockPool' = msgAndPool.pool
          /\ outMsg' = msgAndPool.msg
          /\ UNCHANGED inMsg
                     
                
\* If node is running, then in every step we try to create blockRequest.
\* In addition, input message (if exists) is consumed and processed. 
NextNode ==
    \/ /\ state = "running"
       /\ NodeStep  
              
    \/ /\ state = "finished" 
       /\ UNCHANGED <<nvars, inMsg, outMsg>>
    

(********************************** ENVIRONMENT ***********************************)


InitEnv ==
    /\ envPeerHeights \in [AllPeerIds -> Heights] 
    /\ statusRequested = FALSE
    /\ statusResponseSentBy = {}
    /\ blocksRequested = {}


CreateStatusResponseMessage(peer, h) == 
    IF peer \in Correct 
    THEN
        [type |-> "statusResponse", peerId |-> peer, height |-> h]
    ELSE 
        \E anyHeight \in Heights:
            LET msg == [type |-> "statusResponse", peerId |-> peer, height |-> anyHeight] IN 
            msg
            
CreateBlockResponseMessage(peer, h) == 
    IF peer \in Correct 
    THEN
        [type |-> "blockResponse", peerId |-> peer, block |-> CorrectBlock(h)]
    ELSE 
        \E anyBlock \in Blocks:
            LET msg == [type |-> "blockResponse", block |-> anyBlock] IN 
            msg           
   
SendResponse ==   
   \/ \E peer \in blockPool.peerIds \ statusResponseSentBy:
            /\ inMsg' = CreateStatusResponseMessage(peer, envPeerHeights[peer]) 
            /\ LET peersResponded == statusResponseSentBy \union {peer} IN
                    IF peersResponded = blockPool.peerIds    \* all correct peers have responded 
                    THEN
                        /\ statusResponseSentBy' = {}
                        /\ statusRequested = FALSE
                    ELSE 
                        /\ statusResponseSentBy' = peersResponded
                        /\ UNCHANGED statusRequested  
            /\ UNCHANGED blocksRequested                  
            
   \/ /\ \E msg \in blocksRequested:
            /\ inMsg' = CreateBlockResponseMessage(msg.peerId, msg.height)               
            /\ blocksRequested' = blocksRequested \ {msg}
            /\ UNCHANGED <<statusResponseSentBy, statusRequested>>  
        
   \/ /\ UNCHANGED <<inMsg, statusResponseSentBy, blocksRequested>>  
        
OnStatusRequest ==
    /\ outMsg.type = "statusRequest"
    /\ outMsg' = NoMsg
    /\ statusRequested' = TRUE
    /\ statusResponseSentBy' = {}
    /\ UNCHANGED <<blocksRequested>>
    

OnBlockRequest ==
    /\ outMsg.type = "blockRequest"
    /\ outMsg' = NoMsg
    /\ blocksRequested' = blocksRequested \union {outMsg}
    /\ UNCHANGED <<statusRequested, statusResponseSentBy>>

\* environment consumes a message and update it's local state. It then makes a single step, i.e., it sends at most single message.
\* message sent could be either from correct processes as a result of received messages or faulty message. 
NextEnv ==
    \/ OnStatusRequest
        /\ SendResponse
    \/ OnBlockRequest
        /\ SendResponse
    \/ outMsg = NoMsg 
        /\ SendResponse
        /\ UNCHANGED <<outMsg>>
     
\* the composition of the node and the environment
Init ==
    /\ turn = "Environment"
    /\ inMsg = NoMsg
    /\ outMsg = [type |-> "statusRequest"]
    /\ InitNode
    /\ InitEnv

Next ==
    IF turn = "Environment"
    THEN
        /\ NextEnv
        /\ turn' = "Node"
        /\ UNCHANGED <<nvars, envPeerHeights>>
    ELSE
        /\ NextNode
        /\ turn' = "Environment"
        /\ UNCHANGED envvars  
        
 

\* properties to check
TypeOK ==
    /\ state \in States
    /\ inMsg \in InMsgs \union {}
    /\ outMsg \in OutMsgs
    
    
=============================================================================
          
\*=============================================================================
\* Modification History
\* Last modified Fri Feb 07 16:45:37 CET 2020 by zarkomilosevic
\* Created Tue Feb 04 10:36:18 CET 2020 by zarkomilosevic
