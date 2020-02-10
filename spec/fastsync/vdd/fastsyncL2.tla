----------------------------- MODULE fastsyncL2 -----------------------------
(*
 L2 specification of the fast sync protocol.
 
 In this specification, we have two parties:
    - the node (state machine) that is doing fastsync
    - the peersState (the peers with which node interacts to download blocks)

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

\* the variables of the peers providing blocks
VARIABLES                                   
  peersState
  (*
  peersState [
    peerHeights,                             \* track peer heights
    statusRequested,                         \* true if peers received statusRequest and not all peers responded
    statusResponseSentBy,                    \* set of peers that responded to the latest statusRequest
    blocksRequested,                         \* set of blockRequests received that are not answered yet 
    turn                                     \* sending statusResponse or blockResponse
  ]
  *) 
 
 \* the variables for the network and scheduler
 VARIABLES
  turn,                                     \* who is taking the turn: "Peers" or "Node" 
  inMsg,
  outMsg   
  
  
(* the variables of the node *)  
nvars == <<state, blockPool>>
  

InMsgs ==
    {NoMsg}
        \union
    [type: {"statusResponse"}, peerId: AllPeerIds, height: Heights]
        \union
    [type: {"blockResponse"}, peerId: AllPeerIds, block: Blocks]

FaultyInMsgs ==
    [type: {"statusResponse"}, peerId: Faulty, height: Heights]
        \union
    [type: {"blockResponse"}, peerId: Faulty, block: Blocks]    

OutMsgs ==
    {NoMsg}
        \union
    [type: {"statusRequest"}]    
        \union  
    [type: {"blockRequest"}, peerId: AllPeerIds, height: Heights]  
        

(********************************** NODE ***********************************)

InitNode == 
    \E startHeight \in Heights: 
        /\    blockPool = [
                height |-> startHeight,
                peerIds |-> {},
                peerHeights |-> [p \in AllPeerIds |-> NilHeight],     \* no peer height is known
                blockStore |-> [h \in Heights |-> NilBlock],
                receivedBlocks |-> [h \in Heights |-> NilPeer],
                pendingBlocks |-> [h \in Heights |-> NilPeer] 
            ]
       /\ state = IF startHeight <= MAX_HEIGHT - 1 THEN "running" ELSE "finished"

\* using this operator we capture assumption that correct processes always respond timely
MsgOnTime(msg, msgOnTime) == 
    IF msg.peerId \in Correct 
    THEN TRUE 
    ELSE msgOnTime  
    
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
HandleStatusResponse(msg, bPool, msgOnTime) == 
    IF /\ msg.peerId \notin bPool.peerIds 
       /\ MsgOnTime(msg, msgOnTime) 
    THEN    \* a new peer and a timely response 
        LET pIds == bPool.peerIds \union {msg.peerId} IN
        LET pHeights == [bPool.peerHeights EXCEPT ![msg.peerId] = msg.height] IN
        [bPool EXCEPT 
            !.peerIds = pIds,
            !.peerHeights = pHeights
         ]                   
    ELSE RemovePeer(msg.peerId, bPool)   \* the peer has sent us duplicate status message or not on time
        
        
HandleBlockResponse(msg, bPool, msgOnTime) == 
    LET h == msg.block.height IN
    IF /\ msg.peerId \in bPool.peerIds
       /\ bPool.blockStore[h] = NilBlock 
       /\ bPool.pendingBlocks[h] = msg.peerId 
       /\ MsgOnTime(msg, msgOnTime)  
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
    LET peersThatCanServe == {p \in bPool.peerIds: 
                /\ bPool.peerHeights[p] >= bPool.height 
                /\ LET peerPendingRequests == 
                    {i \in Heights: i >= bPool.height /\ bPool.pendingBlocks[i] = p}
                   IN Cardinality(peerPendingRequests) < PEER_MAX_REQUESTS } IN
    
    LET pendingBlocks == 
        {i \in Heights: i >= bPool.height /\ bPool.pendingBlocks[i] /= NilPeer} IN
    
    IF \/ peersThatCanServe = {} 
       \/ Cardinality(pendingBlocks) > TARGET_PENDING 
    THEN NilPeer 
    ELSE CHOOSE p \in peersThatCanServe: TRUE    \* TODO: Maybe introduce nondeterminism for peer selection
    
       
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
        

\* TODO: add timer based decision in case peerIds is empty
GetState(bPool) == 
    LET maxPeerHeight == 
        CHOOSE max \in Heights: 
            \A p \in bPool.peerIds: bPool.peerHeights[p] <= max IN
    
    IF bPool.height <= maxPeerHeight - 1 THEN "running" ELSE "finished" 


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
          

HandleResponse(msg, bPool, msgOnTime) == 
    IF msg = NoMsg 
    THEN bPool
    ELSE IF msg.type = "statusResponse" 
        THEN HandleStatusResponse(msg, bPool, msgOnTime)
        ELSE HandleBlockResponse(msg, bPool, msgOnTime)
    
NodeStep ==
   \E msgOnTime \in BOOLEAN:
        LET bPool == HandleResponse(inMsg, blockPool, msgOnTime) IN
        LET nbPool == ExecuteBlocks(bPool) IN
        LET msgAndPool == CreateRequest(nbPool) IN 
   
        /\ state' = GetState(msgAndPool.pool)
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


TurnResponse == {"status", "block"}

InitPeers ==
    \E pHeights \in [AllPeerIds -> Heights]: 
        peersState = [
         peerHeights |-> pHeights,
         statusRequested |-> FALSE,
         statusResponseSentBy |-> {},
         blocksRequested |-> {}
    ]
            
HandleStatusRequest(pState) == 
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
         THEN HandleStatusRequest(pState)
         ELSE HandleBlockRequest(msg, pState)
                

CreateStatusResponse(peer, pState) == 
    LET m == [type |-> "statusResponse", peerId |-> peer, height |-> pState.peerHeights[peer]] IN
    LET npState == 
        [pState EXCEPT 
            !.statusResponseSentBy = pState.statusResponseSentBy \union {peer}      
        ] IN
    [msg |-> m, peers |-> npState] 
             
CreateBlockResponse(msg, pState) == 
    LET m == [type |-> "blockResponse", peerId |-> msg.peerId, block |-> CorrectBlock(msg.height)] IN
    LET npState == 
        [pState EXCEPT 
            !.blocksRequested = pState.blocksRequested \ {msg}      
        ] IN
    [msg |-> m, peers |-> npState]   


CreateResponse(pState) == 
    LET correctNotSentStatusResponse == 
            {p \in AllPeerIds: p \in Correct \ pState.statusResponseSentBy} IN
    
    \/ /\ pState.statusRequested 
       /\ correctNotSentStatusResponse /= {} 
       /\ pState.blocksRequested /= {}
       /\ \E t \in TurnResponse:
            \/ /\ t = "status"
               /\ \E p \in correctNotSentStatusResponse: 
                    CreateStatusResponse(p, pState)
            \/ /\ t = "block"        
               /\ \E msg \in pState.blocksRequested:
                    CreateBlockResponse(msg, pState)
    
    \/ /\ pState.statusRequested 
       /\ correctNotSentStatusResponse /= {} 
       /\ pState.blocksRequested = {}
       /\ \E p \in correctNotSentStatusResponse: 
              LET msgAndPeers == CreateStatusResponse(p, pState) IN      
              /\ peersState' = msgAndPeers.peers
              /\ inMsg' = msgAndPeers.msg   
    
    
    \/ /\ (~pState.statusRequested \/ correctNotSentStatusResponse = Correct) 
       /\  pState.blocksRequested /= {}
       /\ \E msg \in pState.blocksRequested:
              LET msgAndPeers == CreateBlockResponse(msg, pState) IN      
              /\ peersState' = msgAndPeers.peers
              /\ inMsg' = msgAndPeers.msg   
    
                    
    \/ /\ (~pState.statusRequested \/ correctNotSentStatusResponse = Correct)
       /\ pState.blocksRequested = {}
       /\ peersState' = pState
       /\ inMsg' = NoMsg                  
    
\* peersState consumes a message and update it's local state. It then makes a single step, i.e., it sends at most single message.
\* message sent could be either from correct processes as a result of received messages or faulty message. 
NextPeers ==
    LET pState == HandleRequest(outMsg, peersState) IN
    LET msgAndPeers == CreateResponse(pState) IN
    
    \/  /\ outMsg' = NoMsg                    \* correct peers respond
        /\ CreateResponse(pState) 
    
    \/  /\ outMsg' = NoMsg                    \* faulty peers respond
        /\ peersState' = pState
        /\ inMsg' \in FaultyInMsgs         
       

\* the composition of the node, the peers, the network and scheduler
Init ==
    /\ turn = "Peers"
    /\ inMsg = NoMsg
    /\ outMsg = [type |-> "statusRequest"]
    /\ InitNode
    /\ InitPeers

Next ==
    IF turn = "Peers"
    THEN
        /\ NextPeers
        /\ turn' = "Node"
        /\ UNCHANGED nvars
    ELSE
        /\ NextNode
        /\ turn' = "Peers"
        /\ UNCHANGED peersState  
        
 

\* properties to check
TypeOK ==
    /\ state \in States
    /\ inMsg \in InMsgs 
    /\ outMsg \in OutMsgs
    
\* a few simple properties that trigger counterexamples
NeverFinishAtMax == state = "finished" => blockPool.height = MAX_HEIGHT
    
    
    
=============================================================================
          
\*=============================================================================
\* Modification History
\* Last modified Mon Feb 10 18:11:58 CET 2020 by zarkomilosevic
\* Created Tue Feb 04 10:36:18 CET 2020 by zarkomilosevic
