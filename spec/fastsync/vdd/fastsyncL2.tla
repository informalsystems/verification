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

- node is initialised with a set of peers with which messages can be exchanged
- peers can be removed (in case they misbehave) but they cannot be added
- some numbers of peers is faulty (correct and faulty peer ids are input parameter)
- peers do not modify its height, i.e., we take a snaphsot of the system and try to sync as much as we can
within that shapshot; therefore StatusRequest message is sent only once
- we assume synchronous communication between correct processes (node and correct peers) and model communication
with asycnhronous rpc calls, i.e, every request receives corresponding reply 
- faulty processes can send arbitrary messages (even if they are not requested)
- fast sync should terminate with at least a block height that is equal to the maximum height of the correct peer

This spec can be extended allong the following lines to capture full fast sync problem:

1) Node can establish connections to other peers during fast sync protocol. This should probably be modelled by having
additional input message received by Node (AddPeer). This should be relatively easily supported
as it shouldn't significantly affect termination conditions. More preciselly, the properties should be very similar 
in case we bound eventually reception of AddPeer messages; otherwise we can't terminate as AddPeer message can 
always delay termination.

2) Peers modify its height (blockchain grows) and node wants to try to sync to the latest block. In this case, node
needs to send multiple StatusRequest messages. We might want to try to model this variant as multi-round version of this
spec where round corresponds to a single loop (StatusRequest sent -> All corresponding StatusResponses received -> Termination 
condition satisfied). In this case starting next round could be modelled as an external event (NextRound). 
Termination condition would then be constrained of eventually stopping to receive NextRound events.   
*)

EXTENDS Integers, FiniteSets, Sequences 

CONSTANTS MAX_HEIGHT, 
          CORRECT, 
          FAULTY, 
          TARGET_PENDING, 
          PEER_MAX_REQUESTS

\* the set of potential heights
Heights == 1..MAX_HEIGHT

\* simplifies execute blocks logic. Used only in block store. 
HeightsPlus == 1..MAX_HEIGHT+1

\* the set of all peer ids the node can receive a message from
AllPeerIds == CORRECT \union FAULTY

Blocks == [height: Heights, wellFormed: BOOLEAN, lastCommit: BOOLEAN]

\* correct node will create always valid blocks, i.e., wellFormed = true and lastCommit = true. 
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
  state,                                     \* running or finished                              
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
    statusRequested,                         \* set of statusRequests received that are not answered yet 
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
    [type: {"statusResponse"}, peerId: FAULTY, height: Heights]
        \union
    [type: {"blockResponse"}, peerId: FAULTY, block: Blocks]    

OutMsgs ==
    {NoMsg}
        \union
    [type: {"statusRequest"}, peerIds: SUBSET AllPeerIds \ {}] \* NOTE: peerIds is a set of ids    
        \union  
    [type: {"blockRequest"}, peerId: AllPeerIds, height: Heights]  
        

(********************************** NODE ***********************************)

InitNode == 
    \E startHeight \in Heights: 
        \E pIds \in SUBSET AllPeerIds:
        /\ pIds /= {}
        /\ startHeight <= MAX_HEIGHT - 1
        /\ blockPool = [
                height |-> startHeight,
                peerIds |-> pIds, 
                peerHeights |-> [p \in AllPeerIds |-> NilHeight],     \* no peer height is known
                blockStore |-> [h \in HeightsPlus |-> NilBlock],
                receivedBlocks |-> [h \in Heights |-> NilPeer],
                pendingBlocks |-> [h \in Heights |-> NilPeer] 
           ]
       /\ state = "running" 
       

\* using this operator we capture assumption that correct processes always respond timely
MsgOnTime(msg, randomFlag) == 
    IF msg.peerId \in CORRECT 
    THEN TRUE 
    ELSE randomFlag  
    
\* Remove faulty peer.
\* Returns new block pool. If the peer is alredy removed, returns input value.  
RemovePeer(peer, bPool) ==       
    LET pIds == bPool.peerIds \ {peer} IN
    LET pHeights == [bPool.peerHeights EXCEPT ![peer] = NilHeight] IN
    LET failedRequests == {h \in Heights: h >= bPool.height /\ bPool.pendingBlocks[h] = peer} IN
    LET pBlocks == 
    [h \in Heights |-> IF h \in failedRequests THEN NilPeer ELSE bPool.pendingBlocks[h]] IN  
    LET rBlocks == 
    [h \in Heights |-> IF h \in failedRequests THEN NilPeer ELSE bPool.receivedBlocks[h]] IN
    LET bStore == 
    [h \in Heights |-> IF h \in failedRequests THEN NilBlock ELSE bPool.blockStore[h]] IN  \* Should we remove received block in this case?
    
    IF peer \in bPool.peerIds     
    THEN [bPool EXCEPT 
            !.peerIds = pIds,
            !.peerHeights = pHeights,
            !.pendingBlocks = pBlocks,
            !.receivedBlocks = rBlocks,
            !.blockStore = bStore
          ]                              
    ELSE bPool
     
\* If valid (and timely) status response, update peerHeights.
\* If invalid message, then remove peer.
\* Returns new block pool.                             
HandleStatusResponse(msg, bPool, randomFlag) == 
    LET peerHeight == bPool.peerHeights[msg.peerId] IN     
    IF /\ msg.peerId \in bPool.peerIds 
       /\ MsgOnTime(msg, randomFlag)
       /\ msg.height >= peerHeight  
    THEN    \* a correct and timely response 
        LET pHeights == [bPool.peerHeights EXCEPT ![msg.peerId] = msg.height] IN
        [bPool EXCEPT !.peerHeights = pHeights]                   
    ELSE RemovePeer(msg.peerId, bPool)   \* the peer has sent us duplicate status message or not on time or it was not solicited response
        
        
HandleBlockResponse(msg, bPool, randomFlag) == 
    LET h == msg.block.height IN
    IF /\ msg.peerId \in bPool.peerIds
       /\ bPool.blockStore[h] = NilBlock 
       /\ bPool.pendingBlocks[h] = msg.peerId 
       /\ MsgOnTime(msg, randomFlag)  
    THEN LET bStore == [bPool.blockStore EXCEPT ![h] = msg.block] IN 
         LET rBlocks == [bPool.receivedBlocks EXCEPT![h] = msg.peerId] IN   
         [bPool EXCEPT 
            !.blockStore = bStore,
            !.receivedBlocks = rBlocks
         ]  
    ELSE RemovePeer(msg.peerId, bPool)
                       

MaxPeerHeight(bPool) == 
    IF bPool.peerIds = {}
    THEN 0 \* no peers, just return 0
    ELSE CHOOSE max \in { bPool.peerHeights[p] : p \in bPool.peerIds }:
            \A p \in bPool.peerIds: bPool.peerHeights[p] <= max \* max is the maximum
    

\* returns next height for which request should be sent.
\* returns NilHeight in case there is no height for which request can be sent.
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
            /\ bPool.blockStore[h] = NilBlock
        }
    IN 
    Cardinality(peerPendingRequests)

\* Returns peer that can serve block for given height. 
\* Returns NilPeer in case there are no such peer.
FindPeerToServe(bPool, h) == 
    LET peersThatCanServe == { p \in bPool.peerIds: 
                /\ bPool.peerHeights[p] >= h 
                /\ NumOfPendingRequests(bPool, p) <= PEER_MAX_REQUESTS } IN
    
    LET pendingBlocks == 
        {i \in Heights: 
            /\ i >= bPool.height 
            /\ bPool.pendingBlocks[i] /= NilPeer
            /\ bPool.blockStore[i] = NilBlock
        } IN
    
    IF \/ peersThatCanServe = {} 
       \/ Cardinality(pendingBlocks) > TARGET_PENDING 
    THEN NilPeer 
    ELSE CHOOSE p \in peersThatCanServe: TRUE    \* TODO: Maybe introduce nondeterminism for peer selection
    
       
\* Make a request for a block (if possible) and returns request message and block poool.
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
    IF /\ bPool.height < MaxPeerHeight(bPool) 
       /\ bPool.peerIds /= {}  
    THEN "running" 
    ELSE "finished" 


(*
    - block bStore[bPool.height - 1] is trusted block and it defines next validator set that is executing block at bPool.height
    - last commit for the block at height bPool.height is part of the block at height bPool.height + 1
    - validity of last commit for block at bPool.height therefore depends on the block bStore[bPool.height - 1]. It consists in verifying
      if > 2/3 of the voting power of the trusted validator set has signed it.
    - block at height h is valid if it is wellformed and if last commit from the block at height h+1 is valid and signs the block at height h
*)

IsValidCommit(trustedBlock, block) ==
    /\ trustedBlock.height = block.Height - 2 
    /\ block.lastCommit
    
IsValidBlock(trustedCommit, block) == 
    /\ trustedCommit 
    /\ block.wellFormed
    
\* Tries to execute next block in the pool, i.e., defines block validation logic. 
\* Returns new block pool (peers that has send invalid blocks are removed).
ExecuteBlocks(bPool) ==  
    LET bStore == bPool.blockStore IN
    LET block1 == bStore[bPool.height] IN
    LET block2 == bStore[bPool.height+1] IN
    
    IF block1 = NilBlock \/ block2 = NilBlock \* we don't have two next consequtive blocks
    THEN bPool   
    ELSE IF ~IsValidCommit(bStore[bPool.height - 1], block2) 
         THEN RemovePeer(bPool.receivedBlocks[block2.height], bPool)
         ELSE IF IsValidBlock(block2.lastCommit, block1)
              THEN \* all good, execute block at position height
                 [bPool EXCEPT !.height = bPool.height + 1]
              ELSE  
                 RemovePeer(bPool.receivedBlocks[block1.height], bPool)        

              
HandleResponse(msg, bPool, randomFlag) == 
    IF msg = NoMsg 
    THEN bPool
    ELSE IF msg.type = "statusResponse" 
        THEN HandleStatusResponse(msg, bPool, randomFlag)
        ELSE HandleBlockResponse(msg, bPool, randomFlag)
    
NodeStep ==
   \E randomFlag \in BOOLEAN:
        LET bPool == HandleResponse(inMsg, blockPool, randomFlag) IN
        LET nbPool == ExecuteBlocks(bPool) IN
        LET msgAndPool == CreateRequest(nbPool) IN 
        LET nstate == GetState(msgAndPool.pool) IN
   
        /\ state' = nstate
        /\ blockPool' = msgAndPool.pool
        /\ outMsg' = msgAndPool.msg
        /\ inMsg' = NoMsg
                            
                
\* If node is running, then in every step we try to create blockRequest.
\* In addition, input message (if exists) is consumed and processed. 
NextNode ==
    \/ /\ state /= "finished" 
       /\ NodeStep  
              
    \/ /\ state = "finished" 
       /\ UNCHANGED <<nvars, inMsg, outMsg>>
    

(********************************** Peers ***********************************)


TurnResponse == {"status", "block"}

InitPeers ==
    \E pHeights \in [AllPeerIds -> Heights]: 
        peersState = [
         peerHeights |-> pHeights,
         statusRequested |-> {},
         blocksRequested |-> {},
         turn |-> "status"
    ]
            
HandleStatusRequest(msg, pState) == 
    [pState EXCEPT 
        !.statusRequested = msg.peerIds
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

CreateStatusResponse(peer, pState, randomHeight) ==  
    LET m == 
        IF peer \in CORRECT 
        THEN [type |-> "statusResponse", peerId |-> peer, height |-> pState.peerHeights[peer]]
        ELSE [type |-> "statusResponse", peerId |-> peer, height |-> randomHeight] IN
    LET npState == 
        [pState EXCEPT 
            !.statusRequested = pState.statusRequested \ {peer}       
        ] IN
    [msg |-> m, peers |-> npState] 
             
CreateBlockResponse(msg, pState, randomBlock) == 
    LET m == 
        IF msg.peerId \in CORRECT
        THEN [type |-> "blockResponse", peerId |-> msg.peerId, block |-> CorrectBlock(msg.height)]
        ELSE [type |-> "blockResponse", peerId |-> msg.peerId, block |-> randomBlock] IN
    LET npState == 
        [pState EXCEPT 
            !.blocksRequested = pState.blocksRequested \ {msg}      
        ] IN
    [msg |-> m, peers |-> npState]   

CreateResponse(pState) == 
    \/ /\ pState.statusRequested /= {}  
       /\ pState.blocksRequested /= {}
       /\ \E t \in TurnResponse:
            \/ /\ t = "status"
               /\ \E h \in Heights: 
                  \E peer \in pState.statusRequested:   
                    LET msgAndPeers == CreateStatusResponse(peer, pState, h) IN
                    /\ peersState' = msgAndPeers.peers
                    /\ inMsg' = msgAndPeers.msg   
                                                               
            \/ /\ t = "block"        
               /\ \E msg \in pState.blocksRequested:
                   \E block \in Blocks:
                    LET msgAndPeers == CreateBlockResponse(msg, pState, block) IN      
                    /\ peersState' = msgAndPeers.peers
                    /\ inMsg' = msgAndPeers.msg  
    
    \/ /\ pState.statusRequested /= {}  
       /\ pState.blocksRequested = {}
       /\ \E h \in Heights: 
            \E peer \in pState.statusRequested:   
                LET msgAndPeers == CreateStatusResponse(peer, pState, h) IN
                /\ peersState' = msgAndPeers.peers
                /\ inMsg' = msgAndPeers.msg     
    
    
    \/ /\ pState.statusRequested = {} 
       /\ pState.blocksRequested /= {}
       /\ \E msg \in pState.blocksRequested:
            \E block \in Blocks:
                LET msgAndPeers == CreateBlockResponse(msg, pState, block) IN      
                /\ peersState' = msgAndPeers.peers
                /\ inMsg' = msgAndPeers.msg  
                    
    \/ /\ pState.statusRequested = {}
       /\ pState.blocksRequested = {}
       /\ peersState' = pState
       /\ inMsg' = NoMsg                  
    
\* Peers consume a message and update it's local state. It then makes a single step, i.e., it sends at most single message.
\* Message sent could be either response to a request or faulty message (sent by faulty processes). 
NextPeers ==
    LET pState == HandleRequest(outMsg, peersState) IN
    
    \/  /\ outMsg' = NoMsg                    \* correct peers respond
        /\ CreateResponse(pState) 
    
    \/  /\ outMsg' = NoMsg                    \* faulty peers respond
        /\ peersState' = pState
        /\ inMsg' \in FaultyInMsgs         
       

\* the composition of the node, the peers, the network and scheduler
Init ==
    /\ InitNode
    /\ InitPeers
    /\ turn = "Peers"
    /\ inMsg = NoMsg
    /\ outMsg = [type |-> "statusRequest", peerIds |-> blockPool.peerIds]
    
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
    /\ turn \in {"Peers", "Node"}
    /\ peersState \in [
         peerHeights: [AllPeerIds -> Heights \union {NilHeight}],
         statusRequested: SUBSET AllPeerIds,
         blocksRequested: SUBSET [type: {"blockResponse"}, peerId: AllPeerIds, block: Blocks],
         turn: {"status", "block"}
        ]
    /\ blockPool \in [
                height: Heights,
                peerIds: SUBSET AllPeerIds, 
                peerHeights: [AllPeerIds -> Heights \union {NilHeight}],     
                blockStore: [HeightsPlus -> Blocks \union {NilBlock}],
                receivedBlocks: [Heights -> AllPeerIds \union {NilPeer}],
                pendingBlocks: [Heights -> AllPeerIds \union {NilPeer}]
           ] 
           
           
    
\* a few simple properties that trigger counterexamples
NeverFinishAtMax == state = "finished" => blockPool.height < MaxPeerHeight(blockPool) 

NeverFinishWithEmptyPeerSet == state = "finished" => blockPool.peerIds = {}

\* if there is at least single correct process in peerSet, then blockPool.height >= maxCorrect - 1

\* Termination condition
Termination == state = "finished" => 
    \/ blockPool.peerIds = {} 
    \/ blockPool.height >= MaxPeerHeight(blockPool)
        
=============================================================================
          
\*=============================================================================
\* Modification History
\* Last modified Mon Feb 24 17:30:09 CET 2020 by zarkomilosevic
\* Created Tue Feb 04 10:36:18 CET 2020 by zarkomilosevic
