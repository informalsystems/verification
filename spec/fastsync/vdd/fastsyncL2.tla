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

EXTENDS Integers 

CONSTANTS MAX_HEIGHT, NPEERS, F

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
  state,
  height,
  peerIds,
  peerHeights,
  blockStore
  

\* the variables of the environment
VARIABLES                                   
  envPeerHeights,                          \* corresponds to the "real" peer heights
  statusRequested,                         \* true if environment received statusRequest and not all peers responded
  statusResponseSentBy,                    \* set of peers that responded to the latest statusRequest
  blocksRequested                          \* set of blockRequests received that are not answered yet 
  
 VARIABLES
  turn,                                     \* who is taking the turn: "Environment" or "Node" 
  inMsg,
  outMsg   
  
  
(* the variables of the node *)  
nvars == <<state, height, peerIds, peerHeights, blockStore>>  

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
    /\ height \in Heights \ {MAX_HEIGHT}  
    /\ peerIds = {}
    /\ peerHeights = [p \in AllPeerIds |-> NilHeight]
    /\ blockStore = [h \in Heights |-> NilBlock]
    

\* we probably want to capture this differently
MsgOnTime(msg) == 
    IF msg.peerId \in Correct 
    THEN TRUE 
    ELSE \E res \in BOOLEAN: res  
     

OnStatusResponse == 
    /\ state = "running"
    /\ inMsg.type = "statusResponse"
    /\ inMsg' = NoMsg  
    /\ IF /\ inMsg.peerId \notin peerIds
          /\ MsgOnTime(inMsg) 
       THEN \* a new peer and a timely response 
            /\ peerIds' = peerIds \union {inMsg.peerId}
            /\ peerHeights' =
                    [ peerHeights EXCEPT ![inMsg.peerId] = inMsg.height ] 
       ELSE \* the peer has sent us duplicate status message or not on time
            /\ peerIds' = peerIds \ {inMsg.peerId}
            /\ peerHeights' =
                    [ peerHeights EXCEPT ![inMsg.peerId] = NilHeight]  
    /\ UNCHANGED <<state, height, blockStore>>

OnBlockResponse == 
    /\ state = "running"
    /\ inMsg.type = "blockResponse"
    /\ inMsg' = NoMsg  
    /\ IF /\ inMsg.peerId \in peerIds
          /\ blockStore[inMsg.block.height] = NilBlock \* and block request sent to that peer
       THEN
          /\ blockStore' =
                    [blockStore EXCEPT ![inMsg.block.height] = inMsg.block]
          /\ UNCHANGED <<peerIds, peerHeights>>             
       ELSE    
          /\ peerIds' = peerIds \ {inMsg.peerId}
          /\ peerHeights' =
                    [peerHeights EXCEPT ![inMsg.peerId] = NilHeight]  
          /\ UNCHANGED <<blockStore>>          
    /\ UNCHANGED <<state, height>>
        
    
NextNode ==
    \/ OnStatusResponse
    \/ OnBlockResponse
    \/ state = "finished" /\ UNCHANGED <<nvars, inMsg, outMsg>>
    

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
   \/ \E peer \in peerIds \ statusResponseSentBy:
            /\ inMsg' = CreateStatusResponseMessage(peer, envPeerHeights[peer]) 
            /\ LET peersResponded == statusResponseSentBy \union {peer} IN
                    IF peersResponded = peerIds    \* all correct peers have responded 
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
        /\ UNCHANGED <<outMsg, envvars>>  
        
 
\* properties to check
TypeOK ==
    /\ state \in States
    /\ inMsg \in InMsgs
    /\ outMsg \in OutMsgs
    /\ height \in Heights \cup {NilHeight}
    /\ peerIds \subseteq AllPeerIds
    /\ peerHeights \in [AllPeerIds -> Heights \cup {NilHeight}]
    /\ blockStore \in [Heights -> Blocks \cup {NilBlock}]
    /\ envPeerHeights \in [AllPeerIds -> Heights]
    /\ statusRequested \in BOOLEAN
    /\ statusResponseSentBy \subseteq AllPeerIds 
    \* /\ blocksRequested \in [type: {"blockRequest"}, peerId: AllPeerIds, height: Heights]
          
=============================================================================
\* Modification History
\* Last modified Wed Feb 05 17:10:49 CET 2020 by zarkomilosevic
\* Created Tue Feb 04 10:36:18 CET 2020 by zarkomilosevic
