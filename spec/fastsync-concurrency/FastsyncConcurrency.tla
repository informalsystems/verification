------------------------ MODULE FastsyncConcurrency ------------------------

(***************************************************************************
 FastsyncConcurrency.tla
 
 Reference Go code :
 https://github.com/tendermint/tendermint/tree/master/blockchain/v2

 We assume the following architecture: 
        
      -----> peer 1 ------>   --------------------
      | .       .        .    | receive routine  |                    
      | .       .       -->   --------------------  
      | .       .       |              |     
      | .       .       |              |
      |----> peer n ----               v 
      |                       -------------------- 
      ----------------------- |   demux routine  |
                              --------------------         
                               ^             ^
                               |  |          |  |
                               |  |          |  |
                                  v             v           
                          -----------      ------------ 
                          | process |      | schedule | 
                          | routine |      | routine  |
                          -----------      ------------
 
 A routine r sends a message to a routine s by appending the message to
 the buffer rToS. A routine s receives a message from a buffer rToS by 
 writing the message at the head of the buffer rToS to the variable 
 sInboundMsg. 

 The buffers are as follows:
   - receiveToDemux is bounded (by BoundedBufferMaxLen), blocking 
   - demuxToProcess is unbounded (for model checking, bounded by 
     UnboundedBufferMaxLen)
   - processToDemux is bounded (by BoundedBufferMaxLen), blocking
   - demuxToSchedule is unbounded (for model checking, bounded by 
     UnboundedBufferMaxLen)
   - scheduleToDemux is bounded (by BoundedBufferMaxLen), blocking
   - nodeToPeer[peerID] is bounded (by BoundedBufferMaxLen), blocking with 
     timeout (can lose messages)
   - peerToReceive[peerID] is unbounded (for model checking, bounded by 
     UnboundedBufferMaxLen)
 ***************************************************************************)
 
EXTENDS Naturals, FiniteSets, Sequences

MT == STRING
a <: b == a
EmptySeq == <<>> <: Seq(MT)

CONSTANTS BoundedBufferMaxLen, UnboundedBufferMaxLen, NrPeers

ASSUME BoundedBufferMaxLen <= UnboundedBufferMaxLen

VARIABLES turn, \* which routine is taking a step
          receiveToDemux, \* buffer (bounded, blocking) from receive to demux routine
          demuxToProcess, \* buffer (unbounded) from demux to process routine
          processToDemux, \* buffer (bounded, blocking) from process to demux routine
          demuxToSchedule, \* buffer (unbounded) from demux to schedule routine
          scheduleToDemux, \* buffer (bounded, blocking) from scheudle to demux routine
          nodeToPeer, \* buffers (bounded, blocking with timeout) incoming to peers
          peerToReceive, \* buffers (unbounded) outgoing from peers
          peerTurn, \* the current peer that receives a block request and sends a block response
          receiveInboundMsg, \* inbound message to receive routine
          demuxInboundMsg, \* inbound message to demux routine
          processInboundMsg, \* inbound message to process routine
          scheduleInboundMsg, \* inbound message to schedule routine
          peerInboundMsg \* inbound messages to peers
          
(***************************************************************************
 Definitions
 ***************************************************************************)          
          
\* set of peers
PeerIDs == 1..NrPeers

vars == <<turn, 
          receiveToDemux, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux, 
          nodeToPeer, peerToReceive, peerTurn, 
          receiveInboundMsg, demuxInboundMsg, processInboundMsg, scheduleInboundMsg, peerInboundMsg>>          

buffers == <<receiveToDemux, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux>>
peer == <<nodeToPeer, peerToReceive, peerTurn>>
inboundMsgs == <<receiveInboundMsg, demuxInboundMsg, processInboundMsg, scheduleInboundMsg, peerInboundMsg>> 

\* set of messages that the peers send to the receive routine
peerMsgs == {"bcAddNewPeer", "bcBlockResponse", "bcNoBlockResponse", "bcRemovePeer", "bcStatusResponse"} 

\* set of messages that the process routine sends to the demux routine (forwarded to the schedule routine)
processToDemuxMsgs == {"pcBlockProcessed", "pcBlockVerificationFailure"} 

\* set of messages that the schedule routine sends to the demux routine (forwarded to the process routine)
scheduleToDemuxMsgs == {"scBlockReceived", "scFinishedEv", "scPeerError", "scSchedulerFail"} 

\* set of messages that the demux routine sends to the peers 
ioMsgs == {"bcStatusRequest", "scBlockRequest"}

\* set of messages that the demux routine sends to the process routine  
demuxToProcessMsgs == {"rProcessBlock", "scBlockReceived", "scFinishedEv", "scPeerError"}

\* set of messages that the demux routine sends to the schedule routine 
demuxToScheduleMsgs == peerMsgs \union processToDemuxMsgs 

\* special message denoting no message
noMsg == "noMsg"

\* set of all messages
Msgs == peerMsgs \union demuxToProcessMsgs \union processToDemuxMsgs \union demuxToScheduleMsgs 
            \union scheduleToDemuxMsgs \union ioMsgs \union {noMsg}
 
\* set of turns used to schedule the different routines
Turns == {"receiveRoutine", "demuxRoutine", "processRoutine", "scheduleRoutine", "peer"} 

(***************************************************************************
 Useful buffer predicates/operators.
 ***************************************************************************)

\* Check if a bounded buffer is full. A bounded buffer is full if the length of its queue 
\* is greater or equal to BoundedBufferMaxLen
IsFullBounded(buffer) ==
    Len(buffer) >= BoundedBufferMaxLen

\* Check if an unbounded buffer is full. An ubounded buffer is full if the length of its queue 
\* is greater or equal to UnboundedBufferMaxLen
IsFullUnbounded(buffer) ==
    Len(buffer) >= UnboundedBufferMaxLen
  
\* Check if a buffer is empty. A buffer is empty if it is equal to
\* the empty sequence
IsEmpty(buffer) ==
    buffer = EmptySeq

\* Get the value of the message at the head of the buffer's queue, without 
\* removing it from the queue
HeadMessage(buffer) ==
    Head(buffer) 

\* Compute the set of possible next values of a buffer by non-deterministically
\* appending a message from the set Messages to the tail of buffer
BufferSend(buffer, Messages) ==
    \* set of possible next values for buffer
    LET UpdatedBuffers == {Append(buffer, msg) : msg \in Messages \ {noMsg}} IN
    
    IF noMsg \in Messages
    \* do not append noMsg to the buffer
    THEN {buffer} \union UpdatedBuffers
    ELSE UpdatedBuffers

\* Compute the set of possible next values of a peer buffer by non-deterministically
\* appending a message from the set Messages to the tail of buffer
PeerBufferSend(peerBuffer, peerID, Messages) ==
    \* set of possible next values for peer buffer
    LET UpdatedPeerBuffers == {[peerBuffer EXCEPT ![peerID] = Append(peerBuffer[peerID], msg)] 
                                : msg \in Messages \ {noMsg}} IN
    
    IF noMsg \in Messages
    \* do not append noMsg to the buffer
    THEN {peerBuffer} \union UpdatedPeerBuffers
    ELSE UpdatedPeerBuffers

\* Compute the peerBuffer after broadcasting message 
PeerBufferBroadcast(peerBuffer, message) ==
    [peerID \in PeerIDs |-> Append(peerBuffer[peerID], message)]

\* Assign the message at the head of the buffer to inboundMsg  
AssignInboundMsg(inboundMsg, buffer) ==
    /\ inboundMsg = noMsg 
    /\ ~IsEmpty(buffer)
    /\ inboundMsg' = HeadMessage(buffer)
    /\ buffer' = Tail(buffer)     

\* Assign the message at the head of peerBuffer[peerID] to inboundPeerMsg[peerID]
AssignInboundPeerMsg(inboundPeerMsg, peerBuffer, peerID) ==
    /\ inboundPeerMsg[peerID] = noMsg 
    /\ ~IsEmpty(peerBuffer[peerID])
    /\ inboundPeerMsg' = [inboundPeerMsg EXCEPT ![peerID] = HeadMessage(peerBuffer[peerID])]
    /\ peerBuffer' = [peerBuffer EXCEPT ![peerID] = Tail(peerBuffer[peerID])]

(***************************************************************************
 Handle actions for buffers
 ***************************************************************************)

\* Handle receiveToDemux: assign the head of receiveToDemux to demuxInboundMsg  
HandleReceiveToDemux == 
    /\ AssignInboundMsg(demuxInboundMsg, receiveToDemux)
    /\ UNCHANGED <<demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<receiveInboundMsg, processInboundMsg, scheduleInboundMsg, peerInboundMsg>> 

\* Handle processToDemux: assign the head of processToDemux to demuxInboundMsg    
HandleProcessToDemux ==
    /\ AssignInboundMsg(demuxInboundMsg, processToDemux)
    /\ UNCHANGED <<receiveToDemux, demuxToProcess, scheduleToDemux, demuxToSchedule>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<receiveInboundMsg, processInboundMsg, scheduleInboundMsg, peerInboundMsg>>    

\* Handle scheduleToDemux: assign the head of scheduleToDemux to demuxInboundMsg        
HandleScheduleToDemux ==
    /\ AssignInboundMsg(demuxInboundMsg, scheduleToDemux)
    /\ UNCHANGED <<receiveToDemux, processToDemux, demuxToSchedule, demuxToProcess>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<receiveInboundMsg, processInboundMsg, scheduleInboundMsg, peerInboundMsg>>

\* Handle demuxToSchedule: assign the head of demuxToSchedule to scheduleInboundMsg    
HandleDemuxToSchedule ==
    /\ AssignInboundMsg(scheduleInboundMsg, demuxToSchedule)
    /\ UNCHANGED <<receiveToDemux, demuxToProcess, processToDemux, scheduleToDemux>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<receiveInboundMsg, demuxInboundMsg, processInboundMsg, peerInboundMsg>>   

\* Handle demuxToProcess: assign the head of demuxToProcess to processInboundMsg         
HandleDemuxToProcess ==
    /\ AssignInboundMsg(processInboundMsg, demuxToProcess)
    /\ UNCHANGED <<receiveToDemux, demuxToSchedule, scheduleToDemux, processToDemux>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<receiveInboundMsg, demuxInboundMsg, scheduleInboundMsg, peerInboundMsg>>      

\* Handle peerToReceive[peerTurn]: assign the head of peerToReceive[peerTurn] to 
\* receiveInboundMsg     
HandlePeerToReceive == 
    /\ receiveInboundMsg = noMsg
    /\ ~IsEmpty(peerToReceive[peerTurn])
    /\ receiveInboundMsg' = HeadMessage(peerToReceive[peerTurn])
    /\ peerToReceive' = [peerToReceive EXCEPT ![peerTurn] = Tail(peerToReceive[peerTurn])]
    /\ peerTurn' \in PeerIDs
    /\ UNCHANGED buffers
    /\ UNCHANGED <<nodeToPeer>> 
    /\ UNCHANGED <<demuxInboundMsg, processInboundMsg, scheduleInboundMsg, peerInboundMsg>>      
    
\* Handle nodeToPeer[peerTurn]: assign the head of nodeToPeer[peerTurn] to      
\* peerInboundMsg[peerTurn] and non-deterministically assign peerTurn
HandleNodeToPeer ==
    /\ AssignInboundPeerMsg(peerInboundMsg, nodeToPeer, peerTurn)
    /\ peerTurn' \in PeerIDs
    /\ UNCHANGED buffers
    /\ UNCHANGED peerToReceive
    /\ UNCHANGED <<receiveInboundMsg, demuxInboundMsg, scheduleInboundMsg, processInboundMsg>>
 
(***************************************************************************
 Handle actions for inbound messages
 ***************************************************************************)
 
\* Handle processInboundMsg: based on the value of processInboundMsg, send appropriate 
\* messages to processToDemux     
\* -- processor.go (handle(), lines 102-164)    
HandleProcessMsg ==
    /\ processInboundMsg /= noMsg
    /\ \/ /\ processInboundMsg \in {"scBlockReceived", "scFinishedEv", "scPeerError"} 
          /\ UNCHANGED processToDemux
       \/ /\ processInboundMsg = "rProcessBlock"
          /\ ~IsFullBounded(processToDemux)
          /\ processToDemux' \in BufferSend(processToDemux, {noMsg, "pcBlockProcessed", "pcBlockVerificationFailure"})
    /\ processInboundMsg' = noMsg
    /\ UNCHANGED <<receiveToDemux, demuxToSchedule, scheduleToDemux, demuxToProcess>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<receiveInboundMsg, demuxInboundMsg, scheduleInboundMsg, peerInboundMsg>>         


\* Handle scheduleInboundMsg: based on the value of scheduleInboundMsg, send appropriate 
\* messages to scheduleToDemux      
\* -- scheduler.go (handle(), lines 663-695)
HandleScheduleMsg ==
    /\ scheduleInboundMsg /= noMsg
    /\ ~IsFullBounded(scheduleToDemux)
    /\ \/ /\ scheduleInboundMsg = "bcAddNewPeer"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scSchedulerFail"})
       
       \/ /\ scheduleInboundMsg = "bcBlockResponse"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scBlockReceived", "scPeerError"})
       
       \/ /\ scheduleInboundMsg = "bcNoBlockResponse"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scPeerError"})
       
       \/ /\ scheduleInboundMsg = "bcRemovePeer"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scSchedulerFail", "scPeerError"})
       
       \/ /\ scheduleInboundMsg = "bcStatusResponse"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scPeerError"})
       
       \/ /\ scheduleInboundMsg = "pcBlockProcessed"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scSchedulerFail", "scFinishedEv"})
       
       \/ /\ scheduleInboundMsg = "pcBlockVerificationFailure"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scFinishedEv"})
    /\ scheduleInboundMsg' = noMsg
    /\ UNCHANGED <<receiveToDemux, demuxToProcess, processToDemux, demuxToSchedule>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<receiveInboundMsg, demuxInboundMsg, processInboundMsg, peerInboundMsg>>   
    
\* Handle receiveInboundMsg: send the value of receiveInboundMsg to receiveToDemux
\* -- reactor.go (Receive(), AddPeer(), RemovePeer())        
HandleReceiveMsg ==
    /\ receiveInboundMsg /= noMsg
    /\ ~IsFullBounded(receiveToDemux)
    /\ receiveToDemux' \in BufferSend(receiveToDemux, {receiveInboundMsg})
    /\ receiveInboundMsg' = noMsg
    /\ UNCHANGED <<demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<demuxInboundMsg, processInboundMsg, scheduleInboundMsg, peerInboundMsg>>
  
\* Handle demuxInboundMsg: based on the value of demuxInboundMsg, send messages to
\* appropriate buffers
\* -- reactor.go (demux(), line 332 - 339)    
HandleDemuxMsg ==
    /\ demuxInboundMsg /= noMsg
    /\ \/ \* the message came from receiveToDemux and should be forwarded to demuxToSchedule
          \* which is unbounded, hence we check if it's full with IsFullUnbounded
          /\ demuxInboundMsg \in peerMsgs 
          /\ ~IsFullUnbounded(demuxToSchedule)
          /\ demuxToSchedule' \in BufferSend(demuxToSchedule, {demuxInboundMsg})
          /\ UNCHANGED <<demuxToProcess, nodeToPeer>>
       \/ \* the message came from scheduleToDemux and should be forwarded to demuxToProcess
          \* which is unbounded, hence we check if it's full with IsFullUnbounded
          /\ demuxInboundMsg \in {"scBlockReceived", "scFinishedEv", "scPeerError"} 
          /\ ~IsFullUnbounded(demuxToProcess)
          /\ demuxToProcess' \in BufferSend(demuxToProcess, {demuxInboundMsg})
          /\ UNCHANGED <<demuxToSchedule, nodeToPeer>>
       \/ \* the message came from scheduleToDemux and should be forwarded to nodeToPeer[peerTurn] 
          /\ demuxInboundMsg \in {"scBlockRequest"} 
          /\ ~IsFullBounded(nodeToPeer[peerTurn])
          /\ nodeToPeer' \in PeerBufferSend(nodeToPeer, peerTurn, {demuxInboundMsg})
          /\ peerTurn' \in PeerIDs
          /\ UNCHANGED <<demuxToProcess, demuxToSchedule>>
       \/ \* the message came from processToDemux and should be forwarded to demuxToSchedule
          \* which is unbounded, hence we check if it's full with IsFullUnbounded
          /\ demuxInboundMsg \in processToDemuxMsgs 
          /\ ~IsFullUnbounded(demuxToSchedule)
          /\ demuxToSchedule' \in BufferSend(demuxToSchedule, {demuxInboundMsg})
          /\ UNCHANGED <<demuxToProcess, nodeToPeer>>
       \/ \* the message is "scSchedulerFail" -- it is not forwarded anywhere
          /\ demuxInboundMsg \in {"scSchedulerFail"}
          /\ UNCHANGED <<demuxToProcess, demuxToSchedule, nodeToPeer>>   
    /\ demuxInboundMsg' = noMsg       
    /\ UNCHANGED <<receiveToDemux, processToDemux, scheduleToDemux>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<receiveInboundMsg, processInboundMsg, scheduleInboundMsg, peerInboundMsg>>   
    
\* Handle peerInboundMsg[peerTurn]: based on the value of peerInboundMsg[peerTurn], send 
\* appropriate messages to peerToReceive[peerTurn]    
HandlePeerMsg ==
    /\ peerInboundMsg[peerTurn] /= noMsg
    /\ ~IsFullBounded(peerToReceive[peerTurn])
    /\ \/ /\ peerInboundMsg[peerTurn] = "bcStatusRequest"
          /\ peerToReceive' \in PeerBufferSend(peerToReceive, peerTurn, {"bcStatusResponse"})
       \/ /\ peerInboundMsg[peerTurn] = "scBlockRequest"
          /\ peerToReceive' \in PeerBufferSend(peerToReceive, peerTurn, {"bcBlockResponse"})
    /\ peerInboundMsg' = [peerInboundMsg EXCEPT ![peerTurn] = noMsg]
    /\ peerTurn' \in PeerIDs
    /\ UNCHANGED buffers
    /\ UNCHANGED nodeToPeer
    /\ UNCHANGED <<receiveInboundMsg, demuxInboundMsg, scheduleInboundMsg, processInboundMsg>>
    
(***************************************************************************
 Periodic actions
 ***************************************************************************)    
    
\* Demux routine broadcasts a status request to all peers 
BroadcastStatusRequest == 
    /\ \A peerID \in PeerIDs : ~IsFullBounded(nodeToPeer[peerID])    
    /\ nodeToPeer' = PeerBufferBroadcast(nodeToPeer, "bcStatusRequest")     
    /\ UNCHANGED <<receiveToDemux, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux>>
    /\ UNCHANGED <<peerToReceive, peerTurn>>
    /\ UNCHANGED <<receiveInboundMsg, processInboundMsg, demuxInboundMsg, scheduleInboundMsg, peerInboundMsg>>
 
\* Demux routine sends a "rProcessBlock" message to the process routine  
SendRProcessBlock ==
    /\ ~IsFullUnbounded(demuxToProcess)
    /\ demuxToProcess' \in BufferSend(demuxToProcess, {"rProcessBlock"}) 
    /\ UNCHANGED <<receiveToDemux, processToDemux, demuxToSchedule, scheduleToDemux>>
    /\ UNCHANGED peer
    /\ UNCHANGED <<receiveInboundMsg, demuxInboundMsg, scheduleInboundMsg, processInboundMsg, peerInboundMsg>>

\* Simulate faulty peers by non-deterministically sending unsolicited peer messages 
SendUnsolicitedPeerMsgs ==
    /\ peerInboundMsg[peerTurn] = noMsg
    /\ ~IsFullBounded(peerToReceive[peerTurn])
    /\ peerToReceive' \in PeerBufferSend(peerToReceive, peerTurn, peerMsgs)
    /\ peerTurn' \in PeerIDs
    /\ UNCHANGED buffers
    /\ UNCHANGED nodeToPeer
    /\ UNCHANGED <<receiveInboundMsg, demuxInboundMsg, scheduleInboundMsg, processInboundMsg, peerInboundMsg>>

\* Capture a timeout on the nodeToPeer buffer when it is full, i.e., drop the oldest message 
NodeToPeerTimeout ==
    /\ IsFullBounded(nodeToPeer[peerTurn])
    /\ nodeToPeer' = [nodeToPeer EXCEPT ![peerTurn] = Tail(nodeToPeer[peerTurn])]
    /\ peerTurn' \in PeerIDs  
    /\ UNCHANGED buffers
    /\ UNCHANGED <<peerInboundMsg, peerToReceive>>
    /\ UNCHANGED inboundMsgs 
    

(***************************************************************************
 Routine actions
 ***************************************************************************)
\* Receive routine action
ReceiveRoutine ==
    \* handle the incoming message from the peer
    \/ HandlePeerToReceive
    \* handle the inbound message
    \/ HandleReceiveMsg
    
\* Demux routine action  
DemuxRoutine ==
    \* handle the buffers receiveToDemux, processToDemux or scheduleToDemux
    \/ HandleReceiveToDemux
    \/ HandleProcessToDemux
    \/ HandleScheduleToDemux
    \* handle the inbound message
    \/ HandleDemuxMsg
    \* broadcast "bcStatusRequest"
    \/ BroadcastStatusRequest 
    \* send "rProcessBlock"
    \/ SendRProcessBlock

\* Process routine action
ProcessRoutine ==
    \* handle the buffer demuxToProcess
    \/ HandleDemuxToProcess
    \* handle the inbound message
    \/ HandleProcessMsg

\* Schedule routine action
ScheduleRoutine ==
    \* handle the buffer demuxToSchedule
    \/ HandleDemuxToSchedule
    \* handle the inbound message
    \/ HandleScheduleMsg

\* Peer action
Peer ==
    \* handle the peer buffers
    \/ HandleNodeToPeer
    \* handle the inbound message
    \/ HandlePeerMsg
    \* capture a timeout on the peer buffer of peerTurn 
    \/ NodeToPeerTimeout
    \* simulate faulty peers
    \* (this introduces a lot of non-determinism and slows TLC down)
    \* \/ SendUnsolicitedPeerMsgs
    
(***************************************************************************
 Specification
 ***************************************************************************)

\* Initial value of each buffer
initBuffer == EmptySeq

\* Initial state predicate
Init ==
    /\ turn \in Turns  
    /\ receiveToDemux = initBuffer 
    /\ demuxToProcess = initBuffer
    /\ processToDemux = initBuffer
    /\ demuxToSchedule = initBuffer
    /\ scheduleToDemux = initBuffer
    /\ nodeToPeer = [peerID \in PeerIDs |-> initBuffer]
    /\ peerToReceive = [peerID \in PeerIDs |-> initBuffer]
    /\ peerTurn \in PeerIDs
    /\ demuxInboundMsg = noMsg
    /\ processInboundMsg = noMsg
    /\ scheduleInboundMsg = noMsg
    /\ receiveInboundMsg = noMsg
    /\ peerInboundMsg = [peerID \in PeerIDs |-> noMsg]

\* TakeTurns action
\* The routines and peers take turns in the system
TakeTurns ==
    /\ \/ /\ turn = "receiveRoutine"
          /\ ReceiveRoutine
       \/ /\ turn = "demuxRoutine"
          /\ DemuxRoutine
       \/ /\ turn = "processRoutine"
          /\ ProcessRoutine
       \/ /\ turn = "scheduleRoutine"
          /\ ScheduleRoutine
       \/ /\ turn = "peer"
          /\ Peer
    /\ turn' \in Turns

\* Next action
Next ==
    \/ TakeTurns
    \/ UNCHANGED vars

\* Fairness constraint
Fairness == 
    /\ WF_vars(Next)
    \* prevent the peer from always taking the timeout action 
    /\ WF_vars(HandleNodeToPeer)
    /\ WF_vars(HandlePeerMsg)

\* Spec formula
Spec == Init /\ [][Next]_vars /\ Fairness
 
(***************************************************************************
 Invariants
 ***************************************************************************)

\* Type invariant
TypeOK ==
    /\ turn \in Turns
    /\ receiveToDemux \in Seq(peerMsgs)
    /\ demuxToProcess \in Seq(demuxToProcessMsgs)
    /\ processToDemux \in Seq(processToDemuxMsgs)
    /\ demuxToSchedule \in Seq(demuxToScheduleMsgs)
    /\ scheduleToDemux \in Seq(scheduleToDemuxMsgs)
    /\ nodeToPeer \in [PeerIDs -> Seq(ioMsgs)]
    /\ peerToReceive \in [PeerIDs -> Seq(peerMsgs)]
    /\ peerTurn \in PeerIDs
    /\ receiveInboundMsg \in peerMsgs \union {noMsg}
    /\ demuxInboundMsg \in peerMsgs \union processToDemuxMsgs \union scheduleToDemuxMsgs \union {noMsg}
    /\ processInboundMsg \in demuxToProcessMsgs \union {noMsg}
    /\ scheduleInboundMsg \in demuxToScheduleMsgs \union {noMsg}
    /\ \A peerID \in PeerIDs : peerInboundMsg[peerID] \in ioMsgs \union {noMsg}

\* A good state of the demux routine
GoodStateDemux ==
    \* message from incoming buffers can be processed
    \/ IsFullBounded(receiveToDemux) /\ IsFullBounded(processToDemux) /\ IsFullBounded(scheduleToDemux) => demuxInboundMsg = noMsg
    \* inbound message can be forwarded to process routine
    \/ demuxInboundMsg \in demuxToProcessMsgs
    \* inbound message can be forwarded to schedule routine
    \/ demuxInboundMsg \in demuxToScheduleMsgs 
    \* inbound message can be forwarded to peer or the message is "scSchedulerFail" which is not forwarded
    \/ demuxInboundMsg \in {"scBlockRequest", " scSchedulerFail"}
    \* "bcStatusRequest" to peer can be broadcast to all peers
    \/ \A peerID \in PeerIDs : ~IsFullBounded(nodeToPeer[peerID])
    
\* A good state of the receive routine    
GoodStateReceive == 
    \* inbound message can be forwarded to demux routine
    \/ receiveInboundMsg \in peerMsgs => ~IsFullBounded(receiveToDemux)

\* A good state of the process routine
GoodStateProcess == 
    \* inbound message can be forwarded to demux routine
    \/ processInboundMsg \in demuxToProcessMsgs => ~IsFullBounded(processToDemux)      

\* A good state of the schedule routine 
GoodStateSchedule ==
    \* inbound message can be forwarded to demux routine
    \/ scheduleInboundMsg \in demuxToScheduleMsgs => ~IsFullBounded(scheduleToDemux)    

\* A good state of the peer         
GoodStatePeer ==
    \* message from incoming peer buffer can be processed 
    \/ IsFullBounded(nodeToPeer[peerTurn]) => peerInboundMsg[peerTurn] = noMsg 
    \* inbound message can be forwarded to receive routine
    \/ peerInboundMsg[peerTurn] \in ioMsgs      
           
\* A good state of the system           
GoodState ==
    \/ GoodStateDemux
    \/ GoodStateReceive
    \/ GoodStateProcess
    \/ GoodStateSchedule
    \/ GoodStatePeer

\* Inv
\* A conjunction of all invariants     
Inv ==
    /\ TypeOK
    /\ GoodState
        
=============================================================================
\* Modification History
\* Last modified Fri May 29 17:10:47 CEST 2020 by ilinastoilkovska
\* Created Wed Feb 05 15:44:25 CET 2020 by ilina