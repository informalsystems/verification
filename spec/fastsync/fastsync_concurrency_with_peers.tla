------------------ MODULE fastsync_concurrency_with_peers ------------------

\* Reference go code :
\* https://github.com/tendermint/tendermint/blob/brapse/blockchain-v2-riri-reactor/blockchain/v2
\* all buffers are bounded and blocking
\* the threads are modeled by interleaving

EXTENDS Naturals, FiniteSets, Sequences

MT == STRING
a <: b == a
EmptySeq == <<>> <: Seq(MT)

CONSTANTS QueueMaxSize, NrPeers

VARIABLES turn, \* which routine is taking a step
          receiveToDemux, \* the buffer from the receive routine to the demux routine
          demuxToSend, \* the buffer from the demux routine to the send routine
          demuxToProcess, \* the buffer from the demux routine to the process routine
          processToDemux, \* the buffer from the process routine to the demux routine
          demuxToSchedule, \* the buffer from the demux routine to the schedule routine
          scheduleToDemux, \* the buffer from the scheudle routine to the demux routine
          nodeToPeer, \* the buffers incoming to the peers
          peerToReceive, \* the buffers outgoing from the peers
          peerTurn \* the current peer that receives a block request and sends a block response

\* set of peers
PeerIDs == 1..NrPeers

vars == <<turn, receiveToDemux, demuxToSend, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux, nodeToPeer, peerToReceive, peerTurn>>          
buffers == <<receiveToDemux, demuxToSend, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux>>
peer == <<nodeToPeer, peerToReceive, peerTurn>>

\* set of messages that the peers send to the receive routine
peerMsgs == {"bcAddNewPeer", "bcBlockResponse", "bcNoBlockResponse", "bcRemovePeer", "bcStatusResponse"} 

\* set of messages that the process routine sends to the demux routine (forwarded to the schedule routine)
processToDemuxMsgs == {"pcBlockProcessed", "pcBlockVerificationFailure"} 

\* set of messages that the schedule routine sends to the demux routine (forwarded to the process routine)
scheduleToDemuxMsgs == {"scBlockReceived", "scFinishedEv", "scPeerError", "scSchedulerFail"} 

\* set of messages that the demux routine sends to the send routine (blockRequest) 
demuxToSendMsgs == {"scBlockRequest"}  

\* set of messages that the demux routine broadcasts to all peers (statusRequest)
demuxPeerMsgs == {"bcStatusRequest"}

ioMsgs == demuxToSendMsgs \union demuxPeerMsgs

\* set of messages that the demux routine sends to the process routine  
demuxToProcessMsgs == {"rProcessBlock", "scBlockReceived", "scFinishedEv", "scPeerError"}

\* set of messages that the demux routine sends to the schedule routine 
demuxToScheduleMsgs == peerMsgs \union processToDemuxMsgs 

\* special message denoting no message
noMsg == "noMsg"

\* set of all messages
Msgs == peerMsgs \union demuxToSendMsgs \union demuxToProcessMsgs \union processToDemuxMsgs \union demuxToScheduleMsgs \union scheduleToDemuxMsgs \union demuxPeerMsgs \union {noMsg}
 
\* set of turns used to schedule the different routines
Turns == {"receiveRoutine", "demuxRoutine", "sendRoutine", "processRoutine", "scheduleRoutine", "peer"} 

(*  
A buffer is a record: 
   buffer \in [inMsg : Msgs, queue : Seq(Msgs)]
where
    - inMsg is the incoming message that should be added to the queue
    - queue is a sequence of messages 
Initially, inMsg is noMsg, and queue is empty. 
A routine sends a message to a buffer by assigning a value to inMsg.
A buffer internally adds inMsg to the queue if there is space, and sets inMsg to noMsg.
A buffer is blocking if queue is full and inMsg is not equal to inMsg. 

To model peer buffers, we use functions of buffers: 
    peerBuffer \in [PeerIDs : [inMsg : Msgs, queue : Seq(Msgs)]]

That is, to each peerID \in PeerIDs we assign a buffer:
    peerBuffer[peerID] \in [inMsg : Msgs, queue : Seq(Msgs)]
*) 

(*** Useful buffer predicates/operators. ***)

(*
IsFull(buffer) -- A buffer prediate checking if a buffer is full.
A buffer is full if the length of its queue is greater or equal to QueueMaxSize
*)
IsFull(buffer) ==
    Len(buffer.queue) >= QueueMaxSize
  
(*
IsEmpty(buffer) -- A buffer prediate checking if a buffer is empty.
A buffer is empty if its queue is the empty sequence
*)
IsEmpty(buffer) ==
    buffer.queue = EmptySeq

(*
IsReady(buffer) -- A buffer prediate checking if a buffer is ready.
A buffer is ready to receive a message if the value for its inMsg field is equal to noMsg
*)   
IsReady(buffer) ==
    buffer.inMsg = noMsg

(* 
HeadMessage(buffer) -- A buffer operator that gets the message  
Get the value of the message at the head of the buffer's queue, without removing it from the queue
*)
HeadMessage(buffer) ==
    Head(buffer.queue) 

(*
BufferSend(buffer, msgs) -- A buffer operator that computes the set of possible next values of a buffer
    - buffer - the buffer of interest
    - msgs - a set of messages that are non-deterministically sent to the buffer

The resulting set of possible next values for the buffer contains:
    - for each message msg \in msgs, the buffer: 
        [buffer EXCEPT !.inMsg = msg]
      where the value of inMsg is set to msg
*)
BufferSend(buffer, msgs) ==
    {[buffer EXCEPT !.inMsg = msg] : msg \in msgs}

(*
PeerBufferSend(peerBuffer, peerID, msgs) -- A peer buffer operator that computes the set of possible next values of a peer buffer
    - peerBuffer - the peer buffer of interest
    - peerID - the peerID to which messages from msgs are sent
    - msgs - a set of messages that are non-deterministically sent to the buffer
    
The resulting set of possible next values for the peer buffer contains:
    - for each message msg \in msgs, the peer buffer: 
        [peerBuffer EXCEPT ![peerID].inMsg = msg]
      where the value of peerBuffer[peerID].inMsg is set to msg    
*)
PeerBufferSend(peerBuffer, peerID, msgs) ==
    {[peerBuffer EXCEPT ![peerID].inMsg = msg] : msg \in msgs}

\* compute the outcome of a broadcast to all peers: set the inMsg of the buffer for every peer to some msg \in msgs  
(*
PeerBufferBroadcast(peerBuffer, msg) -- A peer buffer operator that computes the result of the given peer buffer after a broadcast to all peers
    - peerBuffer - the peer buffer of interest
    - msg - the message that is broadcast
    
The resulting peer buffer is a function where each peerID \in PeerIDs is assigned the buffer 
    [peerBuffer[peerID] EXCEPT !.inMsg = msg]      
*)
PeerBufferBroadcast(peerBuffer, msg) ==
    [peerID \in PeerIDs |-> [peerBuffer[peerID] EXCEPT !.inMsg = msg]]
    

\* initial value of each buffer: the queue is IsEmpty, the inMsg is noMsg
initBuffer ==
    [inMsg |-> noMsg, queue |-> EmptySeq]

\* type invariant
TypeOK ==
    /\ turn \in Turns
    /\ receiveToDemux \in [inMsg : peerMsgs \union {noMsg}, queue : Seq(peerMsgs)]
    /\ demuxToSend \in [inMsg : demuxToSendMsgs \union {noMsg}, queue : Seq(demuxToSendMsgs)]
    /\ demuxToProcess \in [inMsg : demuxToProcessMsgs \union {noMsg}, queue : Seq(demuxToProcessMsgs)]
    /\ processToDemux \in [inMsg : processToDemuxMsgs \union {noMsg}, queue : Seq(processToDemuxMsgs)]
    /\ demuxToSchedule \in [inMsg : demuxToScheduleMsgs \union {noMsg}, queue : Seq(demuxToScheduleMsgs)]
    /\ scheduleToDemux \in [inMsg : scheduleToDemuxMsgs \union {noMsg}, queue : Seq(scheduleToDemuxMsgs)]
    /\ nodeToPeer \in [PeerIDs -> [inMsg : ioMsgs \union {noMsg}, queue : Seq(ioMsgs)]]
    /\ peerToReceive \in [PeerIDs -> [inMsg : peerMsgs \union {noMsg}, queue : Seq(peerMsgs)]]
    /\ peerTurn \in PeerIDs

\* initial state predicate
Init ==
    /\ turn \in Turns \* starting in any routine 
    /\ receiveToDemux = initBuffer 
    /\ demuxToSend = initBuffer
    /\ demuxToProcess = initBuffer
    /\ processToDemux = initBuffer
    /\ demuxToSchedule = initBuffer
    /\ scheduleToDemux = initBuffer
    /\ nodeToPeer = [peerID \in PeerIDs |-> initBuffer]
    /\ peerToReceive = [peerID \in PeerIDs |-> initBuffer]
    /\ peerTurn \in PeerIDs

(* 
Handle Actions: 
    a routine gets a message from the head of an incoming buffer, 
    and forwards it to the appropriate outgoing buffer, based on the content of the incoming message

Example: 
    The process routine checks the message at the head of the demuxToProcess buffer, 
    and sends an appropriate message back to the demux routine on the processToDemux buffer 
*)

(*
HandleDemuxToProcess -- processor.go (handle(), lines 102-164)
Process routine handle for the message sent from the demux routine on the demuxToProcess buffer
    - enabled if:
        * demuxToProcess is not empty
        * processToDemux is ready
    - check the message at the head of demuxToProcess:
        * if it is "scBlockReceived", "scFinishedEv", or "scPeerError", 
          then do not send anything back to the demux routine
        * if it is "rProcessBlock", then either do not send anything, 
          or send "pcBlockProcessed" or "pcBlockVerificationFailure"
    - remove the message from the demuxToProcess buffer

Remark: when the message at the head of demuxToProcess is "rProcessBlock", the Go code checks additional 
conditions. Here, we abstract away these checks, and non-deterministically send 
the messages that can be generated by the process routine.     
*)
HandleDemuxToProcess ==
    /\ ~IsEmpty(demuxToProcess)
    /\ IsReady(processToDemux)
    
    /\ \/ /\ HeadMessage(demuxToProcess) \in {"scBlockReceived", "scFinishedEv", "scPeerError"} 
          /\ UNCHANGED processToDemux
       \/ /\ HeadMessage(demuxToProcess) = "rProcessBlock"
          /\ processToDemux' \in BufferSend(processToDemux, {noMsg, "pcBlockProcessed", "pcBlockVerificationFailure"})   
    
    /\ demuxToProcess' = [demuxToProcess EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToSchedule, scheduleToDemux>>
    /\ UNCHANGED peer
    

(*
HandleDemuxToSchedule -- scheduler.go (handle(), lines 663-695)
Schedule routine handle for the message sent from the demux routine on the demuxToSchedule buffer
    - enabled if:
        * demuxToSchedule is not IsEmpty
        * scheduleToDemux is IsReady
    - check the message at the head of demuxToSchedule:
        * if it is "bcAddNewPeer",      (handleAddNewPeer(), lines 579-585)
          then either do not send anything to the demux routine or send a "scSchedulerFail"
        * if it is "bcBlockResponse"        (handleBlockReponse(), lines 510-522)
          then send "scBlockReceived" or "scPeerError" to the demux routine
        * if it is "bcNoBlockResponse",      (handleNoBlockReponse(), lines 524-539)
          then either do not send anything to the demux routine or send a "scPeerError"
        * if it is "bcRemovePeer",      (handleRemovePeer(), lines 587-598)
          then either do not send anything to the demux routine or send a "scSchedulerFail" or a "scPeerError"
        * if it is "bcStatusResponse",      (handleStatusResponse(), lines 655-661)
          then either do not send anything to the demux routine or send a "scPeerError"
        * if it is "pcBlockProcessed",      (handleBlockProcessed(), lines 541-558)
          then either do not send anything to the demux routine or send a "scSchedulerFail" or a "scFinishedEv"
        * if it is "pcBlockVerificationFailure",        (handleBlockProcessError(), lines 562-577)      
          then either do not send anything to the demux routine or send a "scFinishedEv"
          
    - remove the message from the demuxToSchedule buffer
*)
HandleDemuxToSchedule ==
    /\ ~IsEmpty(demuxToSchedule)
    /\ IsReady(scheduleToDemux)

    /\ \/ /\ HeadMessage(demuxToSchedule) = "bcAddNewPeer"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scSchedulerFail"}) 
       
       \/ /\ HeadMessage(demuxToSchedule) = "bcBlockResponse"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scBlockReceived", "scPeerError"})  
       
       \/ /\ HeadMessage(demuxToSchedule) = "bcNoBlockResponse"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scPeerError"}) 
       
       \/ /\ HeadMessage(demuxToSchedule) = "bcRemovePeer"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scSchedulerFail", "scPeerError"})
       
       \/ /\ HeadMessage(demuxToSchedule) = "bcStatusResponse"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scPeerError"})  
       
       \/ /\ HeadMessage(demuxToSchedule) = "pcBlockProcessed"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scSchedulerFail", "scFinishedEv"}) 
       
       \/ /\ HeadMessage(demuxToSchedule) = "pcBlockVerificationFailure"
          /\ scheduleToDemux' \in BufferSend(scheduleToDemux, {noMsg, "scFinishedEv"})

    /\ demuxToSchedule' = [demuxToSchedule EXCEPT !.queue = Tail(@)] 
    /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToProcess, processToDemux>>
    /\ UNCHANGED peer
    
(* 
HandlePeerReceive -- reactor.go (Receive(), AddPeer(), RemovePeer()) 
Receive routine handle for the peer message received from the current peer
   - enabled if:
        * the buffer of the current peer is not IsEmpty
        * the receiveToDemux buffer is IsReady
   - add the message to the receiveToDemux buffer
   - remove the message from the buffer of the current peer
   - pick a new current peer. This peer will be sent the next block request message
     by the send routine 
*)    
HandlePeerReceive == 
    /\ ~IsEmpty(peerToReceive[peerTurn])  
    /\ IsReady(receiveToDemux)
    
    /\ receiveToDemux' \in BufferSend(receiveToDemux, {HeadMessage(peerToReceive[peerTurn])})
    /\ peerToReceive' = [peerToReceive EXCEPT ![peerTurn].queue = Tail(peerToReceive[peerTurn].queue)]
    /\ peerTurn' \in PeerIDs
    /\ UNCHANGED <<demuxToSend, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux>>
    /\ UNCHANGED <<nodeToPeer>>    
    
  
(*
HandleReceiveToDemux -- reactor.go (demux(), line 332 - 339)
Demux routine handle for the message at the head of the receiveToDemux buffer
    - enabled if 
        * receiveToDemux is not IsEmpty 
        * demuxToSchedule is IsReady
    - add the message to the demuxToSchedule buffer
    - remove the message from the receiveToDemux buffer
*)    
HandleReceiveToDemux == 
    /\ ~IsEmpty(receiveToDemux)
    /\ IsReady(demuxToSchedule)
    
    /\ demuxToSchedule' \in BufferSend(demuxToSchedule, {HeadMessage(receiveToDemux)})
    /\ receiveToDemux' = [receiveToDemux EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<demuxToSend, demuxToProcess, processToDemux, scheduleToDemux>>
    /\ UNCHANGED peer 

(*
HandleProcessToDemux -- reactor.go (demux(), line 357 - 373)
Demux routine handle for the message at the head of the processToDemux buffer
    - enabled if:
        * processToDemux is not IsEmpty
        * demuxToSchedule is IsReady
    - add the message to the demuxToSchedule buffer
    - remove the message from the processToDemux buffer 
*)
HandleProcessToDemux ==
    /\ ~IsEmpty(processToDemux)
    /\ IsReady(demuxToSchedule)
    
    /\ demuxToSchedule' \in BufferSend(demuxToSchedule, {HeadMessage(processToDemux)})
    /\ processToDemux' = [processToDemux EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToProcess, scheduleToDemux>>
    /\ UNCHANGED peer

(*
HandleScheduleToDemux -- reactor.go (demux(), line 342 - 354)
Demux routine handle for the message at the head of the scheduleToDemux buffer
    - enabled if:
        * scheduleToDemux is not IsEmpty
        * either the message at the head of scheduleToDemux is "scBlockReceived", "scFinishedEv" or "scPeerError"
          and processToDemux is IsReady
        * or the message at the head of scheduleToDemux is "scBlockRequest" and demuxToSend is IsReady      
    - add the message to the appropriate buffer
    - remove the message from the scheduleToDemux buffer 
*)
HandleScheduleToDemux ==
    /\ ~IsEmpty(scheduleToDemux)
    
    /\ \/ /\ IsReady(demuxToProcess)
          /\ HeadMessage(scheduleToDemux) \in {"scBlockReceived", "scFinishedEv", "scPeerError"}
          /\ demuxToProcess' \in BufferSend(demuxToProcess, {HeadMessage(scheduleToDemux)})
          /\ UNCHANGED demuxToSend
            
       \/ /\ IsReady(demuxToSend)
          /\ HeadMessage(scheduleToDemux) = "scBlockRequest"
          /\ demuxToSend' \in BufferSend(demuxToSend, {HeadMessage(scheduleToDemux)})
          /\ UNCHANGED demuxToProcess 
          
    /\ scheduleToDemux' = [scheduleToDemux EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<receiveToDemux, processToDemux, demuxToSchedule>>
    /\ UNCHANGED peer

(*
HandleDemuxToSend -- ?.go (?, lines ?-?)
Send routine handle for the message at the head of the demuxToSend buffer
    - enabled if:
        * demuxToSend is not IsEmpty
        * the buffer of the current peer is IsReady
    - add the message to the buffer of the current peer
    - remove the message from the demuxToSend buffer 
*)    
HandleDemuxToSend ==
    /\ ~IsEmpty(demuxToSend)
    /\ IsReady(nodeToPeer[peerTurn])
    
    /\ nodeToPeer' \in PeerBufferSend(nodeToPeer, peerTurn, {HeadMessage(demuxToSend)})
    /\ peerTurn' \in PeerIDs
    /\ demuxToSend' \in [demuxToSend EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<receiveToDemux, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux>>
    /\ UNCHANGED peerToReceive

(*
BroadcastStatusRequest -- ?.go (?, lines ?-?)
Demux routine action for broadcasting a status request message 
    - enabled if:
        * the buffers of all peers are IsReady
    - add the "bcStatusRequest" message to the buffers of all peers
*)    
BroadcastStatusRequest == 
    /\ \A peerID \in PeerIDs : IsReady(nodeToPeer[peerID])
    
    /\ nodeToPeer' = PeerBufferBroadcast(nodeToPeer, "bcStatusRequest")     
    /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux>>
    /\ UNCHANGED <<peerToReceive, peerTurn>>

(*
SendRProcessBlock -- ?.go (?, lines ?-?)
Demux routine action for sending a "rProcessBlock" message to the process routine
    - enabled if:
        * demuxToProcess is IsReady
    - add the "rProcessBlock" message to the demuxToProcess buffer
*)        
SendRProcessBlock ==
    /\ IsReady(demuxToProcess)
    
    /\ demuxToProcess' \in BufferSend(demuxToProcess, {"rProcessBlock"}) 
    /\ UNCHANGED <<receiveToDemux, demuxToSend, processToDemux, demuxToSchedule, scheduleToDemux>>
    /\ UNCHANGED peer

(*
SendPeerMsgs -- ?.go (?, lines ?-?)
Peer action for non-deterministically sending messages to the receive routine
    - enabled if:
        * the incoming buffer of the current peer is not IsEmpty  
        * the outgoing buffer of the current peer is IsReady
    - if the message at the head of the incoming buffer is status/block request, send a status/block response
    - otherwise, add one of the peer messages "bcAddNewPeer", "bcNoBlockResponse", "bcRemovePeer", "bcStatusResponse"
      to the buffer of the current peer
*)
SendPeerMsgs ==
    /\ ~IsEmpty(nodeToPeer[peerTurn])
    /\ IsReady(peerToReceive[peerTurn])
    /\ \/ /\ HeadMessage(nodeToPeer[peerTurn]) = "bcStatusRequest"
          /\ peerToReceive' \in PeerBufferSend(peerToReceive, peerTurn, {"bcStatusResponse"})
       \/ /\ HeadMessage(nodeToPeer[peerTurn]) = "scBlockRequest"
          /\ peerToReceive' \in PeerBufferSend(peerToReceive, peerTurn, {"bcBlockResponse"})
       \/ /\ peerToReceive' \in PeerBufferSend(peerToReceive, peerTurn, peerMsgs)
    /\ nodeToPeer' = [nodeToPeer EXCEPT ![peerTurn].queue = Tail(nodeToPeer[peerTurn].queue)]  
    /\ peerTurn' \in PeerIDs
    /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux>>

(* 
ReceiveRoutine --
    either handle the message sent by the current peer,
    or do nothing 
*)
ReceiveRoutine ==
    \* handle the incoming message from the peer
    \/ HandlePeerReceive
    \* do nothing
    \/ /\ UNCHANGED buffers
       /\ UNCHANGED peer
    
(*
DemuxRoutine --
    either handle the incoming messages on the receiveToDemux, processToDemux, or scheduleToDemux buffers,
    or broadcast a status request to all peers,
    or send a "rProcessBlock" to the process routine,
    or do nothing
*)    
DemuxRoutine ==
    \* handle the incoming messages on either receiveToDemux, processToDemux or scheduleToDemux
    \/ HandleReceiveToDemux
    \/ HandleProcessToDemux
    \/ HandleScheduleToDemux
       
    \* broadcast a status request
    \/ BroadcastStatusRequest 
       
    \* send a "rProcessBlock" to the process routine
    \/ SendRProcessBlock
       
    \* otherwise, do nothing       
    \/ /\ UNCHANGED buffers
       /\ UNCHANGED peer

(* 
ProcessRoutine --
    either handle the message sent by the demux routine on the demuxToProcess buffer,
    or do nothing 
*)
ProcessRoutine ==
    \* handle the incoming messages on demuxToProcess
    \/ HandleDemuxToProcess
    \* do nothing
    \/ /\ UNCHANGED buffers
       /\ UNCHANGED peer

(* 
ScheduleRoutine --
    either handle the message sent by the demux routine on the demuxToSchedule buffer,
    or do nothing 
*)
ScheduleRoutine ==
    \* handle the incoming message on demuxToSchedule
    \/ HandleDemuxToSchedule
    \* do nothing
    \/ /\ UNCHANGED buffers
       /\ UNCHANGED peer

(* 
SendRoutine --
    either handle the message sent by the demux routine on the demuxToSend buffer,
    or do nothing 
*)
SendRoutine ==
    \* handle the incoming message on demuxToSend
    \/ HandleDemuxToSend
    \* do nothing
    \/ /\ UNCHANGED buffers
       /\ UNCHANGED peer
      
(*
Peer --
    either non-deterministically send peer messages to the receive routine
    or do noting
*)       
Peer ==
    \* send peer messages
    \/ SendPeerMsgs
    \* do nothing 
    \/ /\ UNCHANGED buffers
       /\ UNCHANGED peer

(* 
Internal action of the buffer. 
Enabled if 
    * the buffer's inMsg is not noMsg 
    *  its queue is not full
The inMsg is added to the buffer queue and its value is reset to noMsg  
*)
InternalBuffer(buffer) ==
    /\ buffer.inMsg /= noMsg
    /\ ~IsFull(buffer)
    /\ buffer' = [buffer EXCEPT !.queue = Append(buffer.queue, buffer.inMsg), 
                                !.inMsg = noMsg]
    
(* 
Internal action of some peer buffer. 
Enabled if 
    * the buffer's inMsg is not noMsg 
    *  its queue is not full
The inMsg is added to the buffer queue and its value is reset to noMsg  
*)    
InternalPeerBuffer(buffer) ==
    \E peerID \in PeerIDs : 
        /\ buffer[peerID].inMsg /= noMsg
        /\ ~IsFull(buffer[peerID])
        /\ buffer' = [buffer EXCEPT ![peerID].queue = Append(buffer[peerID].queue, buffer[peerID].inMsg), 
                                    ![peerID].inMsg = noMsg]

(*
Internal buffer receive action.
Enabled if:
    * the internal action of some buffer is enabled.
*)
InternalBufferReceive ==
    \/ /\ InternalBuffer(receiveToDemux) 
       /\ UNCHANGED <<demuxToSend, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux, nodeToPeer, peerToReceive, peerTurn>>
    \/ /\ InternalBuffer(demuxToSend)
       /\ UNCHANGED <<receiveToDemux, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux, nodeToPeer, peerToReceive, peerTurn>>
    \/ /\ InternalBuffer(demuxToProcess)
       /\ UNCHANGED <<receiveToDemux, demuxToSend, processToDemux, demuxToSchedule, scheduleToDemux, nodeToPeer, peerToReceive, peerTurn>>
    \/ /\ InternalBuffer(processToDemux)
       /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToProcess, demuxToSchedule, scheduleToDemux, nodeToPeer, peerToReceive, peerTurn>>
    \/ /\ InternalBuffer(demuxToSchedule)
       /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToProcess, processToDemux, scheduleToDemux, nodeToPeer, peerToReceive, peerTurn>>
    \/ /\ InternalBuffer(scheduleToDemux)
       /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToProcess, processToDemux, demuxToSchedule, nodeToPeer, peerToReceive, peerTurn>>   
    \/ /\ InternalPeerBuffer(nodeToPeer)
       /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux, peerToReceive, peerTurn>>
    \/ /\ InternalPeerBuffer(peerToReceive)
       /\ UNCHANGED <<receiveToDemux, demuxToSend, demuxToProcess, processToDemux, demuxToSchedule, scheduleToDemux, nodeToPeer, peerTurn>>       
    
       
     
Next ==
    /\ \/ /\ turn = "receiveRoutine"
          /\ ReceiveRoutine
       \/ /\ turn = "demuxRoutine"
          /\ DemuxRoutine
       \/ /\ turn = "processRoutine"
          /\ ProcessRoutine
       \/ /\ turn = "scheduleRoutine"
          /\ ScheduleRoutine
       \/ /\ turn = "sendRoutine"
          /\ SendRoutine
       \/ /\ turn = "peer"
          /\ Peer
       \/ InternalBufferReceive
    /\ turn' \in Turns  

Fairness == 
    /\ WF_vars(InternalBufferReceive)

Spec == Init /\ [][Next]_vars /\ Fairness
  

GoodState ==
    \/ ~IsEmpty(receiveToDemux) => IsReady(demuxToSchedule)
    \/ ~IsEmpty(processToDemux) => IsReady(demuxToSchedule)
    \/ /\ ~IsEmpty(scheduleToDemux) 
       /\ HeadMessage(scheduleToDemux) \in {"scBlockReceived", "scFinishedEv", "scPeerError"}  
                 => IsReady(demuxToProcess)
    \/ /\ ~IsEmpty(scheduleToDemux) 
       /\ HeadMessage(scheduleToDemux) = "scBlockRequest"   
                 => IsReady(demuxToSend)                          
    \/ IsReady(demuxToProcess)
    \/ \A peerID \in PeerIDs: IsReady(nodeToPeer[peerID])
    
    \/ ~IsEmpty(demuxToProcess) => IsReady(processToDemux)    
    
    \/ ~IsEmpty(demuxToSchedule) => IsReady(scheduleToDemux)
    
    \/ ~IsEmpty(demuxToSend) => IsReady(nodeToPeer[peerTurn])
    
    \/ \A peerID \in PeerIDs: ~IsEmpty(nodeToPeer[peerID]) => IsReady(peerToReceive[peerID])
    
    \/ ~IsEmpty(peerToReceive[peerTurn]) => IsReady(receiveToDemux)
    
Invariant ==
    /\ TypeOK
    /\ GoodState
        
=============================================================================
\* Modification History
\* Last modified Tue Feb 25 16:59:00 CET 2020 by ilinastoilkovska
\* Created Wed Feb 05 15:44:25 CET 2020 by ilina
