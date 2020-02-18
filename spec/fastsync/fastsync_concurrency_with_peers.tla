------------------ MODULE fastsync_concurrency_with_peers ------------------

\* Reference go code :
\* https://github.com/tendermint/tendermint/blob/brapse/blockchain-v2-riri-reactor/blockchain/v2
\* all buffers are bounded and blocking

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS QueueLength, NrPeers

VARIABLES turn, \* which routine is taking a step
          receiveDemux, \* the buffer from the receive routine to the demux routine
          demuxSend, \* the buffer from the demux routine to the send routine
          demuxProcess, \* the buffer from the demux routine to the process routine
          processDemux, \* the buffer from the process routine to the demux routine
          demuxSchedule, \* the buffer from the demux routine to the schedule routine
          scheduleDemux, \* the buffer from the scheudle routine to the demux routine
          peerIncoming, \* the buffers incoming to the peers
          peerOutgoing, \* the buffers outgoing from the peers
          peerTurn \* the current peer that receives a block request and sends a block response

\* set of peers
PeerIDs == 1..NrPeers

vars == <<turn, receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux, peerIncoming, peerOutgoing, peerTurn>>          
buffers == <<receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux>>
peer == <<peerIncoming, peerOutgoing, peerTurn>>

\* set of messages that the peers send to the receive routine
peerMsgs == {"bcAddNewPeer", "bcBlockResponse", "bcNoBlockResponse", "bcRemovePeer", "bcStatusResponse"} 

\* set of messages that the process routine sends to the demux routine (forwarded to the schedule routine)
processDemuxMsgs == {"pcBlockProcessed", "pcBlockVerificationFailure"} 

\* set of messages that the schedule routine sends to the demux routine (forwarded to the process routine)
scheduleDemuxMsgs == {"scBlockReceived", "scFinishedEv", "scPeerError", "scSchedulerFail"} 

\* set of messages that the demux routine sends to the send routine (blockRequest) 
demuxSendMsgs == {"scBlockRequest"}  

\* set of messages that the demux routine broadcasts to all peers (statusRequest)
demuxPeerMsgs == {"bcStatusRequest"}

ioMsgs == demuxSendMsgs \cup demuxPeerMsgs

\* set of messages that the demux routine sends to the process routine  
demuxProcessMsgs == {"rProcessBlock", "scBlockReceived", "scFinishedEv", "scPeerError"}

\* set of messages that the demux routine sends to the schedule routine 
demuxScheduleMsgs == peerMsgs \cup processDemuxMsgs 

\* special message denoting no message
noMsg == "noMsg"

\* set of all messages
Msgs == peerMsgs \cup demuxSendMsgs \cup demuxProcessMsgs \cup processDemuxMsgs \cup demuxScheduleMsgs \cup scheduleDemuxMsgs \cup demuxPeerMsgs \cup {noMsg}
 
\* set of turns used to schedule the different routines
Turns == {"receiveRoutine", "demuxRoutine", "sendRoutine", "processRoutine", "scheduleRoutine", "peer"} 

(* Useful buffer predicates/actions. A buffer is a record: 
   buffer \in [inMsg : Msgs, queue : Seq(Msgs)] 
*) 

\* a buffer is full if the length of its queue is greater or equal to QueueLength    
Full(buffer) ==
    Len(buffer.queue) >= QueueLength
    
\* a buffer is empty if its queue is the empty sequence    
Empty(buffer) ==
    buffer.queue = <<>> 

\* a buffer is ready to get a message if its inMsg is noMsg   
Ready(buffer) ==
    buffer.inMsg = noMsg

\* get the message at the head of the buffer queue
GetMessage(buffer) ==
    Head(buffer.queue) 

\* compute the outcome of a routine sending a message to a buffer: set the inMsg of the buffer to some msg \in msgs    
RoutineSend(buffer, msgs) ==
    IF noMsg \in msgs
    THEN {buffer} \cup {[buffer EXCEPT !.inMsg = msg] : msg \in msgs \ {noMsg}}
    ELSE {[buffer EXCEPT !.inMsg = msg] : msg \in msgs}

\* compute the outcome of a peer sending a message to a buffer: set the inMsg of the buffer of peerID to some msg \in msgs    
PeerSend(buffer, peerID, msgs) ==
    IF noMsg \in msgs
    THEN {buffer} \cup {[buffer EXCEPT ![peerID].inMsg = msg] : msg \in msgs \ {noMsg}}
    ELSE {[buffer EXCEPT ![peerID].inMsg = msg] : msg \in msgs}

\* compute the outcome of a broadcast to all peers: set the inMsg of the buffer for every peer to some msg \in msgs  
PeerBroadcast(buffer, msg) ==
    [peerID \in PeerIDs |-> [buffer[peerID] EXCEPT !.inMsg = msg]]
 
\* internal buffer receive: add the inMsg to the queue 
BufRcv(buffer) ==
    [buffer EXCEPT !.queue = Append(buffer.queue, buffer.inMsg), !.inMsg = noMsg]     
    

\* initial value of each buffer: the queue is empty, the inMsg is noMsg
initBuffer ==
    [inMsg |-> noMsg, queue |-> <<>>]

\* type invariant
TypeOK ==
    /\ turn \in Turns
    /\ receiveDemux \in [inMsg : peerMsgs \cup {noMsg}, queue : Seq(peerMsgs)]
    /\ demuxSend \in [inMsg : demuxSendMsgs \cup {noMsg}, queue : Seq(demuxSendMsgs)]
    /\ demuxProcess \in [inMsg : demuxProcessMsgs \cup {noMsg}, queue : Seq(demuxProcessMsgs)]
    /\ processDemux \in [inMsg : processDemuxMsgs \cup {noMsg}, queue : Seq(processDemuxMsgs)]
    /\ demuxSchedule \in [inMsg : demuxScheduleMsgs \cup {noMsg}, queue : Seq(demuxScheduleMsgs)]
    /\ scheduleDemux \in [inMsg : scheduleDemuxMsgs \cup {noMsg}, queue : Seq(scheduleDemuxMsgs)]
    /\ \A peerID \in PeerIDs : peerIncoming[peerID] \in [inMsg : ioMsgs \cup {noMsg}, queue : Seq(ioMsgs)]
    /\ \A peerID \in PeerIDs : peerOutgoing[peerID] \in [inMsg : peerMsgs \cup {noMsg}, queue : Seq(peerMsgs)]
    /\ peerTurn \in PeerIDs

\* initial state predicate
Init ==
    /\ turn \in Turns \* starting in any routine 
    /\ receiveDemux = initBuffer 
    /\ demuxSend = initBuffer
    /\ demuxProcess = initBuffer
    /\ processDemux = initBuffer
    /\ demuxSchedule = initBuffer
    /\ scheduleDemux = initBuffer
    /\ peerIncoming = [peerID \in PeerIDs |-> initBuffer]
    /\ peerOutgoing = [peerID \in PeerIDs |-> initBuffer]
    /\ peerTurn \in PeerIDs

(* 
Handle Actions: 
    a routine gets a message from the head of an incoming buffer, 
    and forwards it to the appropriate outgoing buffer, based on the content of the incoming message

Example: 
    The process routine checks the message at the head of the demuxProcess buffer, 
    and sends an appropriate message back to the demux routine on the processDemux buffer 
*)

(*
HandleDemuxProcess -- processor.go (handle(), lines 102-164)
Process routine handle for the message sent from the demux routine on the demuxProcess buffer
    - enabled if:
        * demuxProcess is not empty
        * processDemux is ready
    - check the message at the head of demuxProcess:
        * if it is "scBlockReceived", "scFinishedEv", or "scPeerError", 
          then do not send anything back to the demux routine
        * if it is "rProcessBlock", then either do not send anything, 
          or send "pcBlockProcessed" or "pcBlockVerificationFailure"
    - remove the message from the demuxProcess buffer
*)
HandleDemuxProcess ==
    /\ ~Empty(demuxProcess)
    /\ Ready(processDemux)
    
    /\ \/ /\ GetMessage(demuxProcess) \in {"scBlockReceived", "scFinishedEv", "scPeerError"} 
          /\ processDemux' \in RoutineSend(processDemux, {noMsg})
       \/ /\ GetMessage(demuxProcess) = "rProcessBlock"
          /\ processDemux' \in RoutineSend(processDemux, {noMsg, "pcBlockProcessed", "pcBlockVerificationFailure"})   
    
    /\ demuxProcess' = [demuxProcess EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<receiveDemux, demuxSend, demuxSchedule, scheduleDemux>>
    /\ UNCHANGED peer
    

(*
HandleDemuxSchedule -- scheduler.go (handle(), lines 663-695)
Schedule routine handle for the message sent from the demux routine on the demuxSchedule buffer
    - enabled if:
        * demuxSchedule is not empty
        * scheduleDemux is ready
    - check the message at the head of demuxSchedule:
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
          
    - remove the message from the demuxSchedule buffer
*)
HandleDemuxSchedule ==
    /\ ~Empty(demuxSchedule)
    /\ Ready(scheduleDemux)

    /\ \/ /\ GetMessage(demuxSchedule) = "bcAddNewPeer"
          /\ scheduleDemux' \in RoutineSend(scheduleDemux, {noMsg, "scSchedulerFail"}) 
       
       \/ /\ GetMessage(demuxSchedule) = "bcBlockResponse"
          /\ scheduleDemux' \in RoutineSend(scheduleDemux, {noMsg, "scBlockReceived", "scPeerError"})  
       
       \/ /\ GetMessage(demuxSchedule) = "bcNoBlockResponse"
          /\ scheduleDemux' \in RoutineSend(scheduleDemux, {noMsg, "scPeerError"}) 
       
       \/ /\ GetMessage(demuxSchedule) = "bcRemovePeer"
          /\ scheduleDemux' \in RoutineSend(scheduleDemux, {noMsg, "scSchedulerFail", "scPeerError"})
       
       \/ /\ GetMessage(demuxSchedule) = "bcStatusResponse"
          /\ scheduleDemux' \in RoutineSend(scheduleDemux, {noMsg, "scPeerError"})  
       
       \/ /\ GetMessage(demuxSchedule) = "pcBlockProcessed"
          /\ scheduleDemux' \in RoutineSend(scheduleDemux, {noMsg, "scSchedulerFail", "scFinishedEv"}) 
       
       \/ /\ GetMessage(demuxSchedule) = "pcBlockVerificationFailure"
          /\ scheduleDemux' \in RoutineSend(scheduleDemux, {noMsg, "scFinishedEv"})

    /\ demuxSchedule' = [demuxSchedule EXCEPT !.queue = Tail(@)] 
    /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, processDemux>>
    /\ UNCHANGED peer
    
(* 
HandlePeerReceive -- reactor.go (Receive(), AddPeer(), RemovePeer()) 
Receive routine handle for the peer message received from the current peer
   - enabled if:
        * the buffer of the current peer is not empty
        * the receiveDemux buffer is ready
   - add the message to the receiveDemux buffer
   - remove the message from the buffer of the current peer
   - pick a new current peer. This peer will be sent the next block request message
     by the send routine 
*)    
HandlePeerReceive == 
    /\ ~Empty(peerOutgoing[peerTurn])  
    /\ Ready(receiveDemux)
    
    /\ receiveDemux' \in RoutineSend(receiveDemux, {GetMessage(peerOutgoing[peerTurn])})
    /\ peerOutgoing' = [peerOutgoing EXCEPT ![peerTurn].queue = Tail(peerOutgoing[peerTurn].queue)]
    /\ peerTurn' \in PeerIDs
    /\ UNCHANGED <<demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux>>
    /\ UNCHANGED <<peerIncoming>>    
    
  
(*
HandleReceiveDemux -- reactor.go (demux(), line 332 - 339)
Demux routine handle for the message at the head of the receiveDemux buffer
    - enabled if 
        * receiveDemux is not empty 
        * demuxSchedule is ready
    - add the message to the demuxSchedule buffer
    - remove the message from the receiveDemux buffer
*)    
HandleReceiveDemux == 
    /\ ~Empty(receiveDemux)
    /\ Ready(demuxSchedule)
    
    /\ demuxSchedule' \in RoutineSend(demuxSchedule, {GetMessage(receiveDemux)})
    /\ receiveDemux' = [receiveDemux EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<demuxSend, demuxProcess, processDemux, scheduleDemux>>
    /\ UNCHANGED peer 

(*
HandleProcessDemux -- reactor.go (demux(), line 357 - 373)
Demux routine handle for the message at the head of the processDemux buffer
    - enabled if:
        * processDemux is not empty
        * demuxSchedule is ready
    - add the message to the demuxSchedule buffer
    - remove the message from the processDemux buffer 
*)
HandleProcessDemux ==
    /\ ~Empty(processDemux)
    /\ Ready(demuxSchedule)
    
    /\ demuxSchedule' \in RoutineSend(demuxSchedule, {GetMessage(processDemux)})
    /\ processDemux' = [processDemux EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, scheduleDemux>>
    /\ UNCHANGED peer

(*
HandleScheduleDemux -- reactor.go (demux(), line 342 - 354)
Demux routine handle for the message at the head of the scheduleDemux buffer
    - enabled if:
        * scheduleDemux is not empty
        * either the message at the head of scheduleDemux is "scBlockReceived", "scFinishedEv" or "scPeerError"
          and processDemux is ready
        * or the message at the head of scheduleDemux is "scBlockRequest" and demuxSend is ready      
    - add the message to the appropriate buffer
    - remove the message from the scheduleDemux buffer 
*)
HandleScheduleDemux ==
    /\ ~Empty(scheduleDemux)
    
    /\ \/ /\ Ready(demuxProcess)
          /\ GetMessage(scheduleDemux) \in {"scBlockReceived", "scFinishedEv", "scPeerError"}
          /\ demuxProcess' \in RoutineSend(demuxProcess, {GetMessage(scheduleDemux)})
          /\ UNCHANGED demuxSend
            
       \/ /\ Ready(demuxSend)
          /\ GetMessage(scheduleDemux) = "scBlockRequest"
          /\ demuxSend' \in RoutineSend(demuxSend, {GetMessage(scheduleDemux)})
          /\ UNCHANGED processDemux
          
    /\ scheduleDemux' = [scheduleDemux EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<receiveDemux, processDemux, demuxSchedule>>
    /\ UNCHANGED peer

(*
HandleDemuxSend -- ?.go (?, lines ?-?)
Send routine handle for the message at the head of the demuxSend buffer
    - enabled if:
        * demuxSend is not empty
        * the buffer of the current peer is ready
    - add the message to the buffer of the current peer
    - remove the message from the demuxSend buffer 
*)    
HandleDemuxSend ==
    /\ ~Empty(demuxSend)
    /\ Ready(peerIncoming[peerTurn])
    
    /\ peerIncoming' \in PeerSend(peerIncoming, peerTurn, {GetMessage(demuxSend)})
    /\ peerTurn' \in PeerIDs
    /\ demuxSend' \in [demuxSend EXCEPT !.queue = Tail(@)]
    /\ UNCHANGED <<receiveDemux, demuxProcess, processDemux, demuxSchedule, scheduleDemux>>
    /\ UNCHANGED peerOutgoing

(*
BroadcastStatusRequest -- ?.go (?, lines ?-?)
Demux routine action for broadcasting a status request message 
    - enabled if:
        * the buffers of all peers are ready
    - add the "bcStatusRequest" message to the buffers of all peers
*)    
BroadcastStatusRequest == 
    /\ \A peerID \in PeerIDs : Ready(peerIncoming[peerID])
    
    /\ peerIncoming' = PeerBroadcast(peerIncoming, "bcStatusRequest")     
    /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux>>
    /\ UNCHANGED <<peerOutgoing, peerTurn>>

(*
SendRProcessBlock -- ?.go (?, lines ?-?)
Demux routine action for sending a "rProcessBlock" message to the process routine
    - enabled if:
        * demuxProcess is ready
    - add the "rProcessBlock" message to the demuxProcess buffer
*)        
SendRProcessBlock ==
    /\ Ready(demuxProcess)
    
    /\ demuxProcess' \in RoutineSend(demuxProcess, {"rProcessBlock"}) 
    /\ UNCHANGED <<receiveDemux, demuxSend, processDemux, demuxSchedule, scheduleDemux>>
    /\ UNCHANGED peer

(*
SendPeerMsgs -- ?.go (?, lines ?-?)
Peer action for non-deterministically sending messages to the receive routine
    - enabled if:
        * the incoming buffer of the current peer is not empty  
        * the outgoing buffer of the current peer is ready
    - if the message at the head of the incoming buffer is status/block request, send a status/block response
    - otherwise, add one of the peer messages "bcAddNewPeer", "bcNoBlockResponse", "bcRemovePeer", "bcStatusResponse"
      to the buffer of the current peer
*)
SendPeerMsgs ==
    /\ ~Empty(peerIncoming[peerTurn])
    /\ Ready(peerOutgoing[peerTurn])
    /\ \/ /\ GetMessage(peerIncoming[peerTurn]) = "bcStatusRequest"
          /\ peerOutgoing' \in PeerSend(peerOutgoing, peerTurn, {"bcStatusResponse"})
       \/ /\ GetMessage(peerIncoming[peerTurn]) = "scBlockRequest"
          /\ peerOutgoing' \in PeerSend(peerOutgoing, peerTurn, {"bcBlockResponse"})
       \/ /\ peerOutgoing' \in PeerSend(peerOutgoing, peerTurn, peerMsgs)
    /\ peerIncoming' = [peerIncoming EXCEPT ![peerTurn].queue = Tail(peerIncoming[peerTurn].queue)]  
    /\ peerTurn' \in PeerIDs
    /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux>>

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
    either handle the incoming messages on the receiveDemux, processDemux, or scheduleDemux buffers,
    or broadcast a status request to all peers,
    or send a "rProcessBlock" to the process routine,
    or do nothing
*)    
DemuxRoutine ==
    \* handle the incoming messages on either receiveDemux, processDemux or scheduleDemux
    \/ HandleReceiveDemux
    \/ HandleProcessDemux
    \/ HandleScheduleDemux
       
    \* broadcast a status request
    \/ BroadcastStatusRequest 
       
    \* send a "rProcessBlock" to the process routine
    \/ SendRProcessBlock
       
    \* otherwise, do nothing       
    \/ /\ UNCHANGED buffers
       /\ UNCHANGED peer

(* 
ProcessRoutine --
    either handle the message sent by the demux routine on the demuxProcess buffer,
    or do nothing 
*)
ProcessRoutine ==
    \* handle the incoming messages on demuxProcess
    \/ HandleDemuxProcess
    \* do nothing
    \/ /\ UNCHANGED buffers
       /\ UNCHANGED peer

(* 
ScheduleRoutine --
    either handle the message sent by the demux routine on the demuxSchedule buffer,
    or do nothing 
*)
ScheduleRoutine ==
    \* handle the incoming message on demuxSchedule
    \/ HandleDemuxSchedule
    \* do nothing
    \/ /\ UNCHANGED buffers
       /\ UNCHANGED peer

(* 
SendRoutine --
    either handle the message sent by the demux routine on the demuxSend buffer,
    or do nothing 
*)
SendRoutine ==
    \* handle the incoming message on demuxSend
    \/ HandleDemuxSend
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

Buffer ==
    \/ /\ ~Ready(receiveDemux)
       /\ ~Full(receiveDemux)
       /\ receiveDemux' = BufRcv(receiveDemux)
       /\ UNCHANGED <<demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux, peerIncoming, peerOutgoing, peerTurn>>
    \/ /\ ~Ready(demuxSend)
       /\ ~Full(demuxSend)
       /\ demuxSend' = BufRcv(demuxSend)
       /\ UNCHANGED <<receiveDemux, demuxProcess, processDemux, demuxSchedule, scheduleDemux, peerIncoming, peerOutgoing, peerTurn>>
    \/ /\ ~Ready(demuxProcess)
       /\ ~Full(demuxProcess)
       /\ demuxProcess' = BufRcv(demuxProcess)
       /\ UNCHANGED <<receiveDemux, demuxSend, processDemux, demuxSchedule, scheduleDemux, peerIncoming, peerOutgoing, peerTurn>>
    \/ /\ ~Ready(processDemux)
       /\ ~Full(processDemux)
       /\ processDemux' = BufRcv(processDemux)
       /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, demuxSchedule, scheduleDemux, peerIncoming, peerOutgoing, peerTurn>>
    \/ /\ ~Ready(demuxSchedule)
       /\ ~Full(demuxSchedule)
       /\ demuxSchedule' = BufRcv(demuxSchedule)
       /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, processDemux, scheduleDemux, peerIncoming, peerOutgoing, peerTurn>>
    \/ /\ ~Ready(scheduleDemux)
       /\ ~Full(scheduleDemux)
       /\ scheduleDemux' = BufRcv(scheduleDemux)
       /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, peerIncoming, peerOutgoing, peerTurn>>   
    \/ /\ \E peerID \in PeerIDs : /\ ~Ready(peerIncoming[peerID])
                                  /\ ~Full(peerIncoming[peerID])
                                  /\ peerIncoming' = [peerIncoming EXCEPT ![peerID] = BufRcv(@)]
       /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux, peerOutgoing, peerTurn>>
    \/ /\ \E peerID \in PeerIDs : /\ ~Ready(peerOutgoing[peerID])
                                  /\ ~Full(peerOutgoing[peerID])
                                  /\ peerOutgoing' = [peerOutgoing EXCEPT ![peerID] = BufRcv(@)]
       /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux, peerIncoming, peerTurn>>       
    
       
     
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
       \/ Buffer 
    /\ turn' \in Turns  

Fairness == 
    /\ WF_vars(Buffer)

Spec == Init /\ [][Next]_vars /\ Fairness
  

GoodState ==
    \/ ~Empty(receiveDemux) => Ready(demuxSchedule)
    \/ ~Empty(processDemux) => Ready(demuxSchedule)
    \/ /\ ~Empty(scheduleDemux) 
       /\ GetMessage(scheduleDemux) \in {"scBlockReceived", "scFinishedEv", "scPeerError"}  
                 => Ready(demuxProcess)
    \/ /\ ~Empty(scheduleDemux) 
       /\ GetMessage(scheduleDemux) = "scBlockRequest"   
                 => Ready(demuxSend)                          
    \/ Ready(demuxProcess)
    \/ \A peerID \in PeerIDs: Ready(peerIncoming[peerID])
    
    \/ ~Empty(demuxProcess) => Ready(processDemux)    
    
    \/ ~Empty(demuxSchedule) => Ready(scheduleDemux)
    
    \/ ~Empty(demuxSend) => Ready(peerIncoming[peerTurn])
    
    \/ \A peerID \in PeerIDs: ~Empty(peerIncoming[peerID]) => Ready(peerOutgoing[peerID])
    
    \/ ~Empty(peerOutgoing[peerTurn]) => Ready(receiveDemux)
        
=============================================================================
\* Modification History
\* Last modified Tue Feb 18 18:07:27 CET 2020 by ilina
\* Created Wed Feb 05 15:44:25 CET 2020 by ilina
