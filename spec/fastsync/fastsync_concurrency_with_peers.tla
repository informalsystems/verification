------------------ MODULE fastsync_concurrency_with_peers ------------------

\* Reference go code :
\* https://github.com/tendermint/tendermint/blob/brapse/blockchain-v2-riri-reactor/blockchain/v2
\* commit: f7b76d5
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
          peers, \* the peer buffers
          peerTurn \* the current peer that receives a block request and sends a block response

\* set of peers
PeerIDs == 1..NrPeers

vars == <<turn, receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux, peers, peerTurn>>          
buffers == <<receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux>>
peer == <<peers, peerTurn>>

\* set of messages that the peers send to the receive routine
peerMsgs == {"bcAddNewPeer", "bcBlockResponse", "bcNoBlockResponse", "bcRemovePeer", "bcStatusResponse"} 

\* set of messages that the process routine sends to the demux routine (forwarded to the schedule routine)
processMsgs == {"pcBlockProcessed", "pcBlockVerificationFailure"} 

\* set of messages that the schedule routine sends to the demux routine (forwarded to the process routine)
scheduleMsgs == {"scBlockReceived", "scFinishedEv", "scPeerError", "scSchedulerFail"} 

\* set of io messages that the demux routine sends to the send routine (blockRequest) or broadcasts to all peers (statusRequest)
ioMsgs == {"scBlockRequest", "bcStatusRequest"}  

\* set of messages that are sent periodically (we model them by non-determinism) 
timerMsgs == {"rBlockProcessed"}

\* special message denoting no message
noMsg == "noMsg"

\* set of all messages
Msgs == peerMsgs \cup processMsgs \cup scheduleMsgs \cup ioMsgs \cup timerMsgs \cup {noMsg}
 
\* set of turns used to schedule the different routines
Turns == {"receiveRoutine", "demuxRoutine", "sendRoutine", "processRoutine", "scheduleRoutine", "peer"} 

\* useful queue predicates/actions  
\* a queue is full if its length is equal to QueueLength   
Full(queue) ==
    Len(queue) = QueueLength
    
\* a queue is empty if its length is equal to 0    
Empty(queue) ==
    Len(queue) = 0 
 
Init ==
    /\ turn \in Turns \* starting in any routine 
    /\ receiveDemux = <<>>   
    /\ demuxSend = <<>>
    /\ demuxProcess = <<>>
    /\ processDemux = <<>>
    /\ demuxSchedule = <<>>
    /\ scheduleDemux = <<>>
    /\ peers = [peerID \in PeerIDs |-> <<>>]
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
        * processDemux is not full
    - check the message at the head of demuxProcess:
        * if it is "scBlockReceived", "scFinishedEv", or "scPeerError", 
          then do not send anything back to the demux routine
        * if it is "rProcessBlock", then either do not send anything, 
          or send "pcBlockProcessed" or "pcBlockVerificationFailure"
    - remove the message from the demuxProcess buffer
*)
HandleDemuxProcess ==
    /\ ~Empty(demuxProcess)
    /\ ~Full(processDemux)
    
    /\ \/ /\ Head(demuxProcess) \in {"scBlockReceived", "scFinishedEv", "scPeerError"} 
          /\ UNCHANGED processDemux
       \/ /\ Head(demuxProcess) = "rProcessBlock"
          \* non-deterministic assignment
          /\ processDemux' \in {processDemux, \* either nothing is sent 
                                Append(processDemux, "pcBlockProcessed"), \* or a "pcBlockProcessed" is sent
                                Append(processDemux, "pcBlockVerificationFailure")} \* or a "pcBlockVerificationFailure" is sent   
    /\ demuxProcess' = Tail(demuxProcess)
    /\ UNCHANGED <<receiveDemux, demuxSend, demuxSchedule, scheduleDemux>>
    /\ UNCHANGED <<peers, peerTurn>>
    

(*
HandleDemuxSchedule -- scheduler.go (handle(), lines 663-695)
Schedule routine handle for the message sent from the demux routine on the demuxSchedule buffer
    - enabled if:
        * demuxSchedule is not empty
        * scheduleDemux is not full
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
    /\ ~Full(scheduleDemux)

    /\ \/ /\ Head(demuxSchedule) = "bcAddNewPeer"
          /\ scheduleDemux' \in {scheduleDemux, \* either nothing is sent 
                                 Append(scheduleDemux, "scSchedulerFail")} \* or a "scSchedulerFail" is sent 
       
       \/ /\ Head(demuxSchedule) = "bcBlockResponse"
          /\ scheduleDemux' \in {scheduleDemux, \* either nothing is sent
                                 Append(scheduleDemux, "scBlockReceived"), \* or a "scBlockReceived" is sent
                                 Append(scheduleDemux, "scPeerError")} \* or a "scPeerError" is sent
       
       \/ /\ Head(demuxSchedule) = "bcNoBlockResponse"
          /\ scheduleDemux' \in {scheduleDemux, \* either nothing is sent
                                 Append(scheduleDemux, "scPeerError")} \* or a "scPeerError" is sent
       
       \/ /\ Head(demuxSchedule) = "bcRemovePeer"
          /\ scheduleDemux' \in {scheduleDemux, \* either nothing is sent
                                 Append(scheduleDemux, "scSchedulerFail"), \* or a "scSchedulerFail" is sent
                                 Append(scheduleDemux, "scPeerError")} \* or a "scPeerError" is sent
       
       \/ /\ Head(demuxSchedule) = "bcStatusResponse"
          /\ scheduleDemux' \in {scheduleDemux, \* either nothing is sent 
                                 Append(scheduleDemux, "scPeerError")} \* or a "scPeerError" is sent
       
       \/ /\ Head(demuxSchedule) = "pcBlockProcessed"
          /\ scheduleDemux' \in {scheduleDemux, \* either nothing is sent
                                 Append(scheduleDemux, "scSchedulerFail"), \* or a "scSchedulerFail" is sent
                                 Append(scheduleDemux, "scFinishedEv")} \* or a "scFinishedEv" is sent
       
       \/ /\ Head(demuxSchedule) = "pcBlockVerificationFailure"
          /\ scheduleDemux' \in {scheduleDemux, \* either nothing is sent
                                 Append(scheduleDemux, "scFinishedEv")} \* or a "scFinishedEv" is sent   
    /\ demuxSchedule' = Tail(demuxSchedule)
    /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, processDemux>>
    /\ UNCHANGED <<peers, peerTurn>>
    
(* 
HandlePeerReceive -- reactor.go (Receive(), AddPeer(), RemovePeer()) 
Receive routine handle for the peer message received from the current peer
   - enabled if:
        * the buffer of the current peer is not empty
        * the receiveDemux buffer is not full
   - add the message to the receiveDemux buffer
   - remove the message from the buffer of the current peer
   - pick a new current peer. This peer will be sent the next block request message
     by the send routine 
*)    
HandlePeerReceive == 
    /\ ~Empty(peers[peerTurn])  
    /\ ~Full(receiveDemux)
    
    /\ receiveDemux' = Append(receiveDemux, Head(peers[peerTurn]))
    /\ peers' = [peers EXCEPT ![peerTurn] = Tail(peers[peerTurn])]
    /\ peerTurn' \in PeerIDs
    /\ UNCHANGED <<demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux>>    
    
  
(*
HandleReceiveDemux -- reactor.go (demux(), line 332 - 339)
Demux routine handle for the message at the head of the receiveDemux buffer
    - enabled if 
        * receiveDemux is not empty 
        * demuxSchedule is not full
    - add the message to the demuxSchedule buffer
    - remove the message from the receiveDemux buffer
*)    
HandleReceiveDemux == 
    /\ ~Empty(receiveDemux)
    /\ ~Full(demuxSchedule)
    
    /\ demuxSchedule' = Append(demuxSchedule, Head(receiveDemux))
    /\ receiveDemux' = Tail(receiveDemux)
    /\ UNCHANGED <<demuxSend, demuxProcess, processDemux, scheduleDemux>>
    /\ UNCHANGED <<peers, peerTurn>> 

(*
HandleProcessDemux -- reactor.go (demux(), line 357 - 373)
Demux routine handle for the message at the head of the processDemux buffer
    - enabled if:
        * processDemux is not empty
        * demuxSchedule is not full
    - add the message to the demuxSchedule buffer
    - remove the message from the processDemux buffer 
*)
HandleProcessDemux ==
    /\ ~Empty(processDemux)
    /\ ~Full(demuxSchedule)
    
    /\ demuxSchedule' = Append(demuxSchedule, Head(processDemux))
    /\ processDemux' = Tail(processDemux)
    /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, scheduleDemux>>
    /\ UNCHANGED <<peers, peerTurn>>

(*
HandleScheduleDemux -- reactor.go (demux(), line 342 - 354)
Demux routine handle for the message at the head of the scheduleDemux buffer
    - enabled if:
        * scheduleDemux is not empty
        * either the message at the head of scheduleDemux is "scBlockReceived", "scFinishedEv" or "scPeerError"
          and processDemux is not full
        * or the message at the head of scheduleDemux is "scBlockRequest" and demuxSend is not full      
    - add the message to the appropriate buffer
    - remove the message from the scheduleDemux buffer 
*)
HandleScheduleDemux ==
    /\ ~Empty(scheduleDemux)
    
    /\ \/ /\ ~Full(demuxProcess)
          /\ Head(scheduleDemux) \in {"scBlockReceived", "scFinishedEv", "scPeerError"}
          /\ demuxProcess' = Append(demuxProcess, Head(scheduleDemux))
          /\ UNCHANGED demuxSend
            
       \/ /\ ~Full(demuxSend)
          /\ Head(scheduleDemux) = "scBlockRequest"
          /\ demuxSend' = Append(demuxSend, Head(scheduleDemux))
          /\ UNCHANGED processDemux
          
    /\ scheduleDemux' = Tail(scheduleDemux)
    /\ UNCHANGED <<receiveDemux, processDemux, demuxSchedule>>
    /\ UNCHANGED <<peers, peerTurn>>

(*
HandleDemuxSend -- ?.go (?, lines ?-?)
Send routine handle for the message at the head of the demuxSend buffer
    - enabled if:
        * demuxSend is not empty
        * the buffer of the current peer is not full       
    - add the message to the buffer of the current peer
    - remove the message from the demuxSend buffer 
*)    
HandleDemuxSend ==
    /\ ~Empty(demuxSend)
    /\ ~Full(peers[peerTurn])
    
    /\ peers' = [peers EXCEPT ![peerTurn] = Append(peers[peerTurn], "bcBlockResponse")]
    /\ peerTurn' \in PeerIDs
    /\ demuxSend' = Tail(demuxSend)
    /\ UNCHANGED <<receiveDemux, demuxProcess, processDemux, demuxSchedule, scheduleDemux>>
    

(*
BroadcastStatusRequest -- ?.go (?, lines ?-?)
Demux routine action for broadcasting a status request message 
    - enabled if:
        * the buffers of all peers are not full
    - add the "bcStatusRequest" message to the buffers of all peers
*)    
BroadcastStatusRequest == 
    /\ \A peerID \in PeerIDs : ~Full(peers[peerID])
    
    \* we assume that the peer immediately receives the request and adds a "bcStatusResponse" in its buffer
    /\ peers' = [peerID \in PeerIDs |-> Append(peers[peerID], "bcStatusResponse")]    
    /\ UNCHANGED <<receiveDemux, demuxSend, demuxProcess, processDemux, demuxSchedule, scheduleDemux>>
    /\ UNCHANGED <<peerTurn>>

(*
SendRProcessBlock -- ?.go (?, lines ?-?)
Demux routine action for sending a "rProcessBlock" message to the process routine
    - enabled if:
        * demuxProcess is not full
    - add the "rProcessBlock" message to the demuxProcess buffer
*)        
SendRProcessBlock ==
    /\ ~Full(demuxProcess)
    
    /\ demuxProcess' = Append(demuxProcess, "rProcessBlock")
    /\ UNCHANGED <<receiveDemux, demuxSend, processDemux, demuxSchedule, scheduleDemux>>
    /\ UNCHANGED <<peers, peerTurn>>

(*
SendPeerMsgs -- ?.go (?, lines ?-?)
Peer action for non-deterministically sending messages to the receive routine
    - enabled if: 
        * the buffer of the current peer is not full
    - add one of the peer messages "bcAddNewPeer", "bcNoBlockResponse", "bcRemovePeer", "bcStatusResponse"
      to the buffer of the current peer
*)
SendPeerMsgs ==
    /\ ~Full(peers[peerTurn])
    
    /\ peers' \in {[peers EXCEPT ![peerTurn] = Append(peers[peerTurn], "bcAddNewPeer")],
                   [peers EXCEPT ![peerTurn] = Append(peers[peerTurn], "bcNoBlockResponse")],
                   [peers EXCEPT ![peerTurn] = Append(peers[peerTurn], "bcRemovePeer")],
                   [peers EXCEPT ![peerTurn] = Append(peers[peerTurn], "bcStatusResponse")]} 
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
    /\ turn' \in Turns  

Fairness ==
    /\ WF_vars(Next)
    
Spec == Init /\ [][Next]_vars /\ Fairness    

 
GoodStateSchedule ==
    ~Empty(demuxSchedule) => ~Full(scheduleDemux)  

\*BadStateSchedule ==
\*    ~Empty(demuxSchedule) /\ Full(scheduleDemux)

    
GoodStateProcess ==
    ~Empty(demuxProcess) => ~Full(processDemux)    

\*BadStateProcess==
\*    ~Empty(demuxProcess) /\ Full(processDemux)


GoodStateReceive ==
    ~Empty(peers[peerTurn]) => ~Full(receiveDemux)

\*BadStateReceive==
\*    ~Empty(peers[peerTurn]) /\ Full(receiveDemux)

    
GoodStateSend ==
    ~Empty(demuxSend) => ~Full(peers[peerTurn])

\*BadStateSend==
\*    ~Empty(demuxSend) /\ Full(peers[peerTurn])
    
    
GoodStateDemux ==
    \/ ~Empty(processDemux) => ~Full(demuxSchedule)
    \/ ~Empty(receiveDemux) => ~Full(demuxSchedule)
    \/ ~Empty(scheduleDemux) => /\ Head(scheduleDemux) \in {"scBlockReceived", "scFinishedEv", "scPeerError"} 
                                /\ ~Full(demuxProcess)
    \/ ~Empty(scheduleDemux) => /\ Head(scheduleDemux) = "scBlockRequest"  
                                /\ ~Full(demuxSend)
    \/ \A peerID \in PeerIDs: ~Full(peers[peerID])
    \/ ~Full(demuxProcess)
    

=============================================================================
\* Modification History
\* Last modified Fri Feb 07 17:26:02 CET 2020 by ilina
\* Created Wed Feb 05 15:44:25 CET 2020 by ilina
