----------------------------- MODULE fastsyncV2 -----------------------------
(*
 * This is a specification of the fastsync protocol, version 2.
 *
 * In this specification, we have two parties:
 *  - the state machine that is doing fastsync
 *  - the environment (the rest of the node and the peers)
 *
 * Events:
 * At every step, the fastsync state machine
 * is receiving an input event and producing an output event.
 *
 * Messages:
 * We have a set of messages, and the node can receive messages from this set.
 *)
EXTENDS Integers 

CONSTANTS MAX_HEIGHT, NPEERS

\* the set of potential heights
Heights == 1..MAX_HEIGHT
\* the set of all peer ids the node can receive a message from
AllPeerIds == 1..NPEERS

\* a special value for an undefined height
NilHeight == 0

\* the variables of the node running fastsync
VARIABLES
  state,
  height,
  peerIds,
  peerHeights,
  inEvent,
  outEvent

States == { "init", "running", "stopped" }

NoEvent == [type |-> "None"]

InEvents ==
    {NoEvent}
        \union
    [type: {"start"}, height: Heights]
        \union
    [type: {"statusResponse"}, peerId: AllPeerIds, height: Heights]
        \union
    [type: {"blockResponse"}]
        \union
    [type: {"peerRemove"}]

OutEvents ==
    {NoEvent}
        \union
    [type: {"statusRequest"}]
        \union  
    [type: {"blockRequest"}]  
        \union  
    [type: {"peerError"}, peerId: AllPeerIds]  

\* the spec of the node running the protocol
InitSM ==
    /\ state = "init"
    /\ outEvent = NoEvent
    /\ height = NilHeight
    /\ peerIds = {}
    /\ peerHeights = [ p \in AllPeerIds |-> NilHeight ]

OnStart ==
    /\ inEvent.type = "start"
    /\ state = "init"
    /\ state' = "running"
    /\ height' = inEvent.height
    /\ outEvent' = [type |-> "statusRequest"]
    /\ UNCHANGED <<peerIds, peerHeights>>
    
OnStatusResponse ==
    /\ inEvent.type = "statusResponse"
    /\ state = "running"
    /\ UNCHANGED <<state, height>>
    /\ IF /\ inEvent.peerId \in peerIds
          /\ inEvent.height < peerHeights[inEvent.peerId] 
        THEN \* the peer has sent us a lower height
            /\ outEvent' = [type |-> "peerError", peerId |-> inEvent.peerId]
            /\ peerIds' = peerIds \ {inEvent.peerId}
            /\ peerHeights' =
                [ peerHeights EXCEPT ![inEvent.peerId] = NilHeight]
        ELSE \* a new peer or a higher height
            /\ peerIds' = peerIds \union {inEvent.peerId}
            /\ peerHeights' =
                [ peerHeights EXCEPT ![inEvent.peerId] = inEvent.height]
            /\ outEvent' = NoEvent

NextSM ==
    \/ OnStart
    \/ OnStatusResponse
    \/ UNCHANGED <<state, height, peerIds, peerHeights, outEvent>>

\* the spec of the environment
InitEnv ==
    \E h \in Heights:
        inEvent = [type |-> "start", height |-> h]

InitChaos == inEvent \in InEvents

NextEnv ==
    inEvent' \in InEvents

\* the composition of the node and the environment
Init == InitSM /\ InitEnv

Next == NextSM /\ NextEnv

\* properties to check
TypeOK ==
    /\ inEvent \in InEvents
    /\ outEvent \in OutEvents
    /\ height \in Heights \cup {NilHeight}
    /\ peerIds \subseteq AllPeerIds
    /\ peerHeights \in [AllPeerIds -> Heights \cup {NilHeight}]



=============================================================================
\* Modification History
\* Last modified Wed Dec 18 15:59:00 CET 2019 by igor
\* Created Wed Dec 18 14:08:53 CET 2019 by igor
