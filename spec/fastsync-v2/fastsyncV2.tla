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

\* the variables of the environment
VARIABLES
  envState,
  turn \* who is taking the turn: "Environment" or "SM" 

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
    \/ state = "finished" /\ UNCHANGED <<state, height, peerIds, peerHeights, outEvent>>

\* the spec of the environment
(*
  The environment is modelling the input events to the node.
  It does so by reacting to the output events from the state machine.
  
  The correct peers should increase their heights, as in the blockchain.
  The faulty peers can do whatever they like.
  
  TODO: how do we model timeouts?
  
  Unresponsiveness, reordering of messages, incorrect messages (faulty blocks, arbitrary heights).
  Downloading two consequtive blocks to do verification (h and h+1 may come from different peers).
  
  Termination properties are more important than safety.
 *)
InitEnv ==
    /\ envState = "init"
    /\ \E h \in Heights:
        inEvent = [type |-> "start", height |-> h]

InitChaos == inEvent \in InEvents

OnStatusRequest ==
    /\ outEvent.type = "statusRequest"
    /\ inEvent' \in [type: {"statusResponse"}, peerId: AllPeerIds, height: Heights]
    /\ UNCHANGED <<envState>>
    \*/\ envState' = "statusRequested"

NextEnv ==
    \/ OnStatusRequest
    \/  /\ outEvent.type /= "statusRequest"
        /\ inEvent' \in InEvents
        /\ UNCHANGED <<envState>>

\* the composition of the node and the environment
Init ==
    /\ turn = "Environment"
    /\ InitSM
    /\ InitEnv

Next ==
    IF turn = "Environment"
    THEN
        /\ NextEnv
        /\ turn' = "SM"
        /\ UNCHANGED <<state, height, peerIds, peerHeights, outEvent>>
    ELSE
        /\ NextSM
        /\ turn' = "Environment"
        /\ inEvent' = NoEvent
        /\ UNCHANGED <<envState>>

\* properties to check
TypeOK ==
    /\ inEvent \in InEvents
    /\ outEvent \in OutEvents
    /\ height \in Heights \cup {NilHeight}
    /\ peerIds \subseteq AllPeerIds
    /\ peerHeights \in [AllPeerIds -> Heights \cup {NilHeight}]

\* A property to check:    
\* if a peer is lowering its height, it will be removed forever

(*
 if at some point, peerHeights[p] = h1 for some h1,
     and later peerHeights[p] = h2,
     and h1 > h2, then p \in peerIds from that point on.
 *)
LoweringPeerRemoved ==
    \A p \in AllPeerIds:
    <>(\E h1 \in Heights:
        /\ peerHeights[p] = h1
        /\ <>(inEvent.type = "statusResponse"
                /\ inEvent.peerId = p /\ inEvent.height < h1)
            => <>[](p \notin peerIds)
       )

\* 1. Environment: inEvent
\* ...
\* ...
\* ...
\* 2. SM processes inEvent
\* 3. p \notin peerIds

vars == <<state, height, peerIds, peerHeights, inEvent, outEvent, envState>>

\* for every peer p, it is always true that if the status response
\* has a height less than the registered height of p,
\* then from some point on, p is removed from the set of peers 
LoweringPeerRemoved2 ==
    \A p \in AllPeerIds:
    []((turn = "SM"
            /\ inEvent.type = "statusResponse"
            /\ inEvent.peerId = p
            /\ inEvent.height < peerHeights[p])
        => <>[](p \notin peerIds))
        \* => [][p \notin peerIds']_vars)

\* temporal assumptions about the environment
HonestEnv ==
    []((outEvent.type = "statusRequest")
        => \/ <>(inEvent.type = "statusResponse")
           \/ <>(inEvent.type = "statusResponseTimeout"))


=============================================================================
\* Modification History
\* Last modified Wed Jan 08 15:16:03 CET 2020 by igor
\* Created Wed Dec 18 14:08:53 CET 2019 by igor
