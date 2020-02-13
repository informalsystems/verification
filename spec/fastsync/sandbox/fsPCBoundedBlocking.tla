------------------------ MODULE fsPCBoundedBlocking ------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS
  MaxQueueSize,
  \* peers send unsolicited responses with numbers >= baseID
  baseID,
  \* number of responses demux waits before finishing
  minNumResp

None == -1  

(*--algorithm message_queue
variables
  \* queues prefixed by A, B..so state is easy to inspect
  Asend_q = <<>>,
  Breceive_q = <<>>,
  Cdemux_q = <<>>,
  msg = [type |-> "none"],
  peers = {"p1"},
  done = FALSE, \* set to TRUE when demux is done, send and receive read this and stop
  
define
  FilledQueue(queue) == Len(queue) >= MaxQueueSize
  FilledQueues == 
    /\ FilledQueue(Breceive_q)
    /\ FilledQueue(Asend_q)
    /\ FilledQueue(Cdemux_q) 
end define;

macro add_to_blocking_queue(queue, val) begin
  await Len(queue) < MaxQueueSize;
  queue := Append(queue, val);
end macro;

macro read_from_queue(queue) begin
    await Len(queue) > 0;
    \* write message in global variable, not possible to return values here or from procedure
    msg := Head(queue);
    queue := Tail(queue);
end macro;
    
(* 
<> bounded blocking queues
              
   -------------------------------------
   |               peer                |
   |  ..............................   |
   |  |                            |   |
   |  v                            |   |         
   |send                        receive|
   |  |                            ^   |
   |  |                            |   |
   ---+----------------------------+----
      |                            |
      |                            |
   ---+----------------------------+----
   |  |          this node         |   |
   |  |                            |   |
   |  v <> Breceive_q              ^   |
   |receive                       send |
   |  |                            ^ <> Asend_q
   |  |                            |   |
   |  v <> Cdemux_q (1000)         |   |
   |  ..............................   |
   |             demux                 |
   -------------------------------------
      
*)

process demux = "demux"
variables 
  counter = 1
begin Demux:
  while TRUE do
    either
      add_to_blocking_queue(Asend_q, [type |-> "bcStatusRequest", num |-> counter]);
      counter := counter + 1;
    or
      read_from_queue(Cdemux_q);
      if msg.type = "bcStatusResponse" then
        \* terminates on the third status response from peer/ receive
        if msg.num > 0 /\ msg.num < baseID then
          done := TRUE;
          goto Done;
        else
          add_to_unblocking_queue(Asend_q, [type |-> "bcStatusRequest", num |-> counter]);
          counter := counter + 1;
        end if;
      end if;
      
    end either;      
  end while;
end process;

process send \in {"p1_tx"}
begin Send:
  while TRUE do
    if done then
      goto Done
    else
      read_from_queue(Asend_q);
      add_to_blocking_queue(Breceive_q, msg);
    end if;
  end while;
end process;

process receive \in {"p1_rx"}
variables
  counter = baseID
begin Receive:
  while TRUE do
    if done then
      goto Done
    else
      either
        add_to_blocking_queue(Cdemux_q, [type |-> "bcStatusResponse", num |-> counter]);
        counter := counter + 1
      or
        read_from_queue(Breceive_q);
        add_to_blocking_queue(Cdemux_q, [type |-> "bcStatusResponse", num |-> msg.num]);
      end either;
    end if;
  end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
\* Process variable counter of process demux at line 67 col 3 changed to counter_
VARIABLES Asend_q, Breceive_q, Cdemux_q, msg, peers, done, pc

(* define statement *)
FilledQueue(queue) == Len(queue) >= MaxQueueSize
FilledQueues ==
  /\ FilledQueue(Breceive_q)
  /\ FilledQueue(Asend_q)
  /\ FilledQueue(Cdemux_q)

VARIABLES counter_, counter

vars == << Asend_q, Breceive_q, Cdemux_q, msg, peers, done, pc, counter_, 
           counter >>

ProcSet == {"demux"} \cup ({"p1_tx"}) \cup ({"p1_rx"})

Init == (* Global variables *)
        /\ Asend_q = <<>>
        /\ Breceive_q = <<>>
        /\ Cdemux_q = <<>>
        /\ msg = [type |-> "none"]
        /\ peers = {"p1"}
        /\ done = FALSE
        (* Process demux *)
        /\ counter_ = 1
        (* Process receive *)
        /\ counter = [self \in {"p1_rx"} |-> baseID]
        /\ pc = [self \in ProcSet |-> CASE self = "demux" -> "Demux"
                                        [] self \in {"p1_tx"} -> "Send"
                                        [] self \in {"p1_rx"} -> "Receive"]

Demux == /\ pc["demux"] = "Demux"
         /\ \/ /\ Len(Asend_q) < MaxQueueSize
               /\ Asend_q' = Append(Asend_q, ([type |-> "bcStatusRequest", num |-> counter_]))
               /\ counter_' = counter_ + 1
               /\ pc' = [pc EXCEPT !["demux"] = "Demux"]
               /\ UNCHANGED <<Cdemux_q, msg, done>>
            \/ /\ Len(Cdemux_q) > 0
               /\ Len(Cdemux_q) > 0
               /\ msg' = Head(Cdemux_q)
               /\ Cdemux_q' = Tail(Cdemux_q)
               /\ IF msg'.type = "bcStatusResponse"
                     THEN /\ IF msg'.num > minNumResp /\ msg'.num < baseID
                                THEN /\ done' = TRUE
                                     /\ pc' = [pc EXCEPT !["demux"] = "Done"]
                                     /\ UNCHANGED << Asend_q, counter_ >>
                                ELSE /\ Len(Asend_q) < MaxQueueSize
                                     /\ Asend_q' = Append(Asend_q, ([type |-> "bcStatusRequest", num |-> counter_]))
                                     /\ counter_' = counter_ + 1
                                     /\ pc' = [pc EXCEPT !["demux"] = "Demux"]
                                     /\ done' = done
                     ELSE /\ pc' = [pc EXCEPT !["demux"] = "Demux"]
                          /\ UNCHANGED << Asend_q, done, counter_ >>
         /\ UNCHANGED << Breceive_q, peers, counter >>

demux == Demux

Send(self) == /\ pc[self] = "Send"
              /\ IF done
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << Asend_q, Breceive_q, msg >>
                    ELSE /\ Len(Asend_q) > 0
                         /\ msg' = Head(Asend_q)
                         /\ Asend_q' = Tail(Asend_q)
                         /\ Len(Breceive_q) < MaxQueueSize
                         /\ Breceive_q' = Append(Breceive_q, msg')
                         /\ pc' = [pc EXCEPT ![self] = "Send"]
              /\ UNCHANGED << Cdemux_q, peers, done, counter_, counter >>

send(self) == Send(self)

Receive(self) == /\ pc[self] = "Receive"
                 /\ IF done
                       THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << Breceive_q, Cdemux_q, msg, counter >>
                       ELSE /\ \/ /\ Len(Cdemux_q) < MaxQueueSize
                                  /\ Cdemux_q' = Append(Cdemux_q, ([type |-> "bcStatusResponse", num |-> counter[self]]))
                                  /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                                  /\ UNCHANGED <<Breceive_q, msg>>
                               \/ /\ Len(Breceive_q) > 0
                                  /\ msg' = Head(Breceive_q)
                                  /\ Breceive_q' = Tail(Breceive_q)
                                  /\ Len(Cdemux_q) < MaxQueueSize
                                  /\ Cdemux_q' = Append(Cdemux_q, ([type |-> "bcStatusResponse", num |-> msg'.num]))
                                  /\ UNCHANGED counter
                            /\ pc' = [pc EXCEPT ![self] = "Receive"]
                 /\ UNCHANGED << Asend_q, peers, done, counter_ >>

receive(self) == Receive(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == demux
           \/ (\E self \in {"p1_tx"}: send(self))
           \/ (\E self \in {"p1_rx"}: receive(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Feb 13 16:01:13 CET 2020 by ancaz
\* Created Tue Jan 07 16:21:41 CET 2020 by ancaz
