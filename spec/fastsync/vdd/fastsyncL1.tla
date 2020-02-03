----------------------------- MODULE fastsyncL1 -----------------------------
(*
 L1 specification of the fast sync protocol.
*)

EXTENDS Integers, FiniteSets, Sequences

\* the protocol parameters
CONSTANTS
   MAX_HEIGHT,             \* an upper bound on the blockchain height (to bound the chain for model checking)
   BLOCKCHAIN_HEIGHT       \* initial blockchain height
    
\* we might want to add assume that BLOCKCHAIN_HEIGHT < MAX_HEIGHT

\* the set of potential heights
Heights == 1..MAX_HEIGHT

Blocks == [ height: Heights ]

\* visible state
VARIABLES blocks, height, state

vars == <<blocks, height, state>>

States == { "active", "finished" }


\* The initial states
Init ==
    /\ blocks = [h \in 1..BLOCKCHAIN_HEIGHT |-> [height |-> h]]
    /\ height = CHOOSE i \in 1..BLOCKCHAIN_HEIGHT: i <= BLOCKCHAIN_HEIGHT 
    /\ state = "active"

AddBlock == 
    \/ Len(blocks) >= MAX_HEIGHT /\ UNCHANGED vars
    \/ /\ Len(blocks) < MAX_HEIGHT  \* add one more block
       /\ LET nextBlock == [height |-> Len(blocks) + 1] 
          IN blocks' = [ blocks EXCEPT ![nextBlock.height] = nextBlock]
       /\ UNCHANGED <<height, state>>   
           
ExecuteBlock ==
     /\ height < Len(blocks) 
     /\ height' = height + 1
     /\ IF height' = Len(blocks) 
        THEN state' = "finished" 
        ELSE state' = state
     /\ UNCHANGED blocks
     
\* The system transitions: at every step, add one more block until the BLOCKCHAIN_HEIGHT is reached
Next ==
    \/ AddBlock
    \/ ExecuteBlock

\* a few simple properties that trigger counterexamples
NeverFinishAtMax == [] (state = "finished" => height < Len(blocks))

NeverFinishAboveBlockchainInitHeight == [] (state = "finished" => height > BLOCKCHAIN_HEIGHT)

=============================================================================
\* Modification History
\* Last modified Mon Feb 03 17:55:32 CET 2020 by zarkomilosevic
\* Created Mon Feb 03 11:45:26 CET 2020 by zarkomilosevic
