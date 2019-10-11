---------------------------- MODULE Lightclient ----------------------------
EXTENDS Integers, Sequences

\* the parameters of Lite Client
CONSTANTS
  TRUSTED_HEIGHT,
    (* an index of the block header that the light client trusts by social consensus *)
  TO_VERIFY_HEIGHT
    (* an index of the block header that the light client tries to verify *)

\* the parameters that are propagated into Blockchain
CONSTANTS
  AllNodes,
    (* a set of all nodes that can act as validators (correct and faulty) *)
  ULTIMATE_HEIGHT,
    (* a maximal height that can be ever reached (modelling artifact) *)
  MAX_POWER
    (* a maximal voting power of a single node *)

\* the state variables of Blockchain, see Blockchain.tla for the details
VARIABLES tooManyFaults, height, minTrustedHeight, blockchain, Faulty

\* All the variables of Blockchain. For some reason, BC!vars does not work
bcvars == <<tooManyFaults, height, minTrustedHeight, blockchain, Faulty>>

(* Create an instance of Blockchain.
   We could write EXTENDS Blockchain, but then all the constants and state variables
   would be hidden inside the Blockchain module.
 *) 
BC == INSTANCE Blockchain WITH tooManyFaults <- tooManyFaults, height <- height,
  minTrustedHeight <- minTrustedHeight, blockchain <- blockchain, Faulty <- Faulty

(************************** Lite client ************************************)

\* TBD

LCInit == TRUE

LCNext == UNCHANGED bcvars

(************************* Lite client + Blockchain ************************)
Init == LCInit /\ BC!Init

Next == LCNext \/ BC!Next


=============================================================================
\* Modification History
\* Last modified Fri Oct 11 16:24:59 CEST 2019 by igor
\* Created Wed Oct 02 16:39:42 CEST 2019 by igor
