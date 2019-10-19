---------------------------- MODULE Lightclient ----------------------------
EXTENDS Integers, Sequences

\* the parameters of Lite Client
CONSTANTS
  TRUSTED_HEIGHT,
    (* an index of the block header that the light client trusts by social consensus *)
  TO_VERIFY_HEIGHT
    (* an index of the block header that the light client tries to verify *)

VARIABLES
  finished,  (* if the light client has finished *)
  verdict,   (* the verdict of the lite client *)
  checkedHeader (* the signed header that was checked by the client *)
  
lcvars == <<finished, verdict, checkedHeader>>  

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

CheckSupport(heightToTrust, heightToVerify) ==
  LET th == blockchain[heightToTrust] IN
    \E sheader \in BC!SignedHeaders: \* received from the full node
        /\ sheader[1].height = heightToVerify
        /\ checkedHeader' = sheader
        /\  IF minTrustedHeight > heightToTrust
                \/ ~(sheader[2] \subseteq (DOMAIN sheader[1].VP))
            THEN verdict' = FALSE
            ELSE
              LET TP == BC!PowerOfSet(th.NextVP, DOMAIN th.NextVP)
                  SP == BC!PowerOfSet(th.NextVP,
                    sheader[2] \intersect DOMAIN th.NextVP)
              IN
              IF heightToVerify = heightToTrust + 1
              THEN verdict' = (3 * SP > 2 * TP)   \* special case, check 2/3s
              ELSE 
                LET TP2 == BC!PowerOfSet(sheader[1].VP, DOMAIN sheader[1].VP)
                    SP2 == BC!PowerOfSet(sheader[1].VP, sheader[2])
                IN  \* general case 
                verdict' = (3 * SP > TP) /\ (3 * SP2 > 2 * TP2)

DoCheck ==
  \* modeling feature, do not start the client before the blockchain is constructed
  /\ ~finished /\ height > TO_VERIFY_HEIGHT
  /\ finished' = TRUE
  /\ CheckSupport(TRUSTED_HEIGHT, TO_VERIFY_HEIGHT)

LCInit ==
  /\ finished = FALSE
  /\ verdict = FALSE
  /\ checkedHeader = <<blockchain[1], {}>> \* dummy value

LCNext ==
  DoCheck
            
            
(************************* Lite client + Blockchain ************************)
Init == BC!Init /\ LCInit

Next ==
  \/ LCNext /\ UNCHANGED bcvars
  \/ BC!Next /\ UNCHANGED lcvars 


(* The properties to check *)

Correctness == verdict = TRUE => checkedHeader[1] = blockchain[TO_VERIFY_HEIGHT]

=============================================================================
\* Modification History
\* Last modified Thu Oct 17 12:34:21 CEST 2019 by igor
\* Created Wed Oct 02 16:39:42 CEST 2019 by igor
