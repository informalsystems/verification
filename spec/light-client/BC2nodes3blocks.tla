---- MODULE BC2nodes3blocks ----
EXTENDS Blockchain, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A_p1, A_p2
----

\* MV CONSTANT definitions AllNodes
const_AllNodes == 
{A_p1, A_p2}
----

\* CONSTANT definitions @modelParameterConstants:0ULTIMATE_HEIGHT
const_ULTIMATE_HEIGHT == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MAX_POWER
const_MAX_POWER == 
1
----

=============================================================================
\* Modification History
\* Created Wed Nov 06 20:00:32 CET 2019 by igor
