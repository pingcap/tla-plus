---- MODULE MC ----
EXTENDS WriteAndVerify, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
Alice, Bob
----

\* MV CONSTANT definitions CLIENTS
const_172889209848054000 == 
{Alice, Bob}
----

\* SYMMETRY definition
symm_172889209848055000 == 
Permutations(const_172889209848054000)
----

\* CONSTANT definitions @modelParameterConstants:1WITH_CRASHING
const_172889209848056000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:2WITH_RO
const_172889209848057000 == 
FALSE
----

=============================================================================
\* Modification History
\* Created Mon Oct 14 15:48:18 CST 2024 by Hillium

