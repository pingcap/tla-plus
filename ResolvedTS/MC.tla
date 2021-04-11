---- MODULE MC ----
EXTENDS ResolvedTS, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
k1, k2
----

\* MV CONSTANT definitions RM
const_1571478437097222000 ==
{k1, k2}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1571478437097223000 ==
/\ nextTS < 106
----
=============================================================================
\* Modification History
\* Created Sat Oct 19 17:47:17 CST 2019 by neil
