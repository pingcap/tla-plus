--------------------------------- MODULE Test1 ---------------------------------

EXTENDS PessimisticTransaction, TLC

\* Model value is not used to avoid unnecessary state space 
\* checked by TLC. Symmetry should not be used if we are supposed
\* to check liveness.
k1 == 1
k2 == 2
c1 == 1
c2 == 2

Key == {k1, k2}
OptimistiicClient == {}
PessimisticClient == {c1, c2}
ClientKey == c1 :> {k1, k2} @@ c2 :> {k2}
ClientPrimary == c1 :> k1 @@ c2 :> k2

================================================================================
