--------------------------------- MODULE Test2 ---------------------------------
EXTENDS DistributedTransaction, TLC

CONSTANT k1, k2, k3
CONSTANT c1, c2, c3

Keys == {k1, k2, k3}
OptimistiicClient == {c3}
PessimisticClient == {c1, c2}
ClientReadKeys == c1 :> {} @@ c2 :> {} @@ c3 :> {k1, k3}
ClientWriteKeys == c1 :> {k1, k2, k3} @@ c2 :> {k1, k2} @@ c3 :> {k1, k3}
ClientPrimary == c1 :> k1 @@ c2 :> k1 @@ c3 :> k3
================================================================================
