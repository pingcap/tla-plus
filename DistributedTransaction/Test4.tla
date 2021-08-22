--------------------------------- MODULE Test3 ---------------------------------
EXTENDS DistributedTransaction, TLC

CONSTANT k1
CONSTANT c1, c2

Keys == {k1}
OptimistiicClient == {c2}
PessimisticClient == {c1}
ClientReadKeys == c1 :> {} @@ c2 :> {k1}
ClientWriteKeys == c1 :> {k1} @@ c2 :> {k1}
ClientPrimary == c1 :> k1 @@ c2 :> k1
================================================================================
