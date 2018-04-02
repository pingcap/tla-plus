--------------------------------- MODULE Test1 ---------------------------------

EXTENDS ConcurrentPercolator, TLC

\* We use one table with 3 keys and 3 concurrent clients for TLC model checking.
\* These 3 clients have the same primary key, so they are considered symmetric.

CONSTANTS c1, c2, c3

Key == {1, 2, 3}
Client == {c1, c2, c3}
ClientPrimaryKey == c1 :> 1 @@ c2 :> 1 @@ c3 :> 1

Symmetry == Permutations(Client)

================================================================================
