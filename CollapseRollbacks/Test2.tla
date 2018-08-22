--------------------------------- MODULE Test2 ---------------------------------

EXTENDS CollapseRollbacks, TLC

\* We use one table with 2 keys and 2 concurrent clients for TLC model checking.
\* These 2 clients have primary key 1 and 2 respectively.

CONSTANTS c1, c2

Key == {1, 2}
Client == {c1, c2}
ClientPrimaryKey == c1 :> 1 @@ c2 :> 2

================================================================================
