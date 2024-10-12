# DM safe mode replication

DM checkpoint is a low watermark of multiple concurrent replication workers. When the replication task restarts from checkpoint, some DML changes will be executed more than once. In this case, DM will turn on "safe mode" to avoid SQL execution error, for example, use REPLACE INTO instead of INSERT INTO.

This model tests the "safe mode" replication will eventually have the same data in downstream as upstream even if DM restarts from a low watermark checkpoint. Specifically, the current implementation of DM has the following rules in "safe mode":

- use REPLACE INTO for INSERT DML
- use DELETE by PK + REPLACE for UPDATE DML
- use DELETE by PK for DELETE DML

And we use TLA+ to check that these rules are also correct:

- use INSERT IGNORE INTO for INSERT DML
- use DELETE by PK + INSERT IGNORE INTO for UPDATE DML
- use DELETE by PK for DELETE DML
