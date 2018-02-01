------------------------------- MODULE Percolator ------------------------------

EXTENDS Integers, FiniteSets, Sequences, TLAPS

\* The set of transaction keys.
CONSTANTS KEY

AXIOM KeyNotEmpty == KEY # {} \* Keys cannot be empty.

\* The set of clients to execute a transaction.
CONSTANTS CLIENT

\* $next_ts$ is the timestamp for transaction. It is increased monotonically,
\* so every transaction must have a unique start and commit ts.
VARIABLES next_ts

\* $client_state[c]$ is the state of client.
VARIABLES client_state

\* $client_ts[c]$ is a record of [start_ts: ts, commit_ts: ts].
VARIABLES client_ts

\* $client_key[c]$ is a record of [primary: key, secondary: {key},
\* pending: {key}]. Hereby, "pending" denotes the keys that are pending for
\* prewrite.
VARIABLES client_key

\* $key_data[k]$ is the set of multi-version data timestamp of the key.
\* Only start_ts.
VARIABLES key_data

\* $key_lock[k]$ is the set of lock. A lock is of a record
\* [ts: ts, primary: lock]. $ts$ is for start_ts. If $primary$ equals to $k$,
\* it is a primary lock, otherwise secondary lock.
VARIABLES key_lock

\* $key_write[k]$ is a sequence of committed version of the key.
\* A committed version of the key is a record of [start_ts: ts, commit_ts: ts].
VARIABLES key_write

\* Two auxiliary variables for verifying snapshot isolation invariant.
\* $key_last_read_ts[k]$ denotes the last read timestamp for key $k$, this
\* should be monotonic.
\* $key_SI[k]$ denotes the if the snapshot isolation invariant is preserved for
\* key $k$ so far.
VARIABLES key_last_read_ts, key_SI

client_vars == <<client_state, client_ts, client_key>>
key_vars == <<key_data, key_lock, key_write, key_last_read_ts, key_SI>>
vars == <<next_ts, client_vars, key_vars>>

--------------------------------------------------------------------------------
\* Checks whether there is a lock of key $k$, whose $ts$ is less or equal than
\* $ts$.
hasLockLE(k, ts) ==
  \E l \in key_lock[k] : l.ts <= ts

\* Checks whether there is a lock of key $k$ with $ts$.
hasLockEQ(k, ts) ==
  \E l \in key_lock[k] : l.ts = ts

\* Returns TRUE if a lock can be cleanup up.
\* A lock can be cleaned up iff its ts is less than or equal to $ts$.
isStaleLock(k, l, ts) ==
  l.ts <= ts

\* Returns TRUE if we have a stale lock for key $k$.
hasStaleLock(k, ts) ==
  \E l \in key_lock[k] : isStaleLock(k, l, ts)

\* Returns the writes with start_ts equals to $ts$.
findWriteWithStartTS(k, ts) ==
  {key_write[k][w] : w \in {w \in DOMAIN key_write[k] : key_write[k][w].start_ts = ts}}

\* Returns the writes with commit_ts equals to $ts$.
findWriteWithCommitTS(k, ts) ==
  {key_write[k][w] : w \in {w \in DOMAIN key_write[k] : key_write[k][w].commit_ts = ts}}

\* Updates $key_SI$ for key $k$. If a new version of key $k$ is committed with
\* $commit_ts$ < last read timestamp, consider the snapshot isolation invariant
\* for key $k$ has been violated.
checkSnapshotIsolation(k, commit_ts) ==
  IF key_last_read_ts[k] >= commit_ts
  THEN
    key_SI' = [key_SI EXCEPT ![k] = FALSE]
  ELSE
    UNCHANGED <<key_SI>>

\* Cleans up a stale lock and its data.
\* If the lock is a secondary lock, and the assoicated primary lock is cleaned
\* up, we can clean up the lock and do,
\*   1. If the primary key is committed, we must also commit the secondary key.
\*   2. Otherwise, clean up the stale data too.
cleanupStaleLock(k, ts) ==
  \E l \in key_lock[k] :
    /\ isStaleLock(k, l, ts)
    /\ UNCHANGED <<key_last_read_ts, key_SI>>
    /\ \/ /\ l.primary = k  \* this is a primary key, always rollback
                            \* because it is not committed.
          /\ key_data' = [key_data EXCEPT ![k] = @ \ {l.ts}]
          /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
          /\ UNCHANGED <<key_write>>
       \/ /\ l.primary # k  \* this is a secondary key.
          /\ LET
                ws == findWriteWithStartTS(l.primary, l.ts)
              IN
                IF ws = {}
                THEN
                  \* the primary key is not committed, clean up the data.
                  \* Note we should always clean up the corresponding primary
                  \* lock first, then this secondary lock.
                  IF hasLockEQ(l.primary, l.ts)
                  THEN
                    /\ key_data' = [key_data EXCEPT ![l.primary] = @ \ {l.ts}]
                    /\ key_lock' = [key_lock EXCEPT ![l.primary] = @ \ {l}]
                    /\ UNCHANGED <<key_write>>
                  ELSE
                    /\ key_data' = [key_data EXCEPT ![k] = @ \ {l.ts}]
                    /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                    /\ UNCHANGED <<key_write>>
                ELSE
                  \* the primary key is committed, commit the secondary key.
                  \E w \in ws :
                    /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                    /\ key_write' = [key_write EXCEPT ![k] = Append(@, w)]
                    /\ checkSnapshotIsolation(k, w.commit_ts)
                    /\ UNCHANGED <<key_data>>

\* Cleans up a stale lock when the client encounters one.
cleanup(c) ==
  LET
    start_ts == client_ts[c].start_ts
    primary == client_key[c].primary
    secondary == client_key[c].secondary
  IN
    \/ /\ hasStaleLock(primary, start_ts)
       /\ cleanupStaleLock(primary, start_ts)
    \/ \E k \in secondary :
         /\ hasStaleLock(k, start_ts)
         /\ cleanupStaleLock(k, start_ts)

\* Reads one key if there is no stale lock, and updates last read timestamp.
readKey(c) ==
  LET
    start_ts == client_ts[c].start_ts
    primary == client_key[c].primary
    secondary == client_key[c].secondary
  IN
    \E k \in {primary} \union secondary :
      /\ ~hasStaleLock(k, start_ts)
      /\ key_last_read_ts[k] < start_ts
      /\ key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = start_ts]
      /\ UNCHANGED <<key_data, key_lock, key_write, key_SI>>

\* Returns TRUE if there is no lock for key $k$, and no any newer write than
\* $ts$.
canLockKey(k, ts) ==
  LET
    writes == {w \in DOMAIN key_write[k] : key_write[k][w].commit_ts >= ts}
  IN
    /\ key_lock[k] = {}  \* no any lock for the key.
    /\ writes = {}       \* no any newer write.

\* Locks the key and places the data.
lockKey(k, start_ts, primary) ==
  /\ key_lock' = [key_lock EXCEPT ![k] = @ \union {[ts |-> start_ts, primary |-> primary]}]
  /\ key_data' = [key_data EXCEPT ![k] = @ \union {start_ts}]
  /\ UNCHANGED <<key_write, key_last_read_ts, key_SI>>

\* Tries to lock primary key first, then the secondary key.
lock(c) ==
  LET
    start_ts == client_ts[c].start_ts
    primary == client_key[c].primary
    secondary == client_key[c].secondary
    pending == client_key[c].pending
  IN
    IF primary \in pending
    THEN  \* primary key is not locked, lock it first.
      /\ canLockKey(primary, start_ts)
      /\ lockKey(primary, start_ts, primary)
      /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {primary}]
      /\ UNCHANGED <<client_state, client_ts>>
    ELSE  \* primary key has already been locked, choose a secondary key to lock.
      \E k \in pending :
        /\ canLockKey(k, start_ts)
        /\ lockKey(k, start_ts, primary)
        /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
        /\ UNCHANGED <<client_state, client_ts>>

\* Commits the primary key.
commitPrimary(c) ==
  LET
    start_ts == client_ts[c].start_ts
    commit_ts == client_ts[c].commit_ts
    primary == client_key[c].primary
  IN
    /\ hasLockEQ(primary, start_ts)
    /\ key_lock' = [key_lock EXCEPT ![primary] = @ \ {[ts |-> start_ts, primary |-> primary]}]
    /\ key_write' = [key_write EXCEPT ![primary] = Append(@, client_ts[c])]
    /\ checkSnapshotIsolation(primary, commit_ts)
    /\ UNCHANGED <<key_data, key_last_read_ts>>

\* Assigns $start_ts$ to the transaction.
Start(c) ==
  /\ client_state[c] = "init"
  /\ next_ts' = next_ts + 1
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts']
  /\ UNCHANGED <<key_vars, client_key>>

\* Advances to prewrite phase, or tries to clean up one stale lock if we are
\* going to read the corresponding key.
Get(c) ==
  /\ client_state[c] = "working"
  /\ \/ /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
        /\ UNCHANGED <<next_ts, key_vars, client_ts, client_key>>
     \/ /\ cleanup(c)
        /\ UNCHANGED <<next_ts, client_vars>>
     \/ /\ readKey(c)
        /\ UNCHANGED <<next_ts, client_vars>>

\* Enters commit phase if all locks are granted, otherwise tries to lock the
\* primary lock and secondary locks.
Prewrite(c) ==
  /\ client_state[c] = "prewriting"
  /\ IF client_key[c].pending = {}
       THEN  \* all keys have been pre-written
         /\ next_ts' = next_ts + 1
         /\ client_state' = [client_state EXCEPT ![c] = "committing"]
         /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts']
         /\ UNCHANGED <<key_vars, client_key>>
       ELSE
         /\ lock(c)
         /\ UNCHANGED <<next_ts>>

\* If we commit the primary key successfully, we can think the transaction is
\* committed.
Commit(c) ==
  /\ client_state[c] = "committing"
  /\ commitPrimary(c)
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ UNCHANGED <<next_ts, client_ts, client_key>>

\* We can choose to abort at any time if not committed. Hereby, the aborted
\* state unifies client crash, client abort and transaction failure. The client
\* simply halts when aborted, and leaves cleanup to future transaction.
Abort(c) ==
  /\ client_state[c] # "committed"
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

ClientOp(c) ==
  \/ Start(c)
  \/ Get(c)
  \/ Prewrite(c)
  \/ Commit(c)
  \/ Abort(c)

Next == \E c \in CLIENT : ClientOp(c)

Init ==
  LET
    \* Selects a primary key and use the rest for the secondary keys.
    chooseKey(ks) ==
    LET
      primary == CHOOSE k \in ks : TRUE
    IN
      [primary |-> primary,
       secondary |-> ks \ {primary},
       pending |-> ks]
  IN
    /\ next_ts = 0
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |-> chooseKey(KEY)]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_data = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> <<>>]
    /\ key_last_read_ts = [k \in KEY |-> 0]
    /\ key_SI = [k \in KEY |-> TRUE]

PercolatorSpec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
NextTsTypeInv ==
  next_ts \in Nat

ClientStateTypeInv ==
  client_state \in [CLIENT -> {"init", "working", "prewriting",
                               "committing", "committed", "aborted"}]

ClientTsTypeInv ==
  client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]

ClientKeyTypeInv ==
  client_key \in [CLIENT -> [primary : KEY,
                             secondary : SUBSET KEY,
                             pending : SUBSET KEY]]

KeyDataTypeInv ==
  key_data \in [KEY -> SUBSET Nat]

KeyLockTypeInv ==
  key_lock \in [KEY -> SUBSET [ts : Nat, primary : KEY]]

KeyWriteTypeInv ==
  key_write \in [KEY -> Seq([start_ts : Nat, commit_ts : Nat])]

TypeInvariant ==
  /\ NextTsTypeInv
  /\ ClientStateTypeInv
  /\ ClientTsTypeInv
  /\ ClientKeyTypeInv
  /\ KeyDataTypeInv
  /\ KeyLockTypeInv
  /\ KeyWriteTypeInv

--------------------------------------------------------------------------------
\* The committed write timestamp of one key must be in order, and no two writes
\* can overlap. For each write, the commit_ts should be strictly greater than
\* start_ts.
WriteConsistency ==
  /\ \A k \in KEY :
       \A n \in 1..Len(key_write[k]) - 1 :
         key_write[k][n].commit_ts < key_write[k][n + 1].start_ts
  /\ \A k \in KEY :
       \A n \in 1..Len(key_write[k]) :
         key_write[k][n].start_ts < key_write[k][n].commit_ts

LockConsistency ==
  \* There should be at most one lock for each key.
  /\ \A k \in KEY :
       Cardinality(key_lock[k]) <= 1
  \* When the client finishes prewriting and is ready for commit, if the
  \* primary lock exists, all secondary locks should exist.
  /\ \A c \in CLIENT :
       (/\ client_state[c] = "committing"
        /\ hasLockEQ(client_key[c].primary, client_ts[c].start_ts)
       ) =>
         \A k \in client_key[c].secondary :
           hasLockEQ(k, client_ts[c].start_ts)

CommittedConsistency ==
  \A c \in CLIENT :
    LET
      start_ts == client_ts[c].start_ts
      commit_ts == client_ts[c].commit_ts
      primary == client_key[c].primary
      secondary == client_key[c].secondary
      w == [start_ts |-> start_ts, commit_ts |-> commit_ts]
    IN
      client_state[c] = "committed" =>
        \* The primary key lock must be cleaned up, and no any older lock.
        /\ ~hasLockLE(primary, start_ts)
        /\ findWriteWithCommitTS(primary, commit_ts) = {w}
        /\ start_ts \in key_data[primary]
        /\ \A k \in secondary :
           \* The secondary key lock can be empty or not.
           /\ \/ /\ ~hasLockEQ(k, start_ts)
                 /\ findWriteWithCommitTS(k, commit_ts) = {w}
                 /\ ~hasLockLE(k, start_ts - 1)
              \/ /\ hasLockEQ(k, start_ts)
                 /\ findWriteWithCommitTS(k, commit_ts) = {}
                 /\ (Len(key_write[k]) > 0 =>
                      \* Lock has not been cleaned up, so the last write
                      \* committed timestamp must be less than lock start_ts.
                      key_write[k][Len(key_write[k])].commit_ts < start_ts)
           /\ start_ts \in key_data[k]

\* If one transaction is aborted, there should be no committed primary key.
AbortedConsistency ==
  \A c \in CLIENT :
    (/\ client_state[c] = "aborted"
     /\ client_ts[c].commit_ts # 0
    ) =>
      findWriteWithCommitTS(client_key[c].primary, client_ts[c].commit_ts) = {}

\* Snapshot isolation invariant should be preserved.
SnapshotIsolation ==
  \A k \in KEY :
    key_SI[k] = TRUE

--------------------------------------------------------------------------------
\* TLAPS proof for proving Spec keeps type invariant.
LEMMA InitStateSatisfiesTypeInvariant ==
  Init => TypeInvariant
PROOF
<1> USE DEF Init, TypeInvariant
<1> USE DEF NextTsTypeInv, ClientStateTypeInv, ClientTsTypeInv, ClientKeyTypeInv,
            KeyDataTypeInv, KeyLockTypeInv, KeyWriteTypeInv
<1> QED BY SMT, KeyNotEmpty

LEMMA findWriteWithStartTSTypeInv ==
  ASSUME key_write \in [KEY -> Seq([start_ts: Nat, commit_ts: Nat])],
         NEW k \in KEY,
         NEW ts \in Nat
  PROVE findWriteWithStartTS(k, ts) \in SUBSET [start_ts : Nat, commit_ts : Nat]
PROOF
<1> DEFINE ws == key_write[k]
<1> DEFINE Type == [start_ts : Nat, commit_ts : Nat]
<1>a ws = key_write[k] OBVIOUS
<1>b Type = [start_ts : Nat, commit_ts : Nat] OBVIOUS
<1>c ws \in Seq(Type) BY DEF KeyWriteTypeInv
<1> HIDE DEF ws, Type
<1>d SUFFICES ASSUME NEW w \in DOMAIN ws
     PROVE ws[w] \in Type
     BY DEF findWriteWithStartTS, ws, Type
<1> QED BY Z3, <1>c

LEMMA NextKeepsTypeInvariant ==
  TypeInvariant /\ Next => TypeInvariant'
PROOF
<1> SUFFICES ASSUME TypeInvariant, Next PROVE TypeInvariant' OBVIOUS
<1> USE DEF TypeInvariant
<1> USE DEF client_vars, key_vars
<1> PICK c \in CLIENT : ClientOp(c) BY DEF Next
<1>a CASE Start(c)
  <2> USE DEF Start
  <2> USE DEF NextTsTypeInv, ClientStateTypeInv, ClientTsTypeInv, ClientKeyTypeInv,
              KeyDataTypeInv, KeyLockTypeInv, KeyWriteTypeInv
  <2> QED BY <1>a
<1>b CASE Get(c)
  <2> USE DEF Get, cleanup, readKey
  <2>a NextTsTypeInv'
       BY <1>b DEF NextTsTypeInv
  <2>b ClientStateTypeInv'
       BY <1>b DEF ClientStateTypeInv
  <2>c ClientTsTypeInv'
       BY <1>b DEF ClientTsTypeInv
  <2>d ClientKeyTypeInv'
       BY <1>b DEF ClientKeyTypeInv
  <2>e KeyDataTypeInv'
       BY <1>b DEF KeyDataTypeInv, cleanupStaleLock
  <2>f KeyLockTypeInv'
       BY <1>b DEF KeyLockTypeInv, cleanupStaleLock
  <2>g KeyWriteTypeInv'
    <3>a ASSUME NEW k1 \in KEY,
                NEW ts1 \in Nat,
                cleanupStaleLock(k1, ts1)
         PROVE KeyWriteTypeInv'
         BY <3>a, findWriteWithStartTSTypeInv
         DEF ClientTsTypeInv, ClientKeyTypeInv, KeyWriteTypeInv,
             KeyLockTypeInv, KeyDataTypeInv, cleanupStaleLock
    <3> QED BY <1>b, <3>a DEF KeyWriteTypeInv, ClientKeyTypeInv, ClientTsTypeInv
  <2> QED BY <2>a, <2>b, <2>c, <2>d, <2>e, <2>f, <2>g
<1>c CASE Prewrite(c)
  <2> USE DEF Prewrite, lock, lockKey
  <2>a NextTsTypeInv'
    <3>a \/ next_ts' = next_ts + 1
         \/ UNCHANGED <<next_ts>>
         BY <1>c DEF NextTsTypeInv
    <3> QED BY <3>a DEF NextTsTypeInv
  <2>b ClientStateTypeInv'
       BY <1>c DEF ClientStateTypeInv
  <2>c ClientTsTypeInv'
       BY <1>c, <2>a DEF ClientTsTypeInv, NextTsTypeInv
  <2>d ClientKeyTypeInv'
    <3>a CASE client_key[c].pending = {}
         BY <1>c, <3>a DEF ClientKeyTypeInv
    <3>b CASE client_key[c].pending # {}
      <4>a \E k \in KEY :
             client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
           BY <1>c, <3>b DEF ClientKeyTypeInv
      <4>b PICK k \in KEY : client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
           BY <4>a
      <4> QED BY <4>b DEF ClientKeyTypeInv
    <3> QED BY <3>a, <3>b
  <2>e KeyDataTypeInv'
    <3>a CASE client_key[c].pending = {}
         BY <1>c, <3>a DEF KeyDataTypeInv
    <3>b CASE client_key[c].pending # {}
      <4>a \E k \in KEY : \E ts \in Nat :
             key_data' = [key_data EXCEPT ![k] = @ \cup {ts}]
           BY <1>c, <3>b DEF KeyDataTypeInv, ClientKeyTypeInv, ClientTsTypeInv
      <4> QED BY <4>a DEF KeyDataTypeInv
    <3> QED BY <3>a, <3>b
  <2>f KeyLockTypeInv'
    <3>a CASE client_key[c].pending = {}
         BY <1>c, <3>a DEF KeyLockTypeInv
    <3>b CASE client_key[c].pending # {}
      <4>a \E k \in KEY : \E l \in [ts : Nat, primary : KEY] :
             key_lock' = [key_lock EXCEPT ![k] = @ \cup {l}]
           BY <1>c, <3>b DEF KeyLockTypeInv, ClientKeyTypeInv, ClientTsTypeInv
      <4> QED BY <4>a DEF KeyLockTypeInv
    <3> QED BY <3>a, <3>b
  <2>g KeyWriteTypeInv'
       BY <1>c DEF KeyWriteTypeInv
  <2> QED BY <2>a, <2>b, <2>c, <2>d, <2>e, <2>f, <2>g
<1>d CASE Commit(c)
  <2> USE DEF Commit, commitPrimary, lock, lockKey
  <2> USE DEF NextTsTypeInv, ClientStateTypeInv, ClientTsTypeInv, ClientKeyTypeInv,
              KeyDataTypeInv, KeyLockTypeInv, KeyWriteTypeInv
  <2> QED BY <1>d
<1>e CASE Abort(c)
  <2> USE DEF Abort
  <2> USE DEF NextTsTypeInv, ClientStateTypeInv, ClientTsTypeInv, ClientKeyTypeInv,
              KeyDataTypeInv, KeyLockTypeInv, KeyWriteTypeInv
  <2> QED BY <1>e
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e DEF ClientOp

THEOREM TypeSafety ==
  PercolatorSpec => []TypeInvariant
PROOF
<1> SUFFICES ASSUME Init /\ [][Next]_vars PROVE []TypeInvariant
    BY DEF PercolatorSpec
<1> QED BY InitStateSatisfiesTypeInvariant, NextKeepsTypeInvariant, PTL

THEOREM Safety ==
  PercolatorSpec => [](/\ TypeInvariant
                       /\ WriteConsistency
                       /\ LockConsistency
                       /\ CommittedConsistency
                       /\ AbortedConsistency
                       /\ SnapshotIsolation)

================================================================================
