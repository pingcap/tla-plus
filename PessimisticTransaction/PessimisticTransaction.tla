----------------------- MODULE PessimisticTransaction -----------------------

EXTENDS Integers, FiniteSets, TLC

\* The set of transaction keys.
CONSTANTS KEY
ASSUME KEY # {} \* Keys cannot be empty.

\* The set of clients to execute a transaction.
CONSTANTS CLIENT

\* CLIENT_KEY is a set of [c -> SUBSET KEY],
\* representing involved keys of each client
CONSTANTS CLIENT_KEY

ASSUME \A c \in CLIENT: CLIENT_KEY[c] \subseteq CLIENT_KEY[c]

CONSTANTS CLIENT_PRIMARY

ASSUME \A c \in CLIENT: CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

\* The set of pessimistic clients
CONSTANTS PESSIMISTIC_CLIENT

ASSUME PESSIMISTIC_CLIENT \subseteq CLIENT

\* The set of optimistic clients
CONSTANTS OPTIMISTIC_CLIENT

ASSUME OPTIMISTIC_CLIENT \subseteq CLIENT

\* next_ts is the timestamp for transaction. It is increased monotonically,
\* so every transaction must have a unique start and commit ts.
VARIABLES next_ts

\* client_state[c] is the state of client.
VARIABLES client_state

\* client_ts[c] is a record of [start_ts, for_update_ts, commit_ts].
VARIABLES client_ts

\* client_key[c] is a record of [primary: key, secondary: {key},
\* pessimistic: {key}, pending: {key}]. Hereby, "pessimistic" denotes
\* the keys whose pessimistic locks haven't been acquired, "pending"
\* denotes the keys that are pending for prewrite.
VARIABLES client_key

\* key_data[k] is the set of multi-version data of the key.
\* Since we don't care about the concrete value of data, a record of
\* [ts: start_ts] is sufficient to represent one data version.
VARIABLES key_data

\* key_lock[k] is the set of lock. A lock is of a record of [ts: start_ts,
\* for_update_ts, primary: key]. If primary equals to k, it is a primary
\* lock, otherwise secondary lock. If for_update_ts > 0, it belongs to a
\* pessimistic transaction.
VARIABLES key_lock

\* key_write[k] is a sequence of committed version of the key.
\* A committed version of the key is a record of [ts, type, start_ts].
\* type can be "write" or "rollback" depending on record type. start_ts
\* field only exists if type is "write". For "write" record, ts denotes
\* commit_ts; for "rollback" record, $ts$ denotes start_ts.
VARIABLES key_write

\* key_last_read_ts is for verifying snapshot isolation invariant. It should
\* not appear in a real-world implementation.
\*
\* key_last_read_ts[k] denotes the last read timestamp for key k.
\* The commit_ts of a successful commit should greater then the last read_ts.
VARIABLES key_last_read_ts

\* The set of all messages sent by clients. To simulate message resending,
\* client messages are inserted into the set and never deleted. The server can
\* pick any message in the set to execute.
VARIABLES msg

client_vars == <<client_state, client_ts, client_key>>
key_vars == <<key_data, key_lock, key_write, key_last_read_ts>>
vars == <<next_ts, client_vars, key_vars, msg>>

-----------------------------------------------------------------------------

Pos == {x \in Nat : x > 0}

-----------------------------------------------------------------------------

\* Find a stale lock which blocks the read for key k.
findStaleLock(k, ts) ==
  {l \in key_lock[k] : l.pessimistic = FALSE /\ l.ts < ts}
  
\* Get the write records of k before or at timestamp ts
historyWrites(k, ts) ==
  {w \in key_write[k] : w.ts <= ts}

\* Get the set of the latest write record of k before or at timestamp ts
latestHistoryWrite(k, ts) ==
  {w \in historyWrites(k, ts) :
    \A w2 \in historyWrites(k, ts) : w.ts >= w2.ts}
  
\* Rollback key k in the transaction starting at ts
rollback(k, ts) ==
  \* If the existing lock has the same ts, unlock it.
  /\ IF \E l \in key_lock[k] : l.ts = ts
     THEN key_lock' = [key_lock EXCEPT ![k] = {}]
     ELSE UNCHANGED key_lock
  /\ key_data' = [key_data EXCEPT ![k] = @ \ {[ts |-> ts]}]
  \* Write a rollback in the write column.
  /\ key_write' = [key_write EXCEPT
       ![k] = (@ \ {w \in latestHistoryWrite(k, ts) : w.type = "rollback"}) \* collapse rollback
                 \union {[ts |-> ts, type |-> "rollback", start_ts |-> ts]}]
       

\* Commit key k       
commit(k, start_ts, commit_ts) ==
  /\ IF \E l \in key_lock[k] : l.ts = start_ts
     THEN
       \* Write the write column and unlock the lock iff the lock exists
       /\ key_lock' = [key_lock EXCEPT ![k] = {}]
       /\ key_write' = [key_write EXCEPT ![k] = @ \union {[ts |-> commit_ts, type |-> "write", start_ts |-> start_ts]}]
       \* Assert we don't violate snapshot isolation
       /\ Assert(key_last_read_ts[k] < commit_ts, <<key_last_read_ts[k], commit_ts>>)
     ELSE
       UNCHANGED <<key_lock, key_write>>
  /\ UNCHANGED key_data

\* Change the state of client c to aborted
abortTxn(c) ==
  /\ ~ client_state[c] \in {"committed", "undetermined"}
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]

\* Change the state of client c to undetermined due to lost commit RPC.
undetermine(c) ==
  /\ client_state[c] = "committing"
  /\ client_state' = [client_state EXCEPT ![c] = "undetermined"]
  
-----------------------------------------------------------------------------

StartPessimistic(c) ==
  /\ client_state[c] = "init"
  /\ next_ts' = next_ts + 1
  /\ client_key' =
         [client_key EXCEPT
           ![c] = [primary |-> CLIENT_PRIMARY[c],
                   secondary |-> CLIENT_KEY[c] \ {CLIENT_PRIMARY[c]},
                   pessimistic |-> CLIENT_KEY[c], \* Assume we need to acquire pessimistic locks for all keys
                   pending |-> CLIENT_KEY[c]]]
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  \* The for_update_ts is initialized to be the same as start_ts.
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts', ![c].for_update_ts = next_ts']
  /\ UNCHANGED <<key_vars, msg>>
         
LockKey(c) ==
  /\ client_state[c] = "working"
  /\ IF client_key[c].pessimistic = {}
     THEN
       \* The client can prewrite after all pessimistic locks have been acquired.
       /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
       /\ UNCHANGED <<client_ts, client_key, next_ts, key_vars, msg>>
     ELSE
       \* Select any unlocked key and acquire its pessimistic lock
       \E k \in client_key[c].pessimistic :
         /\ msg' = msg \union 
              {[c |-> c, type |-> "lock", key |-> k, primary |-> client_key[c].primary,
               start_ts |-> client_ts[c].start_ts, for_update_ts |-> client_ts[c].for_update_ts]}
         /\ UNCHANGED <<next_ts, client_vars, key_vars>>
       
PessimisticPrewrite(c) ==
  /\ client_state[c] = "prewriting"
  /\ IF client_key[c].pending = {}
     THEN
       \* The client can commit the primary key after prewriting all keys.
       /\ client_state' = [client_state EXCEPT ![c] = "committing"]
       /\ UNCHANGED <<client_ts, client_key, next_ts, key_vars, msg>>
     ELSE
       \* Select any pending key to prewrite
       \E k \in client_key[c].pending :
         /\ msg' = msg \union 
              {[c |-> c, type |-> "prewrite", key |-> k, primary |-> client_key[c].primary,
               start_ts |-> client_ts[c].start_ts, for_update_ts |-> client_ts[c].for_update_ts]}
         /\ UNCHANGED <<next_ts, client_vars, key_vars>>
         
Commit(c) ==
  /\ client_state[c] = "committing"
  \* Get a new ts as commit_ts
  /\ IF client_ts[c].commit_ts = 0
     THEN
       /\ next_ts' = next_ts + 1
       /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts']
     ELSE
       UNCHANGED <<next_ts, client_ts>>
  \* Commit the primary key
  /\ msg' = msg \union
       {[c |-> c, type |-> "commit", key |-> client_key[c].primary,
         start_ts |-> client_ts[c].start_ts, commit_ts |-> client_ts'[c].commit_ts]}
  /\ UNCHANGED <<client_state, client_key, key_vars>>
  
         
PessimisticClientOp(c) ==
  \/ StartPessimistic(c)
  \/ LockKey(c)
  \/ PessimisticPrewrite(c)
  \/ Commit(c)
  \* Committing secondary keys is ommitted
  
DoRead ==
  \E cmd \in msg :
    /\ cmd.type = "read"
    /\ LET
         k == cmd.key
         ts == cmd.ts
       IN
         LET
           stale_lock == findStaleLock(k, ts)
         IN
           IF stale_lock = {}
           \* Successfully read
           THEN
             \* The client receives the read response, update the last read ts
             /\ IF key_last_read_ts[k] < ts
                THEN key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = ts]
                ELSE UNCHANGED key_last_read_ts
             \* To simulate the client fails to receive the read response
             /\ UNCHANGED <<client_vars, key_data, key_lock, key_write, next_ts, msg>>
           ELSE
             \* When there is a blocking lock, the client may resolve the lock by cleanup.
             /\ msg' = msg \union
                  {[type |-> "cleanup", primary |-> l.primary, start_ts |-> l.ts] : l \in stale_lock}
             /\ UNCHANGED <<client_state, client_ts, client_key, key_vars, next_ts>>
             \* Response loss leads to no state change
        
DoCleanup ==
  \E cmd \in msg :
   /\ cmd.type = "cleanup"
   /\ LET
        k == cmd.primary
        ts == cmd.start_ts
      IN
        LET
          lock == {l \in key_lock[k] : l.ts = ts}
          committed == {w \in key_write[k] : w.start_ts = ts /\ w.type = "write"}
        IN
          IF committed # {}
          \* The transaction is already committed, so resolve locks using its commit_ts
          THEN
            /\ msg' = msg \union
                 {[type |-> "resolve", primary |-> k, start_ts |-> ts, commit_ts |-> t.ts] : t \in committed}
            /\ UNCHANGED <<next_ts, client_vars, key_vars>>
          ELSE
            \* The transaction is not committed, so rollback the primary key.
            /\ rollback(k, ts)
            /\ UNCHANGED <<key_last_read_ts, next_ts, client_vars>>
            \* The client may resolve locks using 0 as commit_ts. When the cleanup response is lost,
            \* msg remains unchanged.
            /\ \/ msg' = msg \union
                    {[type |-> "resolve", primary |-> k, start_ts |-> ts, commit_ts |-> 0]}
               \/ UNCHANGED msg

DoResolve ==
  \E cmd \in msg :
    /\ cmd.type = "resolve"
    /\ IF cmd.commit_ts = 0
       THEN
         \* rollback locks when commit_ts = 0
         \E k \in KEY :
           \E l \in key_lock[k] :
             /\ l.primary = cmd.primary
             /\ l.ts = cmd.start_ts
             /\ rollback(k, cmd.start_ts)
       ELSE
         \* commit locks when commit_ts > 0
         \E k \in KEY :
           \E l \in key_lock[k] :
             /\ l.primary = cmd.primary
             /\ l.ts = cmd.start_ts
             /\ commit(k, cmd.start_ts, cmd.commit_ts)
    /\ UNCHANGED <<next_ts, client_vars, key_last_read_ts, msg>>    
          
\* This action is too complex and concrete. Maybe simplify it?
DoLockKey ==
  \E cmd \in msg :
   /\ cmd.type = "lock"
   /\ LET
        c == cmd.c
        k == cmd.key
        primary == cmd.primary
        ts == cmd.start_ts
        for_update_ts == cmd.for_update_ts
        \* Write or overwrite the pessimistic lock
        writeLock ==
              /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> ts, for_update_ts |-> for_update_ts, primary |-> primary, pessimistic |-> TRUE]}]
              /\ UNCHANGED <<client_state, client_ts, key_data, key_write, key_last_read_ts, next_ts, msg>>
              \* Inform the client that the key is locked
              /\ \/ client_key' = [client_key EXCEPT ![c].pessimistic = @ \ {k}]
                 \* client_key remains the same when the response is lost
                 \/ UNCHANGED client_key
        \* Update the for_update_ts in the client with new_ts
        updateForUpdateTs(new_ts) ==
          IF new_ts > client_ts[c].for_update_ts
          THEN
            /\ client_ts' = [client_ts EXCEPT ![c].for_update_ts = for_update_ts]
            /\ UNCHANGED <<client_state, client_key, next_ts, key_vars, msg>>
          ELSE UNCHANGED vars
      IN
        IF key_lock[k] = {}
        THEN
          IF key_write[k] = {}
          \* If no lock or write exists, we can always lock the key
          THEN writeLock
          ELSE
            LET
              \* Find the write record with biggest commit_ts
              latest == CHOOSE w \in key_write[k] : \A w2 \in key_write[k] : w.ts >= w2.ts
            IN
              IF latest.ts > for_update_ts
              \* Update the client's for_update_ts when there is a newer commit.
              \* Response loss causes no state change.
              THEN updateForUpdateTs(latest.ts)
              ELSE
                IF \E w \in key_write[k] : w.start_ts = ts /\ w.type = "rollback"
                \* If any key to be locked is rollbacked, abort the transaction.
                \* TODO: Maybe it needn't be included in the spec.
                THEN abortTxn(c) /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars, msg>>
                \* Otherwise we can lock the key.
                ELSE writeLock
        ELSE
          LET
            l == CHOOSE l \in key_lock[k] : TRUE
          IN
            IF l.ts # ts
            \* If there is a lock from another transaction, the client may cleanup the lock.
            \* Response loss causes no state change.
            THEN                        
              /\ msg' = msg \union
                   {[type |-> "cleanup", primary |-> l.primary, start_ts |-> l.ts]}
              /\ UNCHANGED <<client_state, client_ts, client_key, key_vars, next_ts>>
            ELSE
              \* Only overwrite the lock when it's a pessimistic lock with smaller for_update_ts
              /\ l.pessimistic
              /\ l.for_update_ts < for_update_ts
              /\ writeLock
      
DoPessimisticPrewrite ==
  \E cmd \in msg :
   /\ cmd.type = "prewrite"
   /\ cmd.for_update_ts > 0
   /\ LET
        c == cmd.c
        k == cmd.key
        primary == cmd.primary
        ts == cmd.start_ts
        for_update_ts == cmd.for_update_ts
      IN
        IF
          \/ key_lock[k] = {}
          \/ \E l \in key_lock[k] : l.ts # ts
        THEN
          \* Abort the transaction when its lock doesn't exist
          /\ abortTxn(c)
          /\ UNCHANGED <<client_ts, client_key, next_ts, key_vars, msg>>
        ELSE
          \* Otherwise rewrite the existing lock to an optimistic lock
          /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> ts, for_update_ts |-> for_update_ts, primary |-> primary, pessimistic |-> FALSE]}]
          /\ key_data' = [key_data EXCEPT ![k] = @ \union {[ts |-> ts]}]
          \* Inform the client that the key is successfully prewritten
          /\ \/ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
             \* Simulate response loss
             \/ UNCHANGED client_key
          /\ UNCHANGED <<client_state, client_ts, key_write, key_last_read_ts, next_ts, msg>>
      
DoCommit ==
  \E cmd \in msg :
   /\ cmd.type = "commit"
   /\ LET
        c == cmd.c
        k == cmd.key
        start_ts == cmd.start_ts
        commit_ts == cmd.commit_ts
      IN
        IF \/ \E l \in key_lock[k] : l.ts = start_ts
           \/ \E w \in key_write[k] : w.start_ts = start_ts /\ w.type = "write"
        \* Commit the key iff the prewritten key exists or it's a repeated commit
        THEN
          /\ commit(k, start_ts, commit_ts)
          \* Change client state to committed.
          /\ \/ client_state' = [client_state EXCEPT ![c] = "committed"]
             \* Commit response is lost
             \/ undetermine(c)
          /\ UNCHANGED <<client_ts, client_key, next_ts, key_last_read_ts, msg>>
        ELSE
          \* The lock doesn't exist and the key is not committed, so commit fails.
          /\ \/ /\ Assert(client_state[c] # "committed", client_state[c])
                /\ abortTxn(c)
             \* Commit response is lost
             \/ undetermine(c)
          /\ UNCHANGED <<client_ts, client_key, next_ts, key_vars, msg>>

ServerOp ==
  \/ DoRead
  \/ DoCleanup
  \/ DoResolve
  \/ DoLockKey
  \/ DoPessimisticPrewrite
  \/ DoCommit
 
Read ==
  \E ts \in 0..next_ts :
    \E k \in KEY :
      /\ msg' = msg \union {[type |-> "read", key |-> k, ts |-> next_ts]}
      /\ UNCHANGED <<next_ts, client_vars, key_vars>>

Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0,
                                      for_update_ts |-> 0,
                                      commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |-> {}]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_data = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> {}]
    /\ key_last_read_ts = [k \in KEY |-> 0]
    /\ msg = {}

Next == 
  \/ ServerOp
  \/ \E c \in PESSIMISTIC_CLIENT : PessimisticClientOp(c)
  \/ Read
  
PessimisticSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

NextTsTypeInv == next_ts \in Pos

ClientStateTypeInv ==
  client_state \in [
    CLIENT -> {"init", "working", "prewriting",
               "committing", "committed", "aborted", "undetermined"}
  ]

ClientTsTypeInv ==
  client_ts \in
  [CLIENT -> [start_ts : Nat, for_update_ts : Nat, commit_ts : Nat]]

ClientKeyTypeInv ==
  \A c \in CLIENT :
    \/ client_state[c] = "init"
    \/ client_key[c] \in [primary : KEY,
                          secondary : SUBSET KEY,
                          pessimistic : SUBSET KEY,
                          pending : SUBSET KEY]

KeyDataTypeInv ==
  key_data \in [KEY -> SUBSET [ts : Pos]]

KeyLockTypeInv ==
  key_lock \in [KEY -> SUBSET [ts : Pos, for_update_ts : Nat, primary : KEY, pessimistic : BOOLEAN]]

KeyWriteTypeInv ==
  key_write \in [KEY ->
    SUBSET [ts : Pos, type : {"write", "rollback"}, start_ts : Pos]
  ]

KeyLastReadTsTypeInv ==
  key_last_read_ts \in [KEY -> Nat]

MsgTypeInv ==
  msg \subseteq (
    [c : CLIENT, type : {"lock", "prewrite"}, key : KEY, primary: KEY,
     start_ts : Pos, for_update_ts : Pos] \union
    [c : CLIENT, type : {"commit"}, key : KEY, start_ts : Pos, commit_ts : Pos] \union
    [type : {"read"}, key : KEY, ts : Nat] \union
    [type : {"cleanup"}, primary : KEY, start_ts : Pos] \union
    [type : {"resolve"}, primary : KEY, start_ts : Pos, commit_ts : Nat]
  )

TypeInvariant ==
  /\ NextTsTypeInv
  /\ ClientStateTypeInv
  /\ ClientTsTypeInv
  /\ ClientKeyTypeInv
  /\ KeyDataTypeInv
  /\ KeyLockTypeInv
  /\ KeyWriteTypeInv
  /\ KeyLastReadTsTypeInv
  /\ MsgTypeInv
  
-----------------------------------------------------------------------------

\* For each write, the commit_ts should be strictly greater than
\* the start_ts. For each rollback, the commit_ts should equals to
\* the start_ts.
WriteConsistency ==
  \A k \in KEY:
    \A rec \in key_write[k] :
      \/ /\ rec.type = "write"
         /\ rec.ts > rec.start_ts
         /\ \E d \in key_data[k] : rec.start_ts = d.ts
      \/ /\ rec.type = "rollback"
         /\ rec.ts = rec.start_ts

LockConsistency ==
  \A k \in KEY :
    \* There should be at most one lock for each key.
    /\ Cardinality(key_lock[k]) <= 1
    \* When the lock exists, there cannot be a corresponding commit record
    /\ \A l \in key_lock[k] :
         ~ \E w \in key_write[k] : w.start_ts = l.ts

CommittedClientConsistency ==
  \A c \in CLIENT :
    LET
      start_ts == client_ts[c].start_ts
      commit_ts == client_ts[c].commit_ts
      primary == client_key[c].primary
    IN
      \* When the client considers it's committed, its primary key must be committed
      client_state[c] = "committed" =>
        \E w \in key_write[primary] :
          /\ w.start_ts = start_ts
          /\ w.type = "write"
          /\ w.commit_ts = commit_ts

\* If a client is aborted, there should be no committed primary key.
AbortedClientConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      ~ \E w \in key_write[client_key[c].primary] :
          /\ w.start_ts = client_ts[c].start_ts
          /\ w.type = "write"

CommittedTxnConsistency ==
  \A c \in CLIENT :
    client_state[c] # "init" =>
      LET
        primary == client_key[c].primary
        secondary == client_key[c].secondary
        start_ts == client_ts[c].start_ts
      IN
        \A wp \in key_write[primary] :
          \* If the primary key is committed, the secondary keys of the same transaction
          \* must be either committed or locked
          wp.start_ts = start_ts /\ wp.type = "write" =>
            \A s \in secondary :
              \/ \E l \in key_lock[s] : l.ts = start_ts
              \/ \E ws \in key_write[s] : ws.start_ts = start_ts /\ ws.type = "write"
    
\* For each transaction, we cannot have both committed and rolled back keys.
RollbackConsistency ==
  \A start_ts \in {client_ts[c].start_ts : c \in CLIENT} :
    (\E k \in KEY :
       \E w \in key_write[k] : w.start_ts = start_ts /\ w.type = "rollback") =>
      \A k2 \in KEY :
        ~ \E w2 \in key_write[k2] : w2.start_ts = start_ts /\ w2.type = "write"

\* For each key, each write or rollback record in write column should have a
\* unique start_ts.
UniqueWrite ==
  \A k \in KEY :
    Cardinality({w.start_ts : w \in key_write[k]}) = Cardinality(key_write[k])
    
-----------------------------------------------------------------------------

THEOREM Safety ==
  PessimisticSpec => [](/\ TypeInvariant
                        /\ WriteConsistency
                        /\ LockConsistency
                        /\ CommittedTxnConsistency
                        /\ AbortedClientConsistency
                        /\ RollbackConsistency
                        /\ UniqueWrite)

=============================================================================
