----------------------- MODULE PessimisticTransaction -----------------------

EXTENDS Integers, TLC

\* The set of transaction keys.
CONSTANTS KEY
ASSUME KEY # {} \* Keys cannot be empty.

\* The set of clients to execute a transaction.
CONSTANTS CLIENT

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

\* lock_resolver[c] is a record of [lock: {[key, primary, start_ts]},
\* status: {[primary, start_ts, commit_ts]}]. When client c encounters
\* a lock, the lock will be added to the lock field. When there are locks
\* in the record, client c may resolve the locks.
VARIABLES lock_resolver

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
\* client messages are inserted to the set and never deleted. The server can
\* pick any message in the set to execute.
VARIABLES msg

client_vars == <<client_state, client_ts, client_key, lock_resolver>>
key_vars == <<key_data, key_lock, key_write, key_last_read_ts>>
vars == <<next_ts, client_vars, key_vars, msg>>

-----------------------------------------------------------------------------

Pos == {x \in Nat : x > 0}

Range(m) == {m[i] : i \in DOMAIN m}

-----------------------------------------------------------------------------

\* find a stale lock for key k.
findStaleLock(k, ts) ==
  {l \in key_lock[k] : l.for_update_ts = 0 /\ l.ts < ts}

sendTxnStatus(c, k, ts, commit_ts) ==
  lock_resolver' = [lock_resolver EXCEPT
    ![c].status = @ \union {[primary |-> k,
                             start_ts |-> ts,
                             commit_ts |-> commit_ts]}]
  
writeRollback(k, ts) ==
  key_write' = [key_write EXCEPT
    ![k] = @ \union {[ts |-> ts, type |-> "rollback", start_ts |-> ts]}]

abortTxn(c) ==
  client_state' = [client_state EXCEPT ![c] = "abort"]
  
-----------------------------------------------------------------------------

Start(c) ==
  /\ client_state[c] = "init"
  /\ next_ts' = next_ts + 1
  /\ \E ks \in SUBSET KEY:
       \E primary \in ks :
         client_key' =
           [client_key EXCEPT
             ![c] = [primary |-> primary,
                     secondary |-> ks \ {primary},
                     pessimistic |-> ks,
                     pending |-> ks]
           ]
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts', ![c].for_update_ts = next_ts']
  /\ UNCHANGED <<lock_resolver, key_vars, msg>>
  
Read(c) ==
  /\ client_state[c] = "working"
  /\ \E k \in KEY :
       /\ msg' = msg \union 
            {[c |-> c, type |-> "read", key |-> k, start_ts |-> client_ts[c].start_ts]}
       /\ UNCHANGED <<next_ts, client_vars, key_vars>>
         
CheckTxnStatus(c) ==
  /\ client_state[c] \in {"working", "prewriting"}
  /\ LET
       lock == lock_resolver[c].lock
       status == lock_resolver[c].status
     IN
       LET
         unknown_lock ==
           {l \in lock : 
             ~ \E s \in status :
                 /\ l.primary = s.primary 
                 /\ l.start_ts = s.start_ts}
       IN
         /\ msg' = msg \union {
              [c |-> c, type |-> "cleanup",
               key |-> l.primary, start_ts |-> l.start_ts] : l \in unknown_lock
            }
         /\ UNCHANGED <<next_ts, client_vars, key_vars>>
         
ResolveLock(c) ==
  /\ client_state[c] \in {"working", "prewriting"}
  /\ LET
       lock == lock_resolver[c].lock
       status == lock_resolver[c].status
     IN
       LET
         txn_with_lock ==
           {s \in status : 
             \E l \in lock :
               /\ l.primary = s.primary 
               /\ l.start_ts = s.start_ts}
       IN
         /\ msg' = msg \union {
              [c |-> c, type |-> "resolve", key |-> txn.primary,
               start_ts |-> txn.start_ts, commit_ts |-> txn.commit_ts] : txn \in txn_with_lock
            }
         /\ UNCHANGED <<next_ts, client_vars, key_vars>>
         
LockKey(c) ==
  /\ client_state[c] = "working"
  /\ IF client_key[c].pessimistic = {}
     THEN
       /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
       /\ UNCHANGED <<client_ts, client_key, lock_resolver, next_ts, key_vars, msg>>
     ELSE
       \E k \in client_key[c].pessimistic :
         /\ msg' = msg \union 
              {[c |-> c, type |-> "lock", key |-> k, primary |-> client_key[c].primary,
               start_ts |-> client_ts[c].start_ts, for_update_ts |-> client_ts[c].for_update_ts]}
         /\ UNCHANGED <<next_ts, client_vars, key_vars>>
       
Prewrite(c) ==
  /\ client_state[c] = "prewriting"
  /\ IF client_key[c].pending = {}
     THEN
       /\ client_state' = [client_state EXCEPT ![c] = "committing"]
       /\ UNCHANGED <<client_ts, client_key, lock_resolver, next_ts, key_vars, msg>>
     ELSE
       \E k \in client_key[c].pending :
         /\ msg' = msg \union 
              {[c |-> c, type |-> "prewrite", key |-> k, primary |-> client_key[c].primary,
               start_ts |-> client_ts[c].start_ts, for_update_ts |-> client_ts[c].for_update_ts]}
         /\ UNCHANGED <<next_ts, client_vars, key_vars>>
         
Commit(c) ==
  /\ client_state[c] = "committing"
  /\ IF client_ts[c].commit_ts = 0
     THEN
       /\ next_ts' = next_ts + 1
       /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts']
     ELSE
       UNCHANGED <<next_ts, client_ts>>
  /\ msg' = msg \union
       {[c |-> c, type |-> "commit", key |-> client_key[c].primary,
         start_ts |-> client_ts[c].start_ts, commit_ts |-> client_ts'[c].commit_ts]}
  /\ UNCHANGED <<client_state, client_key, lock_resolver, key_vars>>
  
         
ClientOp(c) ==
  \/ Start(c)
  \/ Read(c)
  \/ CheckTxnStatus(c)
  \/ ResolveLock(c)
  \/ LockKey(c)
  \/ Prewrite(c)
  \/ Commit(c)
  
DoRead(cmd) ==
  LET
    c == cmd.c
    k == cmd.key
    ts == cmd.start_ts
  IN
    LET
      stale_lock == findStaleLock(k, ts)
    IN
      IF stale_lock = {}
      THEN
        /\ key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = ts]
        /\ UNCHANGED <<client_vars, key_data, key_lock, key_write, next_ts, msg>>
      ELSE
        /\ lock_resolver' = [lock_resolver EXCEPT ![c].lock = @ \union stale_lock]
        /\ UNCHANGED <<client_state, client_ts, client_key, key_vars, next_ts, msg>>
        
DoCheckTxnStatus(cmd) ==
  LET
    c == cmd.c
    k == cmd.key
    ts == cmd.start_ts
  IN
    LET
      lock == {l \in key_lock[k] : l.ts = ts}
      write == {w \in key_write[k] : w.start_ts = ts}
    IN
      IF lock = {}
      THEN
        IF \E w \in write : w.type = "write"
        THEN
          LET
            rec == CHOOSE w \in write : w.type = "write"
          IN
            /\ sendTxnStatus(c, k, ts, rec.ts)
            /\ UNCHANGED <<client_state, client_ts, client_key, key_vars, next_ts, msg>>   
        ELSE
          IF \E w \in write : w.type = "rollback"
          THEN
            /\ sendTxnStatus(c, k, ts, 0)
            /\ UNCHANGED <<client_state, client_ts, client_key, key_vars, next_ts, msg>>
          ELSE
            /\ writeRollback(k, ts)
            /\ sendTxnStatus(c, k, ts, 0)
            /\ UNCHANGED <<client_state, client_ts, client_key, key_data, key_lock, key_last_read_ts, next_ts, msg>>                          
      ELSE
        /\ key_lock' = [key_lock EXCEPT ![k] = {}]
        /\ key_data' = [key_data EXCEPT ![k] = @ \ {[ts |-> ts]}]
        /\ writeRollback(k, ts)
        /\ sendTxnStatus(c, k, ts, 0)   
        /\ UNCHANGED <<client_state, client_ts, client_key, key_last_read_ts, next_ts, msg>>     
        
DoLockKey(cmd) ==
  LET
    c == cmd.c
    k == cmd.key
    primary == cmd.primary
    ts == cmd.start_ts
    for_update_ts == cmd.for_update_ts
  IN
    IF key_lock[k] = {}
    THEN
      /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> ts, for_update_ts |-> for_update_ts, primary |-> primary, pessimistic |-> TRUE]}]
      /\ client_key' = [client_key EXCEPT ![c].pessimistic = @ \ {k}] \* may not change
      /\ UNCHANGED <<client_state, client_ts, lock_resolver, key_data, key_write, key_last_read_ts, next_ts, msg>>
    ELSE
      /\ lock_resolver' = [lock_resolver EXCEPT ![c].lock = @ \union {[key |-> k, primary |-> l.primary, start_ts |-> l.ts] : l \in key_lock[k]}]
      /\ UNCHANGED <<client_state, client_ts, client_key, key_vars, next_ts, msg>>
      
DoPrewrite(cmd) ==
  LET
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
      /\ abortTxn(c)
      /\ UNCHANGED <<client_ts, client_key, lock_resolver, next_ts, key_vars, msg>>
    ELSE
      /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> ts, for_update_ts |-> for_update_ts, primary |-> primary, pessimistic |-> FALSE]}]
      /\ key_data' = [key_data EXCEPT ![k] = @ \union {[ts |-> ts]}]
      /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}] \* may not change
      /\ UNCHANGED <<client_state, client_ts, lock_resolver, key_write, key_last_read_ts, next_ts, msg>>
      
DoCommit(cmd) ==
  LET
    c == cmd.c
    k == cmd.key
    start_ts == cmd.start_ts
    commit_ts == cmd.commit_ts
  IN
    IF
      \/ key_lock[k] = {}
      \/ \E l \in key_lock[k] : l.ts # start_ts
    THEN
      IF \E w \in key_write[k] : w.start_ts = start_ts /\ w.type = "write"
      THEN
        /\ client_state' = [client_state EXCEPT ![c] = "committed"]
        /\ UNCHANGED <<client_ts, client_key, lock_resolver, next_ts, key_vars, msg>>
      ELSE
        /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
        /\ UNCHANGED <<client_ts, client_key, lock_resolver, next_ts, key_vars, msg>>
    ELSE
      /\ client_state' = [client_state EXCEPT ![c] = "committed"]
      /\ key_lock' = [key_lock EXCEPT ![k] = {}]
      /\ key_write' = [key_write EXCEPT ![k] = @ \union {[ts |-> commit_ts, type |-> "write", start_ts |-> start_ts]}]
      /\ UNCHANGED <<client_ts, client_key, lock_resolver, next_ts, key_data, key_last_read_ts, msg>>

ServerOp(cmd) ==
  \/ /\ cmd.type = "read"
     /\ DoRead(cmd)
  \/ /\ cmd.type = "cleanup"
     /\ DoCheckTxnStatus(cmd)
  \/ /\ cmd.type = "lock"
     /\ DoLockKey(cmd)
  \/ /\ cmd.type = "prewrite"
     /\ DoPrewrite(cmd)
  \/ /\ cmd.type = "commit"
     /\ DoCommit(cmd)

Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0,
                                      for_update_ts |-> 0,
                                      commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |-> {}]
    /\ lock_resolver = [c \in CLIENT |-> [lock |-> {}, status |-> {}]]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_data = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> {}]
    /\ key_last_read_ts = [k \in KEY |-> 0]
    /\ msg = {}

Next == 
  \/ \E cmd \in msg : ServerOp(cmd)
  \/ \E c \in CLIENT : ClientOp(c)

-----------------------------------------------------------------------------

NextTsTypeInv == next_ts \in Pos

ClientStateTypeInv ==
  client_state \in [
    CLIENT -> {"init", "working", "prewriting",
               "committing", "committed", "aborted"}
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

LockResolverTypeInv ==
  \A c \in CLIENT :
    /\ lock_resolver[c].lock \subseteq [key : KEY, primary : KEY, start_ts: Pos]
    /\ lock_resolver[c].status \subseteq [primary : KEY, start_ts : Pos, commit_ts : Nat]

KeyDataTypeInv ==
  key_data \in [KEY -> SUBSET [ts : Pos]]

KeyLockTypeInv ==
  key_lock \in [KEY -> SUBSET [ts : Pos, for_update_ts : Nat, primary : KEY, pessimistic : BOOLEAN]]

KeyWriteTypeInv ==
  key_write \in [KEY ->
    SUBSET [ts : Pos, type : {"write", "rollback"}, start_ts : Pos]
  ]

KeyWriteStartTsInv ==
  \A k \in DOMAIN key_write:
    LET
      rec == key_write[k]
    IN
      \/ rec = {}
      \/ IF rec.type = "write"
         THEN rec.ts > rec.start_ts
         ELSE rec.type = "rollback" /\ rec.ts = rec.start_ts

KeyLastReadTsTypeInv ==
  key_last_read_ts \in [KEY -> Nat]

MsgTypeInv ==
  msg \subseteq (
    [c : CLIENT, type : {"lock", "prewrite"}, key : KEY, primary: KEY,
     start_ts : Pos, for_update_ts : Pos] \union
    [c : CLIENT, type: {"commit"}, key : KEY, start_ts : Pos, commit_ts : Pos] \union
    [c : CLIENT, type: {"resolve"}, key : KEY, start_ts : Pos, commit_ts : Nat] \union
    [c : CLIENT, type: {"read", "cleanup"}, key : KEY, start_ts : Pos] \union
    [type : {"rollback"}, key : SUBSET KEY, start_ts: Pos]
  )

TypeInvariant ==
  /\ NextTsTypeInv
  /\ ClientStateTypeInv
  /\ ClientTsTypeInv
  /\ ClientKeyTypeInv
  /\ LockResolverTypeInv
  /\ KeyDataTypeInv
  /\ KeyLockTypeInv
  /\ KeyWriteTypeInv
  /\ KeyWriteStartTsInv
  /\ KeyLastReadTsTypeInv
  /\ MsgTypeInv

=============================================================================
