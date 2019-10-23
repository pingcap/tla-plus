----------------------- MODULE PessimisticTransaction -----------------------

EXTENDS Integers, FiniteSets, TLC

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

client_vars == <<client_state, client_ts, client_key>>
key_vars == <<key_data, key_lock, key_write, key_last_read_ts>>
vars == <<next_ts, client_vars, key_vars, msg>>

-----------------------------------------------------------------------------

Pos == {x \in Nat : x > 0}

Range(m) == {m[i] : i \in DOMAIN m}

-----------------------------------------------------------------------------

\* find a stale lock for key k.
findStaleLock(k, ts) ==
  {l \in key_lock[k] : l.pessimistic = FALSE /\ l.ts < ts}
  
rollback(k, ts) ==
  /\ IF \E l \in key_lock[k] : l.ts = ts
     THEN key_lock' = [key_lock EXCEPT ![k] = {}]
     ELSE UNCHANGED key_lock
  /\ key_data' = [key_data EXCEPT ![k] = @ \ {[ts |-> ts]}]
  /\ key_write' = [key_write EXCEPT
       ![k] = @ \union {[ts |-> ts, type |-> "rollback", start_ts |-> ts]}]
       
commit(k, start_ts, commit_ts) ==
  /\ IF \E l \in key_lock[k] : l.ts = start_ts
     THEN 
       /\ key_lock' = [key_lock EXCEPT ![k] = {}]
       /\ key_write' = [key_write EXCEPT ![k] = @ \union {[ts |-> commit_ts, type |-> "write", start_ts |-> start_ts]}]
       /\ Assert(key_last_read_ts[k] < commit_ts, TRUE)
     ELSE
       UNCHANGED <<key_lock, key_write>>
  /\ UNCHANGED key_data

abortTxn(c) ==
  client_state' = [client_state EXCEPT ![c] = "aborted"]
  
-----------------------------------------------------------------------------

Start(c) ==
  /\ client_state[c] = "init"
  /\ next_ts' = next_ts + 1
  /\ \E primary \in KEY :
       client_key' =
         [client_key EXCEPT
           ![c] = [primary |-> primary,
                   secondary |-> KEY \ {primary},
                   pessimistic |-> KEY,
                   pending |-> KEY]
         ]
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts', ![c].for_update_ts = next_ts']
  /\ UNCHANGED <<key_vars, msg>>
         
LockKey(c) ==
  /\ client_state[c] = "working"
  /\ IF client_key[c].pessimistic = {}
     THEN
       /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
       /\ UNCHANGED <<client_ts, client_key, next_ts, key_vars, msg>>
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
       /\ UNCHANGED <<client_ts, client_key, next_ts, key_vars, msg>>
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
  /\ UNCHANGED <<client_state, client_key, key_vars>>
  
         
ClientOp(c) ==
  \/ Start(c)
  \/ LockKey(c)
  \/ Prewrite(c)
  \/ Commit(c)
  
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
           THEN
             /\ IF key_last_read_ts[k] < ts
                THEN key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = ts]
                ELSE UNCHANGED key_last_read_ts
             /\ UNCHANGED <<client_vars, key_data, key_lock, key_write, next_ts, msg>>
           ELSE
             /\ msg' = msg \union
                  {[type |-> "cleanup", primary |-> l.primary, start_ts |-> l.ts] : l \in stale_lock}
             /\ UNCHANGED <<client_state, client_ts, client_key, key_vars, next_ts>>
        
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
          THEN
            /\ msg' = msg \union
                 {[type |-> "resolve", primary |-> k, start_ts |-> ts, commit_ts |-> t.ts] : t \in committed}
            /\ UNCHANGED <<next_ts, client_vars, key_vars>>
          ELSE
            /\ rollback(k, ts)
            /\ UNCHANGED <<key_last_read_ts, next_ts, client_vars>>
            /\ \/ msg' = msg \union
                    {[type |-> "resolve", primary |-> k, start_ts |-> ts, commit_ts |-> 0]}
               \/ UNCHANGED msg

DoResolve ==
  \E cmd \in msg :
    /\ cmd.type = "resolve"
    /\ IF cmd.commit_ts = 0
       THEN
         \E k \in KEY :
           \E l \in key_lock[k] :
             /\ l.primary = cmd.primary
             /\ l.ts = cmd.start_ts
             /\ rollback(k, cmd.start_ts)
       ELSE
         \E k \in KEY :
           \E l \in key_lock[k] :
             /\ l.primary = cmd.primary
             /\ l.ts = cmd.start_ts
             /\ commit(k, cmd.start_ts, cmd.commit_ts)
    /\ UNCHANGED <<next_ts, client_vars, key_last_read_ts, msg>>    
          

DoLockKey ==
  \E cmd \in msg :
   /\ cmd.type = "lock"
   /\ LET
        c == cmd.c
        k == cmd.key
        primary == cmd.primary
        ts == cmd.start_ts
        for_update_ts == cmd.for_update_ts
        writeLock ==
              /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> ts, for_update_ts |-> for_update_ts, primary |-> primary, pessimistic |-> TRUE]}]
              /\ UNCHANGED <<client_state, client_ts, key_data, key_write, key_last_read_ts, next_ts, msg>>
              /\ \/ client_key' = [client_key EXCEPT ![c].pessimistic = @ \ {k}]
                 \/ UNCHANGED client_key
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
          THEN writeLock
          ELSE
            LET 
              latest == CHOOSE w \in key_write[k] : \A w2 \in key_write[k] : w.ts >= w2.ts
            IN
              IF latest.ts > for_update_ts
              THEN updateForUpdateTs(latest.ts)
              ELSE
                IF \E w \in key_write[k] : w.start_ts = ts /\ w.type = "rollback"
                THEN abortTxn(c) /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars, msg>>
                ELSE writeLock
        ELSE
          LET
            l == CHOOSE l \in key_lock[k] : TRUE
          IN
            IF l.ts # ts
            THEN                        
              /\ msg' = msg \union
                   {[type |-> "cleanup", primary |-> l.primary, start_ts |-> l.ts]}
              /\ UNCHANGED <<client_state, client_ts, client_key, key_vars, next_ts>>
            ELSE
              IF l.pessimistic = FALSE
              THEN UNCHANGED vars
              ELSE
                IF l.for_update_ts < for_update_ts
                THEN writeLock
                ELSE UNCHANGED vars
      
DoPrewrite ==
  \E cmd \in msg :
   /\ cmd.type = "prewrite"
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
          /\ abortTxn(c)
          /\ UNCHANGED <<client_ts, client_key, next_ts, key_vars, msg>>
        ELSE
          /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> ts, for_update_ts |-> for_update_ts, primary |-> primary, pessimistic |-> FALSE]}]
          /\ key_data' = [key_data EXCEPT ![k] = @ \union {[ts |-> ts]}]
          /\ \/ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
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
        THEN
          /\ commit(k, start_ts, commit_ts)
          /\ \/ client_state' = [client_state EXCEPT ![c] = "committed"]
             \/ UNCHANGED client_state
          /\ UNCHANGED <<client_ts, client_key, next_ts, key_last_read_ts, msg>>
        ELSE
          /\ \/ client_state' = [client_state EXCEPT ![c] = "aborted"]
             \/ UNCHANGED client_state
          /\ UNCHANGED <<client_ts, client_key, next_ts, key_vars, msg>>

ServerOp ==
  \/ DoRead
  \/ DoCleanup
  \/ DoResolve
  \/ DoLockKey
  \/ DoPrewrite
  \/ DoCommit
     
Read ==
  \E ts \in 0..next_ts :
    \E k \in KEY :
      /\ msg' = msg \union 
           {[type |-> "read", key |-> k, ts |-> ts]}
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
  \/ \E c \in CLIENT : ClientOp(c)
  \/ Read
  
PessimisticSpec == Init /\ [][Next]_vars

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
    [type : {"resolve"}, primary : KEY, start_ts : Pos, commit_ts : Nat] \union
    [type : {"rollback"}, key : SUBSET KEY, start_ts: Pos]
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
  \* There should be at most one lock for each key.
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] :
         ~ \E w \in key_write[k] : w.start_ts = l.ts

CommittedClientConsistency ==
  \A c \in CLIENT :
    LET
      start_ts == client_ts[c].start_ts
      commit_ts == client_ts[c].commit_ts
      primary == client_key[c].primary
    IN
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
                        /\ RollbackConsistency
                        /\ UniqueWrite)

=============================================================================
