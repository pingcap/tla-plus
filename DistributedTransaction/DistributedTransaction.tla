----------------------- MODULE DistributedTransaction -----------------------
EXTENDS Integers, FiniteSets

\* The set of all keys
CONSTANTS KEY

\* The sets of optimistic clients and pessimistic clients.
CONSTANTS OPTIMISTIC_CLIENT, PESSIMISTIC_CLIENT
CLIENT == PESSIMISTIC_CLIENT \union OPTIMISTIC_CLIENT

\* Functions that maps a client to keys it wants to read, write.
\* representing the involved keys of each client.
CONSTANTS CLIENT_READ_KEY, CLIENT_WRITE_KEY
CLIENT_KEY == [c \in CLIENT |-> CLIENT_READ_KEY[c] \union CLIENT_WRITE_KEY[c]]
ASSUME \A c \in CLIENT: CLIENT_KEY[c] \subseteq KEY

\* CLIENT_PRIMARY is the primary key of each client.
CONSTANTS CLIENT_PRIMARY
ASSUME \A c \in CLIENT: CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

\* Timestamp of transactions.
Ts == Nat \ {0}
NoneTs == 0

\* The algorithm is easier to understand in terms of the set of msgs of
\* all messages that have ever been sent.  A more accurate model would use
\* one or more variables to represent the messages actually in transit,
\* and it would include actions representing message loss and duplication
\* as well as message receipt.
\*
\* In the current spec, there is no need to model message loss because we
\* are mainly concerned with the algorithm's safety property.  The safety
\* part of the spec says only what messages may be received and does not
\* assert that any message actually is received.  Thus, there is no
\* difference between a lost message and one that is never received.
VARIABLES req_msgs
VARIABLES resp_msgs

\* key_data[k] is the set of multi-version data of the key.  Since we
\* don't care about the concrete value of data, a start_ts is sufficient
\* to represent one data version.
VARIABLES key_data
\* key_lock[k] is the set of lock (zero or one element).  A lock is of a
\* record of [ts: start_ts, primary: key, type: lock_type].  If primary
\* equals to k, it is a primary lock, otherwise secondary lock.  lock_type
\* is one of {"prewrite_optimistic", "prewrite_pessimistic", "lock_key"}.
\* lock_key denotes the pessimistic lock performed by ServerLockKey
\* action, the prewrite_pessimistic denotes percolator optimistic lock
\* who is transformed from a lock_key lock by action
\* ServerPrewritePessimistic, and prewrite_optimistic denotes the
\* classic optimistic lock.
\* 
\* In TiKV, key_lock has an additional for_update_ts field and the
\* LockType is of four variants: 
\* {"PUT", "DELETE", "LOCK", "PESSIMISTIC"}.
\* 
\* In the spec, we abstract them by:
\* (1) LockType \in {"PUT", "DELETE", "LOCK"} /\ for_update_ts = 0 <=>
\*      type = "prewrite_optimistic"
\* (2) LockType \in {"PUT", "DELETE"} /\ for_update_ts > 0 <=>
\*      type = "prewrite_pessimistic"
\* (3) LockType = "PESSIMISTIC" <=> type = "lock_key"
\*
\* There's an min_commit_ts field to indicate the minimum commit time
\* It's used in non-blocked reading.
\* TODO: upd min_commit_ts comment.
VARIABLES key_lock
\* key_write[k] is a sequence of commit or rollback record of the key.
\* It's a record of [ts, start_ts, type, [protected]].  type can be either
\* "write" or "rollback".  ts represents the commit_ts of "write" record.
\* Otherwise, ts equals to start_ts on "rollback" record.  "rollback"
\* record has an additional protected field.  protected signifies the
\* rollback record would not be collapsed.
VARIABLES key_write

\* client_state[c] indicates the current transaction stage of client c.
VARIABLES client_state
\* client_ts[c] is a record of [start_ts, commit_ts, for_update_ts, min_commit_ts].
\* Fields are all initialized to NoneTs.
VARIABLES client_ts
\* client_key[c] is a record of [locking: {key}, prewriting: {key}].
\* Hereby, "locking" denotes the keys whose pessimistic locks
\* haven't been acquired, "prewriting" denotes the keys that are pending
\* for prewrite.
VARIABLES client_key

\* next_ts is a globally monotonically increasing integer, representing
\* the virtual clock of transactions.  In practice, the variable is
\* maintained by PD, the time oracle of a cluster.
VARIABLES next_ts

msg_vars == <<req_msgs, resp_msgs>>
client_vars == <<client_state, client_ts, client_key>>
key_vars == <<key_data, key_lock, key_write>>
vars == <<msg_vars, client_vars, key_vars, next_ts>>

SendReqs(msgs) == req_msgs' = req_msgs \union msgs
SendResp(msg) == resp_msgs' = resp_msgs \union {msg}
-----------------------------------------------------------------------------
\* Type Definitions

ReqMessages ==
          [start_ts : Ts, primary : KEY, type : {"lock_key"}, key : KEY,
            for_update_ts : Ts]
  \union  [start_ts : Ts, primary : KEY, type : {"get"}, key : KEY]
  \union  [start_ts : Ts, primary : KEY, type : {"prewrite_optimistic"}, key : KEY]
  \union  [start_ts : Ts, primary : KEY, type : {"prewrite_pessimistic"}, key : KEY]
  \union  [start_ts : Ts, primary : KEY, type : {"commit"}, commit_ts : Ts]
  \union  [start_ts : Ts, primary : KEY, type : {"resolve_rollbacked"}]
  \union  [start_ts : Ts, primary : KEY, type : {"resolve_committed"}, commit_ts : Ts]

  \* In TiKV, there's an extra flag `rollback_if_not_exist` in the `check_txn_status` request.
  \*
  \* Because the client prewrites the primary key and secondary key in parallel, it's possible
  \* that the primary key lock is missing and also no commit or rollback record for the transaction
  \* is found in the write CF, while there is a lock on the secondary key (so other transaction
  \* is blocked, therefore this check_txn_status is sent). And there are two possible cases:
  \*
  \*    1. The prewrite request for the primary key has not reached yet.
  \*    2. The client is crashed after sending the prewrite request for the secondary key.
  \*
  \* In order to address the first case, the client sending `check_txn_status` should not rollback
  \* the primary key until the TTL on the secondary key is expired, and thus, `rollback_if_not_exist`
  \* should be set to false before the TTL expires (and set true afterward).
  \*
  \* In TLA+ spec, the TTL is considered constantly expired when the action is taken, so the
  \* `rollback_if_not_exist` is assumed true, thus no need to carry it in the message.
  \union  [start_ts : Ts, caller_start_ts : Ts, primary : KEY, type : {"check_txn_status"},
           resolving_pessimistic_lock : BOOLEAN]

RespMessages ==
          [start_ts : Ts, type : {"prewrited"}, key : KEY]
  \union  [start_ts : Ts, type : {"get_resp"}, key : KEY, value : Ts, met_optimistic_lock : BOOLEAN]

  \* Conceptually, acquire a pessimistic lock of a key is equivalent to reading its value, 
  \* and putting the value in the response can reduce communication. Also, as mentioned
  \* above, we don’t care about the actual value here, so a timestamp can be used 
  \* instead of the value.
  \union  [start_ts : Ts, type : {"locked_key"}, key : KEY, value_ts :  Ts]
  \union  [start_ts : Ts, type : {"lock_failed"}, key : KEY, latest_commit_ts : Ts,
           lock_ts : Ts, lock_type : {"no_lock", "lock_key", "prewrite_pessimistic", "prewrite_optimistic"}]
  \union  [start_ts : Ts, type : {"committed",
                                  "commit_aborted",
                                  "prewrite_aborted",
                                  "lock_key_aborted"}]
  \union  [start_ts : Ts, type : {"check_txn_status_resp"}, 
           action : {"rollbacked",
                     "pessimistic_rollbacked", 
                     "committed", 
                     "min_commit_ts_pushed",
                     "lock_not_exist_do_nothing"}]

TypeOK == /\ req_msgs \in SUBSET ReqMessages
          /\ resp_msgs \in SUBSET RespMessages
          /\ key_data \in [KEY -> SUBSET Ts]
          /\ key_lock \in [KEY -> SUBSET [ts : Ts, 
                                          primary : KEY, 
                                          \* As defined above, Ts == Nat \ 0, here we use 0
                                          \* to indicates that there's no min_commit_ts limit.
                                          min_commit_ts : Ts \union {NoneTs},
                                          type : {"prewrite_optimistic",
                                                  "prewrite_pessimistic",
                                                  "lock_key"}]]
          \* At most one lock in key_lock[k]
          /\ \A k \in KEY: Cardinality(key_lock[k]) <= 1
          /\ key_write \in [KEY -> SUBSET (
                      [ts : Ts, start_ts : Ts, type : {"write"}]
              \union  [ts : Ts, start_ts : Ts, type : {"rollback"}, protected : BOOLEAN])]
          \* The reading phase only apply for optimistic transactions
          /\ client_state \in [CLIENT -> {"init", "locking", "reading", "prewriting", "committing"}]
          /\ client_ts \in [CLIENT -> [start_ts : Ts \union {NoneTs},
                                       commit_ts : Ts \union {NoneTs},
                                       for_update_ts : Ts \union {NoneTs},
                                       min_commit_ts : Ts \union {NoneTs}]]
          /\ client_key \in [CLIENT -> [locking: SUBSET KEY, prewriting : SUBSET KEY]]
          /\ next_ts \in Ts
-----------------------------------------------------------------------------
\* Client Actions

ClientReadKey(c) == 
  /\ client_state[c] = "init"
  /\ c \in OPTIMISTIC_CLIENT
  /\ client_state' = [client_state EXCEPT ![c] = "reading"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ SendReqs({[type |-> "get",
                start_ts |-> client_ts'[c].start_ts,
                primary |-> CLIENT_PRIMARY[c],
                key |-> k] : k \in CLIENT_READ_KEY[c]})
  /\ UNCHANGED <<resp_msgs, client_key, key_vars>>

ClientLockKey(c) ==
  /\ client_state[c] = "reading"
  /\ client_state' = [client_state EXCEPT ![c] = "locking"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts, ![c].for_update_ts = next_ts]
  /\ next_ts' = next_ts + 1
  \* Assume we need to acquire pessimistic locks for all keys
  /\ client_key' = [client_key EXCEPT ![c].locking = CLIENT_KEY[c]]
  /\ SendReqs({[type |-> "lock_key",
                start_ts |-> client_ts'[c].start_ts,
                primary |-> CLIENT_PRIMARY[c],
                key |-> k,
                for_update_ts |-> client_ts'[c].for_update_ts] : k \in CLIENT_KEY[c]})
  /\ UNCHANGED <<resp_msgs, key_vars>>

ClientLockedKey(c) ==
  /\ client_state[c] = "locking"
  /\ \E resp \in resp_msgs :
      /\ resp.type = "locked_key"
      /\ resp.start_ts = client_ts[c].start_ts
      /\ resp.key \in client_key[c].locking
      /\ client_key' = [client_key EXCEPT ![c].locking = @ \ {resp.key}]
      /\ UNCHANGED <<msg_vars, key_vars, client_ts, client_state, next_ts>>

ClientRetryLockKey(c) ==
  /\ client_state[c] = "locking"
  /\ \E resp \in resp_msgs :
      /\ resp.type = "lock_failed"
      /\ resp.start_ts = client_ts[c].start_ts
      /\ resp.latest_commit_ts > client_ts[c].for_update_ts
      /\ client_ts' = [client_ts EXCEPT ![c].for_update_ts = resp.latest_commit_ts]
      /\ IF resp.lock_type \in {"lock_key"}
         THEN
          /\ SendReqs({[type |-> "check_txn_status",
                        start_ts |-> client_ts[c].start_ts,
                        caller_start_ts |-> next_ts,
                        primary |-> CLIENT_PRIMARY[c],
                        resoving_pessimistic_lock |-> TRUE]})
          /\ next_ts' = next_ts + 1
          /\ UNCHANGED <<resp_msgs, key_vars, client_state, client_key>>
          ELSE IF ~ resp.lock_type = "no_lock"
          THEN
            /\ SendReqs({[type |-> "check_txn_status",
                        start_ts |-> client_ts[c].start_ts,
                        caller_start_ts |-> next_ts,
                        primary |-> CLIENT_PRIMARY[c],
                        resoving_pessimistic_lock |-> FALSE]})
            /\ next_ts' = next_ts + 1
            /\ UNCHANGED <<resp_msgs, key_vars, client_state, client_key>>
          ELSE
            /\ UNCHANGED <<resp_msgs, key_vars, client_state, client_key, next_ts>>
      /\ SendReqs({[type |-> "lock_key",
                    start_ts |-> client_ts'[c].start_ts,
                    primary |-> CLIENT_PRIMARY[c],
                    key |-> resp.key,
                    for_update_ts |-> client_ts'[c].for_update_ts]})
      
ClientPrewritePessimistic(c) ==
  /\ client_state[c] = "locking"
  /\ client_key[c].locking = {}
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_KEY[c]]
  /\ SendReqs({[type |-> "prewrite_pessimistic",
                start_ts |-> client_ts[c].start_ts,
                primary |-> CLIENT_PRIMARY[c],
                key |-> k] : k \in CLIENT_KEY[c]})
  /\ UNCHANGED <<resp_msgs, key_vars, client_ts, next_ts>>

\* Add a function like `ClientRetryReadKey` (?)
ClientCheckTxnStatus(c) ==
  /\ client_state = "reading"
  /\ \E resp \in resp_msgs :
    /\ resp.type = "get_resp"
    /\ resp.met_optimistic_lock = TRUE
    /\ SendReqs({[type |-> "check_txn_status",
                  start_ts |-> client_ts[c].start_ts,
                  caller_start_ts |-> next_ts,
                  primary |-> CLIENT_PRIMARY[c],
                  resovling_pessimistic_lock |-> FALSE]})
    /\ UNCHANGED <<resp_msgs, client_vars, key_vars>>

ClientPrewriteOptimistic(c) ==
  /\ client_state[c] = "reading"
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_KEY[c]]
  /\ SendReqs({[type |-> "prewrite_optimistic",
                start_ts |-> client_ts[c].start_ts,
                primary |-> CLIENT_PRIMARY[c],
                key |-> k] : k \in CLIENT_KEY[c]})
  /\ UNCHANGED <<resp_msgs, client_ts, key_vars, next_ts>>

ClientPrewrited(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].locking = {}
  /\ \E resp \in resp_msgs :
      /\ resp.type = "prewrited"
      /\ resp.start_ts = client_ts[c].start_ts
      /\ resp.key \in client_key[c].prewriting
      /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {resp.key}]
      /\ UNCHANGED <<msg_vars, key_vars, client_ts, client_state, next_ts>>

ClientCommit(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].prewriting = {}
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ SendReqs({[type |-> "commit",
               start_ts |-> client_ts'[c].start_ts,
               primary |-> CLIENT_PRIMARY[c],
               commit_ts |-> client_ts'[c].commit_ts]})
  /\ UNCHANGED <<resp_msgs, key_vars, client_key>>
-----------------------------------------------------------------------------
\* Server Actions

\* Write the write column and unlock the lock iff the lock exists.
commit(pk, start_ts, commit_ts) ==
  \E l \in key_lock[pk] :
    /\ l.ts = start_ts
    /\ key_lock' = [key_lock EXCEPT ![pk] = {}]
    /\ key_write' = [key_write EXCEPT ![pk] = @ \union {[ts |-> commit_ts,
                                                         type |-> "write",
                                                         start_ts |-> start_ts]}]

\* Rollback the transaction that starts at start_ts on key k.
rollback(k, start_ts) ==
  LET
    \* Rollback record on the primary key of a pessimistic transaction
    \* needs to be protected from being collapsed.  If we can't decide
    \* whether it suffices that because the lock is missing or mismatched,
    \* it should also be protected.
    protected == \/ \E l \in key_lock[k] :
                      /\ l.ts = start_ts
                      /\ l.primary = k 
                      /\ l.type \in {"lock_key", "prewrite_pessimistic"} 
                 \/ \E l \in key_lock[k] : l.ts /= start_ts
                 \/ key_lock[k] = {}
  IN
    \* If a lock exists and has the same ts, unlock it.
    /\ IF \E l \in key_lock[k] : l.ts = start_ts
       THEN key_lock' = [key_lock EXCEPT ![k] = {}]
       ELSE UNCHANGED key_lock
    /\ key_data' = [key_data EXCEPT ![k] = @ \ {start_ts}]
    /\ IF 
          /\ ~ \E w \in key_write[k]: w.ts = start_ts
       THEN
            key_write' = [key_write EXCEPT
              ![k] = 
                \* collapse rollback
                (@ \ {w \in @ : w.type = "rollback" /\ ~w.protected /\ w.ts < start_ts})
                \* write rollback record
                \union {[ts |-> start_ts,
                        start_ts |-> start_ts,
                        type |-> "rollback",
                        protected |-> protected]}]
       ELSE
          UNCHANGED <<key_write>>

ServerLockKey ==
  \E req \in req_msgs :
    /\ req.type = "lock_key"
    /\ LET
        k == req.key
        start_ts == req.start_ts
       IN
        \* Pessimistic lock is allowed only if no stale lock exists.  If
        \* there is one, wait until ServerCleanupStaleLock to clean it up.
        /\ key_lock[k] = {}
        /\ LET
              latest_write == {w \in key_write[k] : \A w2 \in key_write[k] : w.ts >= w2.ts}
              
              all_commits == {w \in key_write[k] : w.type = "write"}
              latest_commit == {w \in all_commits : \A w2 \in all_commits : w.ts >= w2.ts}
           IN
              IF \E w \in key_write[k] : w.start_ts = start_ts /\ w.type = "rollback"
              THEN
                \* If corresponding rollback record is found, which
                \* indicates that the transcation is rollbacked, abort the
                \* transaction.
                /\ SendResp([start_ts |-> start_ts, type |-> "lock_key_aborted"])
                /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>
              ELSE
                \* Acquire pessimistic lock only if for_update_ts of req
                \* is greater or equal to the latest "write" record.
                \* Because if the latest record is "write", it means that
                \* a new version is committed after for_update_ts, which
                \* violates Read Committed guarantee.
                \/ /\ ~ \E w \in latest_commit : w.ts > req.for_update_ts
                   /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> start_ts,
                                                            primary |-> req.primary,
                                                            min_commit_ts |-> NoneTs,
                                                            type |-> "lock_key"]}]
                   /\ SendResp([start_ts |-> start_ts, type |-> "locked_key", key |-> k])
                   /\ UNCHANGED <<req_msgs, client_vars, key_data, key_write, next_ts>>
                \* Otherwise, reject the request and let client to retry
                \* with new for_update_ts.
                \/ \E w \in latest_commit :
                    /\ w.ts > req.for_update_ts
                    /\ SendResp([start_ts |-> start_ts,
                                 type |-> "lock_failed",
                                 key |-> k,
                                 latest_commit_ts |-> w.ts])
                    /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>

ServerReadKey ==
  \E req \in req_msgs :
    /\ req.type = "get"
    /\ LET
        k == req.key
        start_ts == req.start_ts
       IN
       /\ IF ~ \E l \in key_lock : l.type = "prewrite_optimistic"
          THEN
            /\ SendResp([start_ts |-> start_ts, type |-> "get_resp", key |-> k, value |-> Ts, met_optimistic_lock |-> FALSE]) \* TS here is not defined now...
            /\ UNCHANGED <<req_msgs, client_vars, key_vars>>
          ELSE
            /\ SendResp([start_ts |-> start_ts, type |-> "get_resp", key |-> k, value |-> NoneTs, met_optimistic_lock |-> TRUE])
            /\ UNCHANGED <<req_msgs, client_vars, key_vars>>

ServerPrewritePessimistic ==
  \E req \in req_msgs :
    /\ req.type = "prewrite_pessimistic"
    /\ LET
        k == req.key
        start_ts == req.start_ts
       IN
        \* Pessimistic prewrite is allowed only if pressimistic lock is
        \* acquired, otherwise abort the transaction.
        /\ IF \E l \in key_lock[k] : l.ts = start_ts
           THEN
              /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> start_ts,
                                                      primary |-> req.primary,
                                                      type |-> "prewrite_pessimistic"]}]
              /\ key_data' = [key_data EXCEPT ![k] = @ \union {start_ts}]
              /\ SendResp([start_ts |-> start_ts, type |-> "prewrited", key |-> k])
              /\ UNCHANGED <<req_msgs, client_vars, key_write, next_ts>>
           ELSE
              /\ SendResp([start_ts |-> start_ts, type |-> "prewrite_aborted"])
              /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>

ServerPrewriteOptimistic ==
  \E req \in req_msgs :
    /\ req.type = "prewrite_optimistic"
    /\ LET
        k == req.key
        start_ts == req.start_ts
       IN
        /\ IF \E w \in key_write[k] : w.ts >= start_ts
           THEN
              /\ SendResp([start_ts |-> start_ts, type |-> "prewrite_aborted"])
              /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>
           ELSE
              \* Optimistic prewrite is allowed only if no stale lock exists.  If
              \* there is one, wait until ServerCleanupStaleLock to clean it up.
              /\ \/ key_lock[k] = {} 
                 \/ \E l \in key_lock[k] : l.ts = start_ts
              /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> start_ts,
                                                       primary |-> req.primary,
                                                       min_commit_ts |-> NoneTs,
                                                       type |-> "prewrite_optimistic"]}]
              /\ key_data' = [key_data EXCEPT ![k] = @ \union {start_ts}]
              /\ SendResp([start_ts |-> start_ts, type |-> "prewrited", key |-> k])
              /\ UNCHANGED <<req_msgs, client_vars, key_write, next_ts>>

ServerCommit ==
  \E req \in req_msgs :
    /\ req.type = "commit"
    /\ LET
        pk == req.primary
        start_ts == req.start_ts
       IN
        IF \E w \in key_write[pk] : w.start_ts = start_ts /\ w.type = "write"
        THEN
          \* Key has already been committed.  Do nothing.
          /\ SendResp([start_ts |-> start_ts, type |-> "committed"])
          /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>
        ELSE
          IF \E l \in key_lock[pk] : l.ts = start_ts
          THEN
            \* Commit the key only if the prewrite lock exists.
            /\ commit(pk, start_ts, req.commit_ts)
            /\ SendResp([start_ts |-> start_ts, type |-> "committed"])
            /\ UNCHANGED <<req_msgs, client_vars, key_data, next_ts>>
          ELSE
            \* Otherwise, abort the transaction.
            /\ SendResp([start_ts |-> start_ts, type |-> "commit_aborted"])
            /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>

\* In the spec, the primary key with a lock may clean up itself
\* spontaneously.  There is no need to model a client to request clean up
\* because there is no difference between a optimistic client trying to
\* read a key that has lock timeouted and the key trying to unlock itself.
ServerCleanupStaleLock ==
  \E k \in KEY :
    \E l \in key_lock[k] :
      /\ SendReqs({[type |-> "check_txn_status",
                    start_ts |-> l.ts,
                    caller_start_ts |-> next_ts,
                    primary |-> l.primary,
                    resolving_pessimistic_lock |-> l.type = "lock_key"]})
      /\ next_ts' = next_ts + 1
      /\ UNCHANGED <<resp_msgs, client_vars, key_vars>>

\* Clean up the stale transaction by checking the status of the primary key.
\*
\* In practice, the transaction will be rolled back if TTL on the lock is expired. But
\* because it is hard to model the TTL in TLA+ spec, the TTL is considered constantly
\* expired when the action is taken.
\*
\* Moreover, TiKV will send a response for `TxnStatus` to the client, and then depending
\* on the `TxnStatus`, the client will send `resolve_rollback` or `resolve_commit` to the
\* secondary keys to clean up stale locks.  In the TLA+ spec, the response to `check_txn_status`
\* is omitted and TiKV will directly send `resolve_rollback` or `resolve_commit` message to
\* secondary keys, because the action of client sending resolve message by proxying the
\* `TxnStatus` from TiKV does not change the state of the client, therefore is equal to directly
\* sending resolve message by TiKV
ServerCheckTxnStatus ==
  \E req \in req_msgs :
    /\ req.type = "check_txn_status"
    /\ LET
          pk == req.primary
          start_ts == req.start_ts
          committed == {w \in key_write[pk] : w.start_ts = start_ts /\ w.type = "write"}
          caller_start_ts == req.caller_start_ts
       IN
          IF \E lock \in key_lock[pk] : lock.ts = start_ts
          \* Found the matching lock.
          THEN
          \/
            IF
              \* Pessimistic lock will be unlocked directly without rollback record.
              \E lock \in key_lock[pk] :
                /\ lock.ts = start_ts
                /\ lock.type = "lock_key"
                /\ req.resolving_pessimistic_lock = TRUE
            THEN
              /\ key_lock' = [key_lock EXCEPT ![pk] = {}]
              /\ SendResp({[type |-> "check_txn_status_resp",
                            start_ts |-> start_ts,
                            action |-> "pessimistic_rollback"]})
              /\ UNCHANGED <<msg_vars, key_data, key_write, client_vars, next_ts>>
            ELSE
              /\ rollback(pk, start_ts)
              /\ SendReqs({[type |-> "resolve_rollbacked",
                            start_ts |-> start_ts,
                            primary |-> pk]})
              /\ SendResp([type |-> "check_txn_status_resp",
                            start_ts |-> start_ts,
                            action |-> "rollbacked"])
              /\ UNCHANGED <<client_vars, next_ts>>
          \/
            \* Push min_commit_ts
            \E lock \in key_lock[pk] :
              /\ key_lock' = [key_lock EXCEPT ![pk] = {[ts |-> lock.ts,
                                                       type |-> lock.type,
                                                       primary |-> lock.primary,
                                                       min_commit_ts |-> caller_start_ts]}]
              /\ SendResp([type |-> "check_txn_status_resp",
                            start_ts |-> start_ts,
                            action |-> "min_commit_ts_pushed"])
              /\ UNCHANGED <<req_msgs, key_data, key_write, client_vars, next_ts>>
          \* Lock not found or start_ts on the lock mismatches.
          ELSE
            IF committed /= {} THEN
              /\ SendReqs({[type |-> "resolve_committed",
                            start_ts |-> start_ts,
                            primary |-> pk,
                            commit_ts |-> w.ts] : w \in committed})
              /\ SendResp([type |-> "check_txn_status_resp",
                            start_ts |-> start_ts,
                            action |-> "committed"])
              /\ UNCHANGED <<client_vars, key_vars, next_ts>>
            ELSE IF req.resolving_pessimistic_lock = TRUE THEN
              /\ SendResp({[type |-> "check_txn_status_resp",
                            start_ts |-> start_ts,
                            action |-> "lock_not_exist_do_nothing"]})
              /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>
            ELSE
              /\ rollback(pk, start_ts)
              /\ SendReqs({[type |-> "resolve_rollbacked",
                            start_ts |-> start_ts,
                            primary |-> pk]})
              /\ SendResp([type |-> "check_txn_status_resp",
                            start_ts |-> start_ts,
                            action |-> "rollbacked"])
              /\ UNCHANGED <<client_vars, next_ts>>

ServerResolveCommitted ==
  \E req \in req_msgs :
    /\ req.type = "resolve_committed"
    /\ LET
        start_ts == req.start_ts
       IN
        \E k \in KEY:
          \E l \in key_lock[k] :
            /\ l.primary = req.primary
            /\ l.ts = start_ts
            /\ commit(k, start_ts, req.commit_ts)
            /\ UNCHANGED <<msg_vars, client_vars, key_data, next_ts>>

ServerResolveRollbacked ==
  \E req \in req_msgs :
    /\ req.type = "resolve_rollbacked"
    /\ LET
        start_ts == req.start_ts
       IN
        \E k \in KEY:
          \E l \in key_lock[k] :
            /\ l.primary = req.primary
            /\ l.ts = start_ts
            /\ rollback(k, start_ts)
            /\ UNCHANGED <<msg_vars, client_vars, next_ts>>
-----------------------------------------------------------------------------
\* Specification

Init == 
  /\ next_ts = 1
  /\ req_msgs = {}
  /\ resp_msgs = {}
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_key = [c \in CLIENT |-> [locking |-> {}, prewriting |-> {}]]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> NoneTs,
                                    commit_ts |-> NoneTs,
                                    for_update_ts |-> NoneTs,
                                    min_commit_ts |-> NoneTs]]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_data = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> {}]

Next ==
  \/ \E c \in OPTIMISTIC_CLIENT :
        \/ ClientReadKey(c)
        \/ ClientPrewriteOptimistic(c)
        \/ ClientPrewrited(c)
        \/ ClientCommit(c)
  \/ \E c \in PESSIMISTIC_CLIENT :
        \/ ClientReadKey(c)
        \/ ClientLockKey(c)
        \/ ClientLockedKey(c)
        \/ ClientRetryLockKey(c)
        \/ ClientPrewritePessimistic(c)
        \/ ClientPrewrited(c)
        \/ ClientCommit(c)
  \/ ServerLockKey
  \/ ServerPrewritePessimistic
  \/ ServerPrewriteOptimistic
  \/ ServerCommit
  \/ ServerCleanupStaleLock
  \/ ServerCheckTxnStatus
  \/ ServerResolveCommitted
  \/ ServerResolveRollbacked

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
\* Consistency Invariants

\* Check whether there is a "write" record in key_write[k] corresponding
\* to start_ts.
keyCommitted(k, start_ts) ==
  \E w \in key_write[k] : 
    /\ w.start_ts = start_ts
    /\ w.type = "write"

\* A transaction can't be both committed and aborted.
UniqueCommitOrAbort ==
  \A resp, resp2 \in resp_msgs :
    (resp.type = "committed") /\ (resp2.type = "commit_aborted") =>
      resp.start_ts /= resp2.start_ts

\* If a transaction is committed, the primary key must be committed and
\* the secondary keys of the same transaction must be either committed
\* or locked.
CommitConsistency ==
  \A resp \in resp_msgs :
    (resp.type = "committed") =>
      \E c \in CLIENT :
        /\ client_ts[c].start_ts = resp.start_ts
        \* Primary key must be committed
        /\ keyCommitted(CLIENT_PRIMARY[c], resp.start_ts)
        \* Secondary key must be either committed or locked by the
        \* start_ts of the transaction.
        /\ \A k \in CLIENT_KEY[c] :
            (~ \E l \in key_lock[k] : l.ts = resp.start_ts) =
              keyCommitted(k, resp.start_ts)

\* If a transaction is aborted, all key of that transaction must be not
\* committed.
AbortConsistency ==
  \A resp \in resp_msgs :
    (resp.type = "commit_aborted") =>
      \A c \in CLIENT :
        (client_ts[c].start_ts = resp.start_ts) =>
          ~ keyCommitted(CLIENT_PRIMARY[c], resp.start_ts)

\* For each write, the commit_ts should be strictly greater than the
\* start_ts and have data written into key_data[k].  For each rollback,
\* the commit_ts should equals to the start_ts.
WriteConsistency ==
  \A k \in KEY :
    \A w \in key_write[k] :
      \/ /\ w.type = "write"
         /\ w.ts > w.start_ts
         /\ w.start_ts \in key_data[k]
      \/ /\ w.type = "rollback"
         /\ w.ts = w.start_ts

\* When the lock exists, there can't be a corresponding commit record,
\* vice versa.
UniqueLockOrWrite ==
  \A k \in KEY :
    \A l \in key_lock[k] :
      \A w \in key_write[k] :
        w.start_ts /= l.ts

\* For each key, ecah record in write column should have a unique start_ts.
UniqueWrite ==
  \A k \in KEY :
    \A w, w2 \in key_write[k] :
      (w.start_ts = w2.start_ts) => (w = w2)
-----------------------------------------------------------------------------
\* Snapshot Isolation

\* Asserts that next_ts is monotonically increasing.
NextTsMonotonicity == [][next_ts' >= next_ts]_vars

\* Asserts that no msg would be deleted once sent.
MsgMonotonicity ==
  /\ [][\A req \in req_msgs : req \in req_msgs']_vars
  /\ [][\A resp \in resp_msgs : resp \in resp_msgs']_vars

\* Asserts that all messages sent should have ts less than next_ts.
MsgTsConsistency ==
  /\ \A req \in req_msgs :
      /\ req.start_ts <= next_ts
      /\ req.type \in {"commit", "resolve_committed"} =>
          req.commit_ts <= next_ts
  /\ \A resp \in resp_msgs : resp.start_ts <= next_ts

\* SnapshotIsolation is implied from the following assumptions (but is not
\* necessary) because SnapshotIsolation means that: 
\*  (1) Once a transaction is committed, all keys of the transaction should
\*      be always readable or have a lock on secondary keys(eventually readable).
\*    PROOF BY CommitConsistency, MsgMonotonicity
\*  (2) For a given transaction, all transaction that commits after that 
\*      transaction should have greater commit_ts than the next_ts at the
\*      time that the given transaction commits, so as to be able to
\*      distinguish the transactions that have committed before and after
\*      from all transactions that preserved by (1).
\*    PROOF BY NextTsConsistency, MsgTsConsistency
\*  (3) All aborted transactions would be always not readable.
\*    PROOF BY AbortConsistency, MsgMonotonicity
SnapshotIsolation == /\ CommitConsistency
                     /\ AbortConsistency
                     /\ NextTsMonotonicity
                     /\ MsgMonotonicity
                     /\ MsgTsConsistency
-----------------------------------------------------------------------------
THEOREM Safety ==
  Spec => [](/\ TypeOK
             /\ UniqueCommitOrAbort
             /\ CommitConsistency
             /\ AbortConsistency
             /\ WriteConsistency
             /\ UniqueLockOrWrite
             /\ UniqueWrite
             /\ SnapshotIsolation)
=============================================================================
