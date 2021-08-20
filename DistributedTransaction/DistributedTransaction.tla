----------------------- MODULE DistributedTransaction -----------------------
EXTENDS Integers, FiniteSets, TLC

\* The set of all keys.
CONSTANTS KEY

\* The sets of optimistic clients and pessimistic clients.
CONSTANTS OPTIMISTIC_CLIENT, PESSIMISTIC_CLIENT
CLIENT == PESSIMISTIC_CLIENT \union OPTIMISTIC_CLIENT

CONSTANTS ASYNC_CLIENT
ASSUME ASYNC_CLIENT \in SUBSET CLIENT

CONSTANTS CLIENT_READ_KEY, CLIENT_WRITE_KEY
CLIENT_KEY == [c \in CLIENT |-> CLIENT_READ_KEY[c] \union CLIENT_WRITE_KEY[c]]

\* CLIENT_PRIMARY is the primary key of each client.
CONSTANTS CLIENT_PRIMARY

\* Pessimistic clients can't read a key without writing it and commit it,
\* and pessimistic client read the keys while acquiring pessimistic locks
\* so the CLIENT_READ_KEY for pessimistic clients should be empty.
ASSUME \A c \in PESSIMISTIC_CLIENT: CLIENT_READ_KEY[c] = {}

ASSUME \A c \in CLIENT: CLIENT_KEY[c] \subseteq KEY
ASSUME \A c \in CLIENT: CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

\* The algorithm is easier to understand in terms of the set of msgs of
\* all messages that have ever been sent. A more accurate model would use
\* one or more variables to represent the messages actually in transit,
\* and it would include actions representing message loss and duplication
\* as well as message receipt.
\*
\* In the current spec, there is no need to model message loss because we
\* are mainly concerned with the algorithm's safety property. The safety
\* part of the spec says only what messages may be received and does not
\* assert that any message actually is received. Thus, there is no
\* difference between a lost message and one that is never received.
VARIABLES req_msgs
VARIABLES resp_msgs

\* key_data[k] is the set of multi-version data of the key. Since we
\* don't care about the concrete value of data, a start_ts is sufficient
\* to represent one data version.
VARIABLES key_data
\* key_lock[k] is the set of lock (zero or one element). A lock is of a
\* record of [ts: start_ts, primary: key, type: lock_type]. If primary
\* equals to k, it is a primary lock, otherwise secondary lock. lock_type
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
\* It's a record of [ts, start_ts, type, [protected]]. type can be either
\* "commit" or "rollback". ts represents the commit_ts of "commit" record.
\* Otherwise, ts equals to start_ts on "rollback" record. "rollback"
\* record has an additional protected field. protected signifies the
\* rollback record would not be collapsed.
VARIABLES key_write

\* max_ts of keys, read to keys updates it.
VARIABLES key_max_ts

\* client_stage[c] indicates the current transaction stage of client c.
VARIABLES client_stage
\* client_ts[c] is a record of [start_ts, commit_ts, for_update_ts, min_commit_ts].
\* Fields are all initialized to NoneTs.
VARIABLES client_ts
\* client_key[c] is a record of [reading: {key}, locking: {key}, prewriting: {key}].
\* Hereby, "reading" denotes the keys that the optimistic client is reading,
\* "locking" denotes the keys that the pessimistic client is acquiring for pessimistic
\* locks, and "prewriting" denotes the keys that are waiting for prewrite success.
VARIABLES client_key
\* client_read[c][k] stores the value that the client has read from server for
\* key `k` (by optimsitic read or pessimistic lock key). This is used for checking
\* snapshot isolation.
VARIABLES client_read

\* next_ts is a globally monotonically increasing integer, representing
\* the virtual clock of transactions. In practice, the variable is
\* maintained by PD, the time oracle of a cluster.
VARIABLES next_ts

msg_vars == <<req_msgs, resp_msgs>>
client_vars == <<client_stage, client_ts, client_key, client_read>>
key_vars == <<key_data, key_lock, key_write, key_max_ts>>
vars == <<msg_vars, client_vars, key_vars, next_ts>>

SendReq(msg) == req_msgs' = req_msgs \union {msg}
SendReqs(msgs) == req_msgs' = req_msgs \union msgs
SendResp(msg) == resp_msgs' = resp_msgs \union {msg}
SendResps(msgs) == resp_msgs' = resp_msgs \union msgs
-----------------------------------------------------------------------------
\* Type Definitions

\* Timestamp for transactions.
Ts == Nat \ {0}
NoneTs == 0

\* Represents the data version read from TiKV. NoneTs means that the value is empty.
ValueTs == Ts \union {NoneTs}

\* The messages that sent from client to the server.
ReqMessages ==
          [start_ts : Ts, primary : KEY, type : {"lock_key"}, key : KEY,
            for_update_ts : Ts]
  \union  [start_ts : Ts, primary : KEY, type : {"read_optimistic"}, key : KEY]
  \union  [start_ts : Ts, primary : KEY, type : {"prewrite_optimistic"}, key : KEY]
  \union  [start_ts : Ts, primary : KEY, type : {"async_prewrite_optimistic"},
            key : KEY, all_keys : SUBSET KEY]
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
  \union  [start_ts : Ts, caller_start_ts : Ts \union {NoneTs}, primary : KEY, type : {"check_txn_status"},
           resolving_pessimistic_lock : BOOLEAN]

\* In this spec, the responses from the server to the client are modeled differently from the requests.
\* A response is modeled as a direct call to client handling function which makes the client states and
\* the server states change in atomic.
\*
\* This is ok because, different from requests, which may be duplicated, delayed, or lost, the response
\* can only be lost or delayed. Every client handling function will have a branch that the response
\* is simply ignored, in order to simulate losing the response. Still, we can not simulate the delaying
\* situation, but the client should (we thing) be ok with the delayed response since the client only
\* handles the response at the matching stage (e.g. "reading", "locking", "prewriting"), and every
\* client handling function only changes the client state to one key and leaving the state to other keys
\* untouched, which makes the order of receiving the response to different keys is irrelevant.
\*
\* One more draw back is that, a delayed resent request to server may result in a call the client
\* handling function, which is impossible in real-world because the client must drop the previous
\* connection before retry, in other words, the client is only possible to recieve and to handle the
\* response to the request it last sent. We overcome this by checking whether the client is in the right
\* stage to handle the response. But still, the model will face to some response to the resent resquest
\* for the same client stage. However, the model has just been tested against more but no less cases
\* comparing to the real-world, and is still passing the check.
DirectRespMessages ==
          [start_ts : Ts, type : {"read_optimistic_succeed"}, key : KEY, value_ts : ValueTs]
  \union  [start_ts : Ts, type : {"lock_key_succeed"}, key : KEY, for_update_ts : Ts, value_ts : ValueTs]
  \union  [start_ts : Ts, type : {"key_is_locked"}, key : KEY, lock_primary: KEY, lock_ts : Ts]
  \union  [start_ts : Ts, type : {"lock_key_failed_write_conflict"}, key : KEY, latest_commit_ts : Ts]
  \union  [start_ts : Ts, type : {"prewrited"}, key : KEY]
  \union  [start_ts : Ts, type : {"commit_ts_expired"}, min_commit_ts : Ts]

\* The responses defined in RespMessages will not be handled by the client in this spec, because they all
\* drive the transaction the an end. The messages defined here are used to record the history, in order to
\* check the invariants later defined in the spec (e.g. TiKV server should never has responded a transcation
\* committed while it has also responded the transaction aborted).
RespMessages == [start_ts : Ts, type : {"committed",
                                        "commit_aborted",
                                        "lock_key_aborted",
                                        "prewrite_aborted"}]

TypeOK == /\ req_msgs \in SUBSET ReqMessages
          /\ resp_msgs \in SUBSET RespMessages
          /\ key_data \in [KEY -> SUBSET Ts]
          /\ key_lock \in [KEY -> SUBSET ([start_ts : Ts,
                                           primary : KEY,
                                           \* As defined above, Ts == Nat \ 0, here we use 0
                                           \* to indicates that there's no min_commit_ts limit
                                           \* becuase every valid commit ts is larger than 0.
                                           min_commit_ts : Ts \union {NoneTs},
                                           type : {"prewrite_optimistic",
                                                   "prewrite_pessimistic",
                                                   "lock_key"}]
                                   \union [start_ts : Ts,
                                           primary : KEY,
                                           min_commit_ts : Ts \union {NoneTs},
                                           type : {"async"},
                                           all_keys : SUBSET KEY])]
          /\ key_write \in [KEY -> SUBSET (
                      [ts : Ts, start_ts : Ts, type : {"commit"}]
              \union  [ts : Ts, start_ts : Ts, type : {"rollback"}, protected : BOOLEAN])]
          /\ key_max_ts \in [KEY -> Ts \union {NoneTs}]
          \* At most one lock in key_lock[k]
          /\ \A k \in KEY: Cardinality(key_lock[k]) <= 1
          /\ client_stage \in [CLIENT -> {"init", "reading", "locking", "prewriting", "committing"}]
          /\ client_ts \in [CLIENT -> [start_ts : Ts \union {NoneTs},
                                       commit_ts : Ts \union {NoneTs},
                                       for_update_ts : Ts \union {NoneTs}]]
          /\ client_key \in [CLIENT -> [reading : SUBSET KEY, locking : SUBSET KEY, prewriting : SUBSET KEY]]
          /\ client_read \in [CLIENT -> [KEY ->
                                                [type : {"not_read_yet"}]
                                         \union [type : {"read_succeed"}, value_ts : ValueTs]]]
          /\ \A c \in CLIENT: client_key[c].locking \intersect client_key[c].prewriting = {}
          /\ next_ts \in Ts
-----------------------------------------------------------------------------
\* Client Actions

\* Once the get request is sent, it exist permanently in the req_msgs.
ClientReadOptimistic(c) ==
  /\ client_stage[c] = "init"
  /\ client_stage' = [client_stage EXCEPT ![c] = "reading"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ client_key' = [client_key EXCEPT ![c].reading = CLIENT_READ_KEY[c]]
  /\ next_ts' = next_ts + 1
  /\ SendReqs({[type |-> "read_optimistic",
                start_ts |-> client_ts'[c].start_ts,
                primary |-> CLIENT_PRIMARY[c],
                key |-> k] : k \in CLIENT_READ_KEY[c]})
  /\ UNCHANGED <<resp_msgs, client_read, key_vars>>

add_client_read_history(c, k, value_ts) ==
  client_read' = [client_read EXCEPT ![c][k] = [type |-> "read_succeed", value_ts |-> value_ts]]

ClientReadOptimisticSucceed(resp) ==
  /\ Assert(resp.type = "read_optimistic_succeed", "Message Type Error")
  /\ \/ UNCHANGED <<req_msgs, client_vars, next_ts>>
     \/ \E c \in CLIENT:
          /\ client_ts[c].start_ts = resp.start_ts
          /\ client_stage[c] = "reading"
          /\ resp.key \in client_key[c].reading
          /\ client_key' = [client_key EXCEPT ![c].reading = @ \ {resp.key}]
          /\ add_client_read_history(c, resp.key, resp.value_ts)
          /\ UNCHANGED <<req_msgs, client_ts, client_stage, next_ts>>

ClientResolveLock(resp) ==
  /\ Assert(resp.type = "key_is_locked", "Message Type Error")
  /\ \/ UNCHANGED <<req_msgs, client_vars, next_ts>>
     \/ \E c \in CLIENT:
          /\ client_ts[c].start_ts = resp.start_ts
          /\ client_stage[c] = "locking"
          /\ resp.key \in client_key[c].locking
          /\ SendReq([type |-> "check_txn_status",
                      start_ts |-> resp.lock_ts,
                      caller_start_ts |-> NoneTs,
                      primary |-> resp.lock_primary,
                      resolving_pessimistic_lock |-> resp.lock_type = "lock_key"])
          /\ UNCHANGED <<client_vars, key_max_ts, next_ts>>

ClientLockKey(c) ==
  /\ client_stage[c] = "init"
  /\ client_stage' = [client_stage EXCEPT ![c] = "locking"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts, ![c].for_update_ts = next_ts]
  /\ client_key' = [client_key EXCEPT ![c].locking = CLIENT_WRITE_KEY[c]]
  /\ next_ts' = next_ts + 1
  \* For pessimistic clients assume we need to acquire pessimistic locks for all keys.
  /\ SendReqs({[type |-> "lock_key",
                start_ts |-> client_ts'[c].start_ts,
                primary |-> CLIENT_PRIMARY[c],
                key |-> k,
                for_update_ts |-> client_ts'[c].for_update_ts] : k \in CLIENT_WRITE_KEY[c]})
  /\ UNCHANGED <<resp_msgs, client_read, key_vars>>

ClientLockKeySucceed(resp) ==
  /\ Assert(resp.type = "lock_key_succeed", "Message Type Error")
  /\ \/ UNCHANGED <<req_msgs, client_vars, next_ts>>
     \/ \E c \in CLIENT:
          /\ client_ts[c].start_ts = resp.start_ts
          \* The client guarantees that it will never recieve a response for
          \* a previously sent lock_key request with smaller for_update_ts, which
          \* may carry a bad value that breaks the snapshot isolation. This
          \* guarantee holds because the previous gRPC connection must have closed.
          /\ client_ts[c].for_update_ts = resp.for_update_ts
          /\ client_stage[c] = "locking"
          /\ resp.key \in client_key[c].locking
          /\ client_key' = [client_key EXCEPT ![c].locking = @ \ {resp.key}]
          /\ add_client_read_history(c, resp.key, resp.value_ts)
          /\ UNCHANGED <<req_msgs, client_ts, client_stage, key_max_ts, next_ts>>

ClientLockKeyFailedWriteConflict(resp) ==
  /\ Assert(resp.type = "lock_key_failed_write_conflict", "Message Type Error")
  /\ \/ UNCHANGED <<req_msgs, client_vars, next_ts>>
     \/ \E c \in CLIENT:
          /\ client_ts[c].start_ts = resp.start_ts
          /\ client_stage[c] = "locking"
          /\ resp.key \in client_key[c].locking
          /\ resp.latest_commit_ts > client_ts[c].for_update_ts
          /\ client_ts' = [client_ts EXCEPT ![c].for_update_ts = next_ts]
          /\ next_ts' = next_ts + 1
          /\ SendReqs({[type |-> "lock_key",
                        start_ts |-> client_ts'[c].start_ts,
                        primary |-> CLIENT_PRIMARY[c],
                        key |-> resp.key,
                        for_update_ts |-> client_ts'[c].for_update_ts]})
          /\ UNCHANGED <<client_stage, client_key, client_read, key_max_ts>>

ClientPrewriteOptimistic(c) ==
  /\ client_stage[c] = "reading"
  /\ client_key[c].reading = {}
  /\ client_stage' = [client_stage EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_WRITE_KEY[c]]
  /\ IF c \in ASYNC_CLIENT 
     THEN
       /\ SendReqs({[type |-> "async_prewrite_optimistic",
                     start_ts |-> client_ts[c].start_ts,
                     primary |-> CLIENT_PRIMARY[c],
                     key |-> k,
                     all_keys |-> CLIENT_WRITE_KEY[c]] : k \in CLIENT_WRITE_KEY[c]})
       /\ UNCHANGED <<resp_msgs, client_ts, client_read, key_vars, next_ts>>
     ELSE
       /\ SendReqs({[type |-> "prewrite_optimistic",
                     start_ts |-> client_ts[c].start_ts,
                     primary |-> CLIENT_PRIMARY[c],
                     key |-> k] : k \in CLIENT_WRITE_KEY[c]})
       /\ UNCHANGED <<resp_msgs, client_ts, client_read, key_vars, next_ts>>

ClientPrewritePessimistic(c) ==
  /\ client_stage[c] = "locking"
  /\ client_key[c].locking = {}
  /\ client_stage' = [client_stage EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_WRITE_KEY[c]]
  /\ IF c \in ASYNC_CLIENT
     THEN
       /\ SendReqs({[type |-> "prewrite_pessimistic",
                     start_ts |-> client_ts[c].start_ts,
                     primary |-> CLIENT_PRIMARY[c],
                     key |-> k,
                     all_keys |-> CLIENT_WRITE_KEY[c]] : k \in CLIENT_WRITE_KEY[c]})
       /\ UNCHANGED <<resp_msgs, client_ts, client_read, key_vars, next_ts>>
     ELSE
       /\ SendReqs({[type |-> "prewrite_pessimistic",
                     start_ts |-> client_ts[c].start_ts,
                     primary |-> CLIENT_PRIMARY[c],
                     key |-> k] : k \in CLIENT_WRITE_KEY[c]})
       /\ UNCHANGED <<resp_msgs, client_ts, client_read, key_vars, next_ts>>

ClientPrewrited(resp) ==
  /\ Assert(resp.type = "prewrited", "Message Type Error")
  /\ \/ UNCHANGED <<req_msgs, client_vars, next_ts>>
     \/ \E c \in CLIENT:
          /\ client_ts[c].start_ts = resp.start_ts
          /\ client_stage[c] = "prewriting"
          /\ resp.key \in client_key[c].prewriting
          /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {resp.key}]
          /\ UNCHANGED <<req_msgs, client_ts, client_stage, client_read, key_max_ts, next_ts>>

ClientCommit(c) ==
  /\ client_stage[c] = "prewriting"
  /\ client_key[c].prewriting = {}
  /\ client_stage' = [client_stage EXCEPT ![c] = "committing"]
  /\ IF c \in ASYNC_CLIENT
     THEN
       \* TODO: update the async version
       /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
       /\ next_ts' = next_ts + 1
       /\ SendReqs({[type |-> "commit",
                     start_ts |-> client_ts'[c].start_ts,
                     primary |-> CLIENT_PRIMARY[c],
                     commit_ts |-> client_ts'[c].commit_ts]})
       /\ UNCHANGED <<resp_msgs, key_vars, client_key, key_max_ts, client_read>>
     ELSE
       /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
       /\ next_ts' = next_ts + 1
       /\ SendReqs({[type |-> "commit",
                     start_ts |-> client_ts'[c].start_ts,
                     primary |-> CLIENT_PRIMARY[c],
                     commit_ts |-> client_ts'[c].commit_ts]})
       /\ UNCHANGED <<resp_msgs, key_vars, client_key, key_max_ts, client_read>>

ClientRetryCommit(resp) ==
  /\ Assert(resp.type = "commit_ts_expired", "Message Type Error")
  /\ \/ UNCHANGED <<req_msgs, client_vars, next_ts>>
     \/ \E c \in CLIENT:
          /\ client_ts[c].start_ts = resp.start_ts
          /\ client_stage[c] = "commiting"
          /\ client_ts[c].commit_ts < resp.min_commit_ts
          /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
          /\ next_ts' = next_ts + 1
          /\ SendReqs({[type |-> "commit",
                        start_ts |-> client_ts'[c].start_ts,
                        primary |-> CLIENT_PRIMARY[c],
                        commit_ts |-> client_ts'[c].commit_ts]})
          /\ UNCHANGED <<client_stage, client_key, client_read, key_max_ts>>
-----------------------------------------------------------------------------
\* Server Actions

\* Write the write column and unlock the lock iff the lock exists.
unlock_key(k) ==
  /\ key_lock' = [key_lock EXCEPT ![k] = {}]

commit(pk, start_ts, commit_ts) ==
  \E l \in key_lock[pk] :
    /\ l.start_ts = start_ts
    /\ unlock_key(pk)
    /\ key_write' = [key_write EXCEPT ![pk] = @ \union {[ts |-> commit_ts,
                                                         type |-> "commit",
                                                         start_ts |-> start_ts]}]

\* Rollback the transaction that starts at start_ts on key k.
rollback(k, start_ts) ==
  LET
    \* Rollback record on the primary key of a pessimistic transaction
    \* needs to be protected from being collapsed.
    protected == \E l \in key_lock[k] :
                  /\ l.start_ts = start_ts
                  /\ l.primary = k
                  /\ l.type \in {"lock_key", "prewrite_pessimistic"}
  IN
    \* If a lock exists and has the same ts, unlock it.
    /\ IF \E l \in key_lock[k]: l.start_ts = start_ts
       THEN unlock_key(k)
       ELSE UNCHANGED key_lock
    /\ key_data' = [key_data EXCEPT ![k] = @ \ {start_ts}]
    /\ IF ~ \E w \in key_write[k]: w.ts = start_ts
       THEN
            key_write' = [key_write EXCEPT
              ![k] =
                \* collapse rollback
                (@ \ {w \in @: w.type = "rollback" /\ ~ w.protected /\ w.ts < start_ts})
                \* write rollback record
                \union {[ts |-> start_ts,
                        start_ts |-> start_ts,
                        type |-> "rollback",
                        protected |-> protected]}]
       ELSE
          UNCHANGED <<key_write>>

\* In optimistic transaction, read_ts is start_ts, and, in pessimistic transaction,
\* read_ts is for_update_ts.
find_readable_commit(k, read_ts) ==
  LET
    all_commits_before_read_ts == {w \in key_write[k]: w.type = "commit" /\ w.ts <= read_ts}
    latest_commit_before_read_ts ==
      {w \in all_commits_before_read_ts :
        \A w2 \in all_commits_before_read_ts :
          w.ts >= w2.ts}
  IN
    latest_commit_before_read_ts

\* Optimistic read successfully. Return `value_ts = NoneTs` if the value is empty.
respond_read_succeed(k, start_ts) ==
  LET
    readable_commit == find_readable_commit(k, start_ts)
  IN
    /\ key_max_ts' = [key_max_ts EXCEPT ![k] = next_ts - 1]
    /\ \/ /\ readable_commit = {}
          /\ ClientReadOptimisticSucceed([start_ts |-> start_ts,
                                          type |-> "read_optimistic_succeed",
                                          key |-> k,
                                          value_ts |-> NoneTs])
       \/ \E committed_record \in readable_commit:
           /\ ClientReadOptimisticSucceed([start_ts |-> start_ts,
                                           type |-> "read_optimistic_succeed",
                                           key |-> k,
                                           value_ts |-> committed_record.ts])

\* Pessimistic lock successfully. Return `value_ts = NoneTs` if the value is empty.
respond_lock_key_succeed(k, start_ts, for_update_ts) ==
  LET
    readable_commit == find_readable_commit(k, for_update_ts)
  IN
    \/ /\ readable_commit = {}
       /\ ClientLockKeySucceed([start_ts |-> start_ts,
                                type |-> "lock_key_succeed",
                                key |-> k,
                                for_update_ts |-> for_update_ts,
                                value_ts |-> NoneTs])
    \/ \E committed_record \in readable_commit:
        /\ ClientLockKeySucceed([start_ts |-> start_ts,
                                 type |-> "lock_key_succeed",
                                 key |-> k,
                                 for_update_ts |-> for_update_ts,
                                 value_ts |-> committed_record.ts])

ServerReadKey ==
  \E req \in req_msgs :
    /\ req.type = "read_optimistic"
    /\ \E c \in CLIENT :
      /\ client_ts[c].start_ts = req.start_ts
      /\ LET
           k == req.key
           start_ts == req.start_ts
         IN
           \* If the lock belongs to the transaction sending the request, or
           \* if it's a pessimistic lock, return read succeed.
           \*
           \* The reason why pessimistic lock will not block the read is that
           \* the owner transaction of the pessimistic lock is impossible to
           \* commit the key with a commit_ts smaller than req.start_ts because
           \* the owner transaction must get commit_ts after all prewrites have
           \* completed which is apperently not done since the lock type is
           \* not a prewrite lock.
           /\ IF \/ key_lock[k] = {}
                 \/ \E l \in key_lock[k]: l.type = "lock_key" \/ l.start_ts = start_ts
              THEN
                /\ respond_read_succeed(k, start_ts)
                /\ UNCHANGED <<resp_msgs, key_data, key_lock, key_write, next_ts>>
              ELSE
                \E l \in key_lock[k]:
                  /\ ClientResolveLock([start_ts |-> start_ts,
                                        type |-> "key_is_locked",
                                        key |-> k,
                                        lock_primary |-> l.primary,
                                        lock_ts |-> l.start_ts])
                  /\ UNCHANGED <<resp_msgs, key_vars>>

ServerLockKey ==
  \E req \in req_msgs :
    /\ req.type = "lock_key"
    /\ LET
        k == req.key
        start_ts == req.start_ts
        for_update_ts == req.for_update_ts
       IN
        \* Pessimistic lock is allowed only if no stale lock exists. If
        \* there is one, wait until ClientCheckTxnStatus to clean it up.
        \/ /\ key_lock[k] = {}
           /\ LET
                all_commits == {w \in key_write[k]: w.type = "commit"}
                latest_commit == {w \in all_commits: \A w2 \in all_commits: w.ts >= w2.ts}
              IN
                IF \E w \in key_write[k]: w.start_ts = start_ts /\ w.type = "rollback"
                THEN
                  \* If corresponding rollback record is found, which
                  \* indicates that the transcation is rollbacked, abort the
                  \* transaction.
                  /\ SendResp([start_ts |-> start_ts, type |-> "lock_key_aborted"])
                  /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>
                ELSE
                  \* Acquire pessimistic lock only if for_update_ts of req
                  \* is greater or equal to the latest "commit" record.
                  \* Because if the latest record is "commit", it means that
                  \* a new version is committed after for_update_ts, which
                  \* violates Read Committed guarantee.
                  \/ /\ ~ \E w \in latest_commit: w.ts > req.for_update_ts
                     /\ key_lock' = [key_lock EXCEPT ![k] = {[start_ts |-> start_ts,
                                                              primary |-> req.primary,
                                                              min_commit_ts |-> NoneTs,
                                                              type |-> "lock_key"]}]
                     /\ respond_lock_key_succeed(k, start_ts, for_update_ts)
                     /\ UNCHANGED <<resp_msgs, key_data, key_write, key_max_ts>>
                  \* Otherwise, reject the request and let client to retry
                  \* with new for_update_ts.
                  \/ \E w \in latest_commit :
                      /\ w.ts > req.for_update_ts
                      /\ ~ \E w2 \in all_commits: w2.start_ts = req.start_ts
                      /\ ClientLockKeyFailedWriteConflict([start_ts |-> start_ts,
                                                          type |-> "lock_key_failed_write_conflict",
                                                          key |-> k,
                                                          latest_commit_ts |-> w.ts])
                      /\ UNCHANGED <<resp_msgs, key_vars>>
        \* Lock exsits
        \/ \E l \in key_lock[k]:
            IF l.start_ts = start_ts
            THEN
              /\ respond_lock_key_succeed(k, start_ts, for_update_ts)
              /\ UNCHANGED <<resp_msgs, key_vars>>
            ELSE
              /\ ClientResolveLock([start_ts |-> start_ts,
                                    type |-> "key_is_locked",
                                    key |-> k,
                                    lock_primary |-> l.primary,
                                    lock_ts |-> l.start_ts,
                                    lock_type |-> l.type])
              /\ UNCHANGED <<resp_msgs, key_vars>>

ServerPrewriteOptimistic ==
  \E req \in req_msgs:
    /\ req.type = "prewrite_optimistic"
    /\ LET
        k == req.key
        start_ts == req.start_ts
       IN
        \/ /\ key_lock[k] = {}
           /\ IF \E w \in key_write[k]: w.start_ts = start_ts /\ w.type = "commit" THEN
                \* This is a duplicated prewrite request.
                UNCHANGED <<vars>>
              ELSE IF \/ \E w \in key_write[k]: w.start_ts = start_ts /\ w.type = "rollback"
                      \/ \E w \in key_write[k]: w.ts >= start_ts THEN
                \* This transacstion has been rollbacked or has write conflict.
                /\ SendResp([start_ts |-> start_ts, type |-> "prewrite_aborted"])
                /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>
              ELSE
                \* Prewrite the key.
                /\ key_lock' = [key_lock EXCEPT ![k] = {[start_ts |-> start_ts,
                                                         primary |-> req.primary,
                                                         type |-> "prewrite_optimistic",
                                                         min_commit_ts |-> NoneTs]}]
                /\ key_data' = [key_data EXCEPT ![k] = @ \union {start_ts}]
                /\ ClientPrewrited([start_ts |-> start_ts, type |-> "prewrited", key |-> k])
                /\ UNCHANGED <<resp_msgs, key_write, key_max_ts>>
        \/ \E l \in key_lock[k]:
            IF l.start_ts = start_ts
            THEN
              /\ ClientPrewrited([start_ts |-> start_ts, type |-> "prewrited", key |-> k])
              /\ UNCHANGED <<resp_msgs, key_vars>>
            ELSE
              \* Clean up the stale lock.
              /\ ClientResolveLock([start_ts |-> start_ts,
                                    type |-> "key_is_locked",
                                    key |-> k,
                                    lock_primary |-> l.primary,
                                    lock_ts |-> l.start_ts,
                                    lock_type |-> l.type])
              /\ UNCHANGED <<resp_msgs, key_vars>>

ServerPrewritePessimistic ==
  \E req \in req_msgs :
    /\ req.type = "prewrite_pessimistic"
    /\ LET
        k == req.key
        start_ts == req.start_ts
       IN
        \* Pessimistic prewrite is only allowed if pressimistic lock is
        \* acquired, or, if there's no lock, and no write record whose
        \* commit_ts >= start_ts, otherwise abort the transaction.
        IF
          \/ \E l \in key_lock[k] :
             /\ l.start_ts = start_ts
             /\ l.type = "lock_key"
          \/ /\ key_lock[k] = {}
             /\ ~ \E w \in key_write[k]: w.ts >= start_ts
        THEN
          /\ key_lock' = [key_lock EXCEPT ![k] = {[start_ts |-> start_ts,
                                                   primary |-> req.primary,
                                                   type |-> "prewrite_pessimistic",
                                                   min_commit_ts |-> NoneTs]}]
          /\ key_data' = [key_data EXCEPT ![k] = @ \union {start_ts}]
          /\ ClientPrewrited([start_ts |-> start_ts, type |-> "prewrited", key |-> k])
          /\ UNCHANGED <<resp_msgs, key_write, key_max_ts>>
        ELSE
          /\ SendResp([start_ts |-> start_ts, type |-> "prewrite_aborted"])
          /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>

ServerCommit ==
  \E req \in req_msgs:
    /\ req.type = "commit"
    /\ LET
        pk == req.primary
        start_ts == req.start_ts
       IN
        IF \E w \in key_write[pk]: w.start_ts = start_ts /\ w.type = "commit"
        THEN
          \* Key has already been committed. Do nothing.
          /\ SendResp([start_ts |-> start_ts, type |-> "committed"])
          /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>
        ELSE
          \/ \E l \in key_lock[pk]:
              IF l.start_ts = start_ts /\ ~ l.type = "lock_key"
              THEN
                IF req.commit_ts >= l.min_commit_ts
                THEN
                  \* Commit the key only if the prewrite lock exists and commit_ts is greater than
                  \* the min_commit_ts in the prewrite lock.
                  /\ commit(pk, start_ts, req.commit_ts)
                  /\ SendResp([start_ts |-> start_ts, type |-> "committed"])
                  /\ UNCHANGED <<req_msgs, client_vars, key_data, key_max_ts, next_ts>>
                ELSE
                  /\ ClientRetryCommit([start_ts |-> start_ts,
                                        type |-> "commit_ts_expired",
                                        min_commit_ts |-> l.min_commit_ts])
                  /\ UNCHANGED <<resp_msgs, key_vars>>
              ELSE
                /\ SendResp([start_ts |-> start_ts, type |-> "commit_aborted"])
                /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>
          \/ /\ key_lock[pk] = {}
             /\ SendResp([start_ts |-> start_ts, type |-> "commit_aborted"])
             /\ UNCHANGED <<req_msgs, client_vars, key_vars, next_ts>>

\* Found the matching lock.
check_txn_status_has_lock(lock, caller_start_ts, resolving_pessimistic_lock) ==
  LET
    start_ts == lock.start_ts
    pk == lock.primary
  IN
    \/ IF lock.type = "lock_key" /\ resolving_pessimistic_lock
      THEN
        \* Pessimistic lock will be unlocked directly without rollback record.
        /\ unlock_key(pk)
        /\ UNCHANGED <<msg_vars, key_data, key_write, key_max_ts, client_vars, next_ts>>
      ELSE
        /\ rollback(pk, start_ts)
        /\ SendReqs({[type |-> "resolve_rollbacked",
                      start_ts |-> start_ts,
                      primary |-> pk]})
        /\ UNCHANGED <<resp_msgs, client_vars, key_max_ts, next_ts>>
    \/
      \* Push min_commit_ts.
      /\ lock.min_commit_ts <= caller_start_ts
      /\ key_lock' = [key_lock EXCEPT ![pk] = {[start_ts |-> lock.start_ts,
                                                type |-> lock.type,
                                                primary |-> lock.primary,
                                                min_commit_ts |-> caller_start_ts + 1]}]
      /\ UNCHANGED <<msg_vars, key_data, key_write, key_max_ts, client_vars, next_ts>>

\* Lock not found or start_ts on the lock mismatches.
check_txn_status_missing_lock(start_ts, pk, resolving_pessimistic_lock) ==
  LET
    committed_record == {w \in key_write[pk]: w.start_ts = start_ts /\ w.type = "commit"}
  IN
    IF committed_record /= {} THEN
      /\ SendReqs({[type |-> "resolve_committed",
                    start_ts |-> start_ts,
                    primary |-> pk,
                    commit_ts |-> w.ts]: w \in committed_record})
      /\ UNCHANGED <<resp_msgs, client_vars, key_vars, next_ts>>
    ELSE IF resolving_pessimistic_lock = TRUE THEN
      UNCHANGED <<msg_vars, client_vars, key_vars, next_ts>>
    ELSE
      /\ rollback(pk, start_ts)
      /\ SendReqs({[type |-> "resolve_rollbacked",
                    start_ts |-> start_ts,
                    primary |-> pk]})
      /\ UNCHANGED <<resp_msgs, client_vars, key_max_ts, next_ts>>

\* Clean up the stale transaction by checking the status of the primary key.
\*
\* In practice, the transaction will be rolled back only if TTL on the lock is expired. But
\* because it is hard to model the TTL in TLA+ spec, the TTL is considered constantly expired
\* when ServerCheckTxnStatus is called.
\*
\* Moreover, TiKV will send a response `TxnStatus` to the client, and depending on the `TxnStatus`
\* the client will send `resolve_rollback` or `resolve_commit` to the secondary keys to clean up
\* stale locks on secondary keys. In the TLA+ spec, ServerCheckTxnStatus will not respond to the
\* client and instead TiKV will directly send `resolve_rollback` or `resolve_commit` message to
\* the server where the secondary keys are on, because the action of client sending resolve message
\* by proxying the `TxnStatus` from TiKV to other TiKV does not change the state of the client,
\* therefore is equal to directly sending resolve message from TiKV to TiKV directly.
ServerCheckTxnStatus ==
  \E req \in req_msgs :
    /\ req.type = "check_txn_status"
    /\ LET
        pk == req.primary
        start_ts == req.start_ts
       IN
        \/ \E l \in key_lock[pk]:
            IF start_ts = l.start_ts
            THEN
              check_txn_status_has_lock(l, req.caller_start_ts, req.resolving_pessimistic_lock)
            ELSE
              check_txn_status_missing_lock(start_ts, pk, req.resolving_pessimistic_lock)
        \/ /\ key_lock[pk] = {}
           /\ check_txn_status_missing_lock(start_ts, pk, req.resolving_pessimistic_lock)

ServerResolveCommitted ==
  \E req \in req_msgs :
    /\ req.type = "resolve_committed"
    /\ LET
        start_ts == req.start_ts
       IN
        \E k \in KEY:
          \E l \in key_lock[k] :
            /\ l.primary = req.primary
            /\ l.start_ts = start_ts
            /\ commit(k, start_ts, req.commit_ts)
            /\ UNCHANGED <<msg_vars, client_vars, key_data, key_max_ts, next_ts>>

ServerResolveRollbacked ==
  \E req \in req_msgs :
    /\ req.type = "resolve_rollbacked"
    /\ LET
        start_ts == req.start_ts
       IN
        \E k \in KEY:
          \E l \in key_lock[k] :
            /\ l.primary = req.primary
            /\ l.start_ts = start_ts
            /\ rollback(k, start_ts)
            /\ UNCHANGED <<msg_vars, client_vars, key_max_ts, next_ts>>
-----------------------------------------------------------------------------
\* Specification

Init ==
  /\ next_ts = 1
  /\ req_msgs = {}
  /\ resp_msgs = {}
  /\ client_stage = [c \in CLIENT |-> "init"]
  /\ client_key = [c \in CLIENT |-> [reading |-> {}, locking |-> {}, prewriting |-> {}]]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> NoneTs,
                                    commit_ts |-> NoneTs,
                                    for_update_ts |-> NoneTs]]
  /\ client_read = [c \in CLIENT |-> [k \in KEY |-> [type |-> "not_read_yet"]]]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_data = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> {}]
  /\ key_max_ts = [k \in KEY |-> NoneTs]

Next ==
  \/ \E c \in OPTIMISTIC_CLIENT:
      \/ ClientReadOptimistic(c)
      \/ ClientPrewriteOptimistic(c)
      \/ ClientCommit(c)
  \/ \E c \in PESSIMISTIC_CLIENT:
      \/ ClientLockKey(c)
      \/ ClientPrewritePessimistic(c)
      \/ ClientCommit(c)
  \/ ServerReadKey
  \/ ServerLockKey
  \/ ServerPrewritePessimistic
  \/ ServerPrewriteOptimistic
  \/ ServerCommit
  \/ ServerCheckTxnStatus
  \/ ServerResolveCommitted
  \/ ServerResolveRollbacked

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
\* Consistency Invariants

\* Check whether there is a "commit" record in key_write[k] corresponding
\* to start_ts.
keyCommitted(k, start_ts) ==
  \E w \in key_write[k] :
    /\ w.start_ts = start_ts
    /\ w.type = "commit"

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
        /\ \A k \in CLIENT_WRITE_KEY[c] :
            (~ \E l \in key_lock[k]: l.start_ts = resp.start_ts) =
              keyCommitted(k, resp.start_ts)

\* If a transaction is aborted, all key of that transaction must not be
\* committed.
AbortConsistency ==
  \A resp \in resp_msgs :
    (resp.type = "commit_aborted") =>
      \A c \in CLIENT :
        (client_ts[c].start_ts = resp.start_ts) =>
          ~ keyCommitted(CLIENT_PRIMARY[c], resp.start_ts)

\* For each write, the commit_ts should be strictly greater than the
\* start_ts and have data written into key_data[k]. For each rollback,
\* the commit_ts should equals to the start_ts.
WriteConsistency ==
  \A k \in KEY :
    \A w \in key_write[k] :
      \/ /\ w.type = "commit"
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
        w.start_ts /= l.start_ts

\* For each key, ecah record in write column should have a unique start_ts.
UniqueWrite ==
  \A k \in KEY :
    \A w, w2 \in key_write[k] :
      (w.start_ts = w2.start_ts) => (w = w2)
-----------------------------------------------------------------------------
\* Snapshot Isolation

\* Asserts that all messages sent should have ts less than next_ts.
MsgTsConsistency ==
  /\ \A req \in req_msgs :
      /\ req.start_ts <= next_ts
      /\ req.type \in {"commit", "resolve_committed"} =>
          req.commit_ts <= next_ts
  /\ \A resp \in resp_msgs: resp.start_ts <= next_ts

OptimisticReadSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT:
    \A k \in CLIENT_READ_KEY[c]:
      client_read[c][k].type = "read_succeed" =>
        LET
          readable_commit == find_readable_commit(k, client_ts[c].start_ts)
        IN
          \/ /\ readable_commit = {}
             /\ client_read[c][k].value_ts = NoneTs
          \/ \E committed_record \in readable_commit:
              client_read[c][k].value_ts = committed_record.ts

PessimisticReadSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT:
    (\E resp \in resp_msgs: resp.start_ts = client_ts[c].start_ts /\ resp.type = "committed") =>
      \A k \in CLIENT_WRITE_KEY[c]:
        client_read[c][k].type = "read_succeed" =>
          LET
            readable_commit == find_readable_commit(k, client_ts[c].for_update_ts)
          IN
            \/ /\ readable_commit = {}
               /\ client_read[c][k].value_ts = NoneTs
            \/ \E committed_record \in readable_commit:
                client_read[c][k].value_ts = committed_record.ts
-----------------------------------------------------------------------------
THEOREM Safety ==
  Spec => [](/\ TypeOK
             /\ UniqueCommitOrAbort
             /\ CommitConsistency
             /\ AbortConsistency
             /\ WriteConsistency
             /\ UniqueLockOrWrite
             /\ UniqueWrite
             /\ OptimisticReadSnapshotIsolation
             /\ PessimisticReadSnapshotIsolation
             /\ MsgTsConsistency)
=============================================================================
