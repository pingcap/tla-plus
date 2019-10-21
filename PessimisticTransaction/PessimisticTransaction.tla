----------------------- MODULE PessimisticTransaction -----------------------

EXTENDS Integers

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
\* key_last_read_ts[k] denotes the last read timestamp for key k, this
\* should be monotonic.
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

-----------------------------------------------------------------------------

Start(c) ==
  /\ client_state[c] = "init"
  /\ next_ts' = next_ts + 1
  /\ \E ks \in SUBSET KEY:
       \E primary \in ks:
         client_key' =
           [client_key EXCEPT 
             ![c] = [primary |-> primary,
                     secondary |-> ks \ {primary},
                     pessimistic |-> ks,
                     pending |-> ks]
           ]
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts']
  /\ UNCHANGED <<key_vars, msg>>

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

ClientOp(c) ==
  \/ Start(c)
      
Next == \E c \in CLIENT : ClientOp(c)

-----------------------------------------------------------------------------

NextTsTypeInv == next_ts \in Pos

ClientStateTypeInv ==
  client_state \in [
    CLIENT -> {"init", "working", "prewriting",
               "committing", "committed", "aborted"}
  ]
                               
ClientTsTypeInv ==
  client_ts \in
  [CLIENT -> [start_ts : Nat, for_update_ts: Nat, commit_ts : Nat]]
  
ClientKeyTypeInv ==
  \A c \in CLIENT:
    \/ client_state[c] = "init"
    \/ client_key[c] \in [primary: KEY,
                secondary: SUBSET KEY,
                pessimistic: SUBSET KEY,
                pending : SUBSET KEY
               ]
  
KeyDataTypeInv ==
  key_data \in [KEY -> SUBSET [ts: Pos]]

KeyLockTypeInv ==
  key_lock \in [KEY -> SUBSET [ts: Pos, for_update_ts: Nat, primary: KEY]]

KeyWriteTypeInv ==
  key_write \in [KEY -> 
    SUBSET [ts: Pos, type: {"write", "rollback"}, start_ts: Pos]
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
    [c: CLIENT, type: {"lock", "prewrite"}, key: KEY,
     start_ts: Pos, for_update_ts: Pos] \union
    [c: CLIENT, type: {"commit"}, key: KEY, commit_ts: Pos] \union
    [c: CLIENT, type: {"rollback"}, key: KEY]
  )                 
  
TypeInvariant ==
  /\ NextTsTypeInv
  /\ ClientStateTypeInv
  /\ ClientTsTypeInv
  /\ ClientKeyTypeInv
  /\ KeyDataTypeInv
  /\ KeyLockTypeInv
  /\ KeyWriteTypeInv
  /\ KeyWriteStartTsInv
  /\ KeyLastReadTsTypeInv
  /\ MsgTypeInv
       
=============================================================================
