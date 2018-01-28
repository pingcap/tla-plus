---------------------------- MODULE Percolator ----------------------------

EXTENDS Integers, Sequences, Bags, TLC

\* The set of transaction keys 
CONSTANTS KEY

\* The set of client to execute a transaction
CONSTANTS CLIENT

\* next_ts is the timestamp for transaction. It is increased monotonically so
\* every transaction must have a unique start and commit ts.
VARIABLES next_ts

\* $client_state[c] is the state of client
VARIABLES client_state

\* $client_ts[c] is a record of [start: ts, commit: ts]
VARIABLES client_ts

\* $client_keys[c] is a record of [primary: key, second: {key}]
VARIABLES client_key

\* $key_lock[k] is the set of lock. 
VARIABLES key_lock

\* $key_write[k] is a sequence of committed version of the key.
VARIABLES key_write

\* $key_data[k] is the set of multi-version data timestamp of the key. 
VARIABLES key_data

Init == 
    /\ next_ts = 0
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |-> [primary |-> "", secondary |-> {}]]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> <<>>]
    /\ key_data = [k \in KEY |-> {}]

       
key_vars == <<key_lock, key_write, key_data>>
client_txn_vars == <<client_ts, client_key>>


\* Check whether there is a lock which start ts is less or equal than start_ts.
hasLockLE(k, start_ts) == 
    {l \in key_lock[k] : l.start_ts <= start_ts} /= {}

\* Check whether there is a lock with start ts or not.
hasLockEQ(k, start_ts) ==
     {l \in key_lock[k] : l.start_ts <= start_ts} /= {}
     
\* Select a primary key and use the rest for the secondary key
chooseKey ==
    LET
        primary == CHOOSE k \in KEY: TRUE
    IN
        [primary |-> primary, secondary |-> KEY \ {primary}]

\* Return TRUE means the client meets no lock and can does pre-write.     
canPrewrite(c) == 
     LET 
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary
     IN
        /\ ~hasLockLE(primary, start_ts)
        /\ \A k \in secondary : 
            /\ ~hasLockLE(k, start_ts)
           
\* Return TRUE means a lock can be cleanup up if:
\*  1. The lock is a primary lock and the start ts is less than start_ts.
\*  2. Or the lock is a secondary lock and the associated primary key is cleaned up. 
\* Notice: Percolator paper doesn't explain how to clean up the lock, here we just use 
\* a simple way.
isStaleLock(l, start_ts) ==            
    \/ /\ l.primary = ""
       /\ l.start_ts < start_ts
    \/ /\ l.primary /= ""
       /\ ~hasLockEQ(l.primary, l.start_ts) 
   
\* Return TRUE if we have a stale lock for key.
hasStaleLock(k, start_ts) ==
    \A l \in key_lock[k] :
        \/ isStaleLock(l, start_ts)                       
           
\* Return TRUE means the client can clean up a stale lock
canCleanup(c) == 
     LET 
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary
     IN
        /\ ~hasStaleLock(primary, start_ts)
        /\ \A k \in secondary : 
            /\ ~hasStaleLock(k, start_ts) 
            
\* Find write with start ts.
findWriteWithStart(k, start_ts) ==
    SelectSeq(key_write[k], LAMBDA w : w.start_ts = start_ts)  

\* Clean up a stale lock and its data. If the lock is a secondary lock
\* and the assoicated primary lock is cleaned up, we can clean up the lock and do:
\* 1. If the primary key is committed, we must also commit the secondary key
\* 2. Otherwise, clean up the stale data too
cleanupStaleLock(k, start_ts) == 
    LET
        \* Find a stale lock at first
        l == CHOOSE l \in key_lock[k] : isStaleLock(l, start_ts)
    IN
        /\ key_lock' = key_lock \ {l}
        /\ \/ /\ l.primary = ""
              /\ key_data' = key_data \ {l.start_ts}
              /\ UNCHANGED <<key_write>>
           \/ /\ l.primary /= ""
              /\ LET
                    w == findWriteWithStart(l.primary, l.start_ts)
                 IN
                    IF Len(w) = 0 
                    THEN
                        \* The primary key is not committed, clean up the data
                        /\ key_data' = key_data \ {l.start_ts}
                        /\ UNCHANGED <<key_write>>
                    ELSE
                        \* The primary key is committed, commit the secondary key
                        /\ key_write' = Append(key_write, w[1])
                        /\ UNCHANGED <<key_data>>

\* Clean up a stale lock when the client meets.
cleanup(c) == 
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary
        meetStaleLock(k) == /\ \/ k = primary 
                               \/ k \in secondary
                            /\ hasStaleLock(k, start_ts)   
        k == CHOOSE k \in KEY : meetStaleLock(k)
     IN
        cleanupStaleLock(k, start_ts)
        
\* Return TURE means there is no lock for key and no any newer write.
canLockKey(k, start_ts) ==    
    LET
        writes == {w \in DOMAIN key_write[k] : key_write[k][w].commit_ts >= start_ts}
    IN
        \* No any lock for the key
        /\ key_lock[k] = {} 
        \* No any newer write
        /\ writes = {} 
       
\* Return whether the client can lock all keys    
canLock(c) ==
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary 
    IN
        /\ canLockKey(primary, start_ts)
        /\ \A k \in secondary :
           /\ canLockKey(k, start_ts)

\* Lock the key and save the data
lockKey(k, start_ts, primary) ==
    /\ key_lock' = [key_lock EXCEPT ![k] = @ \UNION {[start_ts |-> start_ts, primary |-> primary]}]
    /\ key_data' = [key_data EXCEPT ![k] = @ \UNION {start_ts}]
    /\ UNCHANGED <<key_write>>
    

\* Try to lock primary key first, then the secondary key            
lock(c) == 
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary        
     IN
        IF hasLockEQ(primary, start_ts)
        THEN
            lockKey(primary, start_ts, "")
        ELSE
            \* primary key has already been locked, we must choose the a secondary key to lock
            LET
                k == CHOOSE k \in secondary : canLockKey(k, start_ts)
            IN
                lockKey(k, start_ts, primary)           
           
\* Return TRUE when the client locks all keys
canCommit(c) == 
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary
    IN
        /\ hasLockEQ(primary, start_ts)
        /\ \A k \in secondary : 
            /\ hasLockEQ(k, start_ts)

\* Return TRUE mean we can commit the primary key.
canCommitPrimary(c) ==
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
    IN
        hasLockEQ(primary, start_ts)
        
\* Commit the primary key.       
commitPrimary(c) == 
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
    IN
        /\ key_write' = [key_write EXCEPT ![primary] = Append(@, client_ts[c])]
        /\ key_lock' = [key_lock EXCEPT ![primary] = @ \ {start_ts}] 
            
Start(c) ==
    /\ client_state[c] = "init"
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ next_ts' = next_ts + 1
    /\ client_ts' = [client_ts EXCEPT ![c] = [@ EXCEPT !.start_ts = next_ts']]
    /\ client_key' = [client_key EXCEPT ![c] = chooseKey]
    /\ UNCHANGED <<key_vars>>

Get(c) ==
    /\ client_state[c] = "working"
    /\ 
        IF canPrewrite(c)
        THEN 
           /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]      
           /\ UNCHANGED <<key_vars, client_txn_vars, next_ts>>
        ELSE
            IF canCleanup(c)
            THEN
                /\ cleanup(c)   
                /\ UNCHANGED <<client_state, client_txn_vars, next_ts>>
            ELSE
                /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
                /\ UNCHANGED <<key_vars, client_txn_vars, next_ts>>

Prewrite(c) ==
    /\ client_state[c] = "prewriting"
    /\ IF canCommit(c)
       THEN
            /\ next_ts' = next_ts + 1
            /\ client_ts' = [client_ts EXCEPT ![c] = [@ EXCEPT !.commit_ts = next_ts']]
            /\ client_state' = [client_state EXCEPT ![c] = "committing"]      
            /\ UNCHANGED <<key_vars, client_key, next_ts>>
       ELSE
            IF canLock(c) 
            THEN
                /\ lock(c)
                /\ UNCHANGED <<client_state, client_txn_vars, next_ts>>
            ELSE
                /\ client_state' = [client_state EXCEPT ![c] = "aborted"]      
                /\ UNCHANGED <<key_vars, client_txn_vars, next_ts>>

Commit(c) ==
    /\ client_state[c] = "committing"
    /\ IF canCommitPrimary(c)
       THEN
            /\ commitPrimary(c)
            /\ client_state' = [client_state EXCEPT ![c] = "committed"] 
            /\ UNCHANGED <<key_data, client_txn_vars, next_ts>>
            \* If we commit primary successfully, we can think the transaction is committed
            \* TODO: use async message to commit second keys
       ELSE
            /\ client_state' = [client_state EXCEPT ![c] = "aborted"]      
            /\ UNCHANGED <<key_vars, client_txn_vars, next_ts>>
Next == 
    \E c \in CLIENT:
        Start(c) \/ Get(c) \/ Prewrite(c) \/ Commit(c)
     

checkWriteOrder(w1, w2) ==
    /\ w1.commit_ts < w2.commit_ts
    /\ w1.start_ts < w2.start_ts
    /\ w1.start_ts < w1.commit_ts


\* The committed write timestamp of the key must be in order.
WriteConsistency ==
    \A k \in KEY :
        IF Len(key_write[k]) > 1 
        THEN
            LET
                ws == [n \in 1..Len(key_write[k]) - 1 |-> checkWriteOrder(key_write[k][n], key_write[k][n + 1])]
            IN
                ~ FALSE \in ws
        ELSE
            IF Len(key_write[k]) = 1 
            THEN
                key_write[k][1].start_ts < key_write[k][1].commit_Ts
            ELSE
                TRUE  

\* find write with commit ts.
findWriteWithCommit(k, commit_ts) ==
    SelectSeq(key_write[k], LAMBDA w : w.commit_ts = commit_ts) 

CommittedConsistency == 
    \A c \in CLIENT :
    LET 
        start_ts == client_ts[c].start
        commit_ts == client_ts[c].commit
        primary == client_key[c].primary
        secondary == client_key[c].second
        w == [start |-> start_ts, commit |-> commit_ts]
    IN  
        \/ /\ client_state[c] = "committed"
           \* The primary key lock must be cleaned up, and no any older lock.
           /\ ~hasLockLE(primary, start_ts) 
           /\ findWriteWithCommit(primary, commit_ts) = <<w>>
           /\ {start_ts} \in key_data[primary]
           /\ \A k \in secondary :
              \* The secondary key lock can be empty or not.
              /\ \/ /\ ~hasLockEQ(k, start_ts)
                    /\ findWriteWithCommit(k, commit_ts) = <<w>>
                    /\ ~hasLockLE(k, start_ts - 1)
                 \/ /\ hasLockEQ(k, start_ts)
                    /\ findWriteWithCommit(k, commit_ts) = <<>>
                    /\ 
                        IF Len(key_write[k]) > 0 
                        THEN
                            \* Lock has not been cleaned up, so the last write committed 
                            \* timestamp must be less than lock start ts.
                            key_write[k][Len(key_write[k])].commit_ts < start_ts
                        ELSE
                            TRUE
              /\ {start_ts} \in key_data[k]
        \/ TRUE

=============================================================================
\* Modification History
\* Last modified Fri Nov 17 16:40:19 CST 2017 by tangliu
\* Created Fri Nov 17 08:55:33 CST 2017 by tangliu
