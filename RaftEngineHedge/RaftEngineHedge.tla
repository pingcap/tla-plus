------------------------------ MODULE RaftEngineHedge -------------------------------

\* This is the formal specification for the TiKV raft-engine's hedge write algorithm
\*
\* There're following components involved in this algorithm. 
\* Raft-Engine: The actual details of Raft-Engine does not matter here. We can think 
\* of Raft-Engine a component doing synchronize foreground write (append-only) and  
\* asynchnorize background read & write (new file only).The background read is on read-only files.
\*
\* HedgeFileSystem: the FileSystem trait implementation that provides the disk hedge functionality
\*                  Read: Always read data from latest disk. Concurrent reads are supported.
\*                  Write: Write data to both disks and returns when data is persisted in one disk.
\*                         Write is serialized and no concurrent Sync_Write are allowed.
\*                  Background_Write: Write data to both disk and returns when data is persisted in
\*                                    both disks. Background_write and write are independent operations 
\*                                    and can be concurrent at file system level. File handle level is 
\*                                    restricted per underlying file system.
\*
\* Disk1: The abstraction that wraps the file system functionality to a disk 1, which includes the requests queue
\* Disk2: The abstraction that wraps the file system functionality to a disk 2, which includes the requests queue
\*
\* This spec is to mirror the Append and Rewrite operation to both HedgeFileSystem as well as normal FileSystem
\* And we want to assert that at any time, raft-engine's data set is same under two file systems. 
\* To mirror all the operation, we assume each disk IO of File system is same as the faster disk in HedgeFileSystem

EXTENDS Integers, FiniteSets, Sequences, TLC

\* The threshold of items in the disk queue
CONSTANT AbortThreshold

\* max data size of the whole raft-engine, the actual size does not matter in this spec
CONSTANT MaxDataSize

\* head, tail for hedge File system's disk1 and disk2's queue, as well as normal file system's disk queue
VARIABLES head_1, head_2, tail_1, tail_2, head, tail

\* flag if disk1 has newer data
VARIABLE is_disk1_newer

\* index of last sealed log
VARIABLE raft_log_last_index, raft_log_last_index1,raft_log_last_index2

\* the raft-engine's sealed data (not actively appending data)
VARIABLE sealed_data, sealed_data1, sealed_data2

\* the raft-engine's active data (actively appending data)
VARIABLE active_data, active_data1, active_data2

\* which disk is aborted. 0 means both disks are working normally
VARIABLE abort

vars == <<head_1, head_2, tail_1, tail_2, head, tail, is_disk1_newer, raft_log_last_index, raft_log_last_index1,raft_log_last_index2, sealed_data, sealed_data1, sealed_data2, active_data, active_data1, active_data2, abort>>
-------------------------------------------------------------------------------
\* Helper functions.
Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b

\* load disk data by simply a random number
\* For simplicity, assuming the data before the nunber is needed
InitData ==
LET
    data1 == CHOOSE i \in 0..MaxDataSize : TRUE
    data2 == CHOOSE i \in 0..MaxDataSize : TRUE
    data == Max(data1, data2)
IN
    /\ head_1 = data
    /\ head_2 = data
    /\ head = data
    /\ tail_1 = data
    /\ tail_2 = data
    /\ tail = data
    /\ sealed_data1 = {i: i \in 0..data1}
    /\ sealed_data2 = {i: i \in 0..data2}
    /\ sealed_data = {i: i \in 0..data}
    /\ raft_log_last_index1 = data1 
    /\ raft_log_last_index2 = data2
    /\ raft_log_last_index = data

\* append raft log into disk queues, not persisted yet
AppendRaftLog ==
    \/  /\ abort = 0
        /\ tail_1' = tail_1 + 1
        /\ tail_2' = tail_2 + 1
        /\ tail' = tail + 1
    \/  /\ abort = 1
        /\ tail_2' = tail_2 + 1
        /\ tail' = tail + 1
    \/  /\ abort = 2
        /\ tail_1' = tail_1 + 1
        /\ tail' = tail + 1

\* persist raft log from queue into disk.
\* The actual persisted log size is random per disk
PersistLog ==
LET 
    writes1 == CHOOSE i \in 0..tail_1 - head_1  : TRUE
    writes2 == CHOOSE i \in 0..tail_2 - head_2 : TRUE
IN
    \/  /\ abort = 0
        /\ head_1' = head_1 + writes1
        /\ head_2' = head_2 + writes2
        /\ head' = Max(head_1', head_2') \* for simplicity, the normal file system's queue length is same as max(disk1, disk2) 
        /\ active_data1' =  active_data1 \cup {head_1 .. head_1'}
        /\ active_data2' =  active_data2 \cup {head_2 .. head_2'}
        /\ active_data' =  active_data \cup {head .. head'}
    \/  /\ abort = 1
        /\ head_2' = head_2 + writes2
        /\ head' = Max(head_1', head_2') 
        /\ active_data2' =  active_data2 \cup {head_2 .. head_2'}
        /\ active_data' =  active_data \cup {head .. head'}
    \/  /\ abort = 2
        /\ head_1' = head_1 + writes1
        /\ head' = Max(head_1', head_2') 
        /\ active_data1' =  active_data1 \cup {head_1 .. head_1'}
        /\ active_data' =  active_data \cup {head .. head'}

\* Delete some raft logs
Delete(set, setX) ==
    LET removed == CHOOSE x \in setX : TRUE
    IN 
        /\ set' = set \ {removed}
        /\ setX' = setX \ {removed}

\* Simulate purging some data by randomly delete data from set and set2
Purge(set, setX) ==
    /\ \E n \in 1..Cardinality(set) :
        /\ \A i \in 1..n : Delete(set, setX)

\* rewrite old data (sealed_data)
Rewrite ==  
    \/ /\ is_disk1_newer = TRUE
       /\ Purge(sealed_data, sealed_data1)
       /\ sealed_data2' = sealed_data1' 
    \/ /\ is_disk1_newer = FALSE
       /\ Purge(sealed_data, sealed_data2)
       /\ sealed_data1' = sealed_data2'

\* seal the active_data
\* Note: Seal must be called after PersistLog to ensure active_data1 correct
Seal == 
    \/  /\ abort = 0
        /\ sealed_data1' = sealed_data1 \cup active_data1 \* seal the active_data1
        /\ active_data1' = {head_1 .. head_1'}
        /\ raft_log_last_index1' = head_1
        /\ sealed_data2' = sealed_data2 \cup active_data2 \* seal the active_data2 
        /\ active_data2' = {head_2 .. head_2'}
        /\ raft_log_last_index2' = head_2
        /\ sealed_data' = sealed_data \cup sealed_data 
        /\ active_data' = {head .. head'}
        /\ raft_log_last_index' = head
    \/  /\ abort = 1
        /\ sealed_data2' = sealed_data2 \cup active_data2 \* seal the active_data2 
        /\ active_data2' = {head_2 .. head_2'}
        /\ raft_log_last_index2' = head_2
        /\ sealed_data' = sealed_data \cup sealed_data 
        /\ active_data' = {head .. head'}
        /\ raft_log_last_index' = head
    \/  /\ abort = 2
        /\ sealed_data1' = sealed_data1 \cup active_data1 \* seal the active_data1
        /\ active_data1' = {head_1 .. head_1'}
        /\ raft_log_last_index1' = head_1
        /\ sealed_data' = sealed_data \cup sealed_data 
        /\ active_data' = {head .. head'}
        /\ raft_log_last_index' = head

\* seal and rewrite cannot run concurrently due to the contest on sealed_data
\* in the code, the file list is protected by the lock
SealOrRewrite ==
LET
    flag == CHOOSE i \in 0..1  : TRUE
IN
    \/  /\ flag = 0
        /\ Rewrite
    \/  /\ flag = 1
        /\ Seal
    
\* check if we need to abort one of the disk
MaybeAbort == abort' = 
        IF tail_1 - head_1 > AbortThreshold THEN
            /\ tail_1' = 0
            /\ head_1' = 0
            /\ 1 
        ELSE
            IF tail_2 - head_2 > AbortThreshold THEN
            /\ tail_2' = 0
            /\ head_2' = 0
            /\ 2 
            ELSE 0

\* background catch up between two disks after one disk is aborted
BackgroundCatchup ==
    \/  /\ abort = 1
        /\ sealed_data1' = sealed_data2'
        /\ head_1' = head_2
        /\ tail_1' = tail_2
        /\ raft_log_last_index1' = head_2
    \/  /\ abort = 2 
        /\ sealed_data2' = sealed_data1'
        /\ head_2' = head_1
        /\ tail_2' = tail_1
        /\ raft_log_last_index2' = head_1
-------------------------------------------------------------------------------
Init ==
    /\ head_1 = 0
    /\ head_2 = 0
    /\ head = 0
    /\ active_data = {}
    /\ active_data1 = {}
    /\ active_data2 = {}
    /\ abort = 0
    /\ is_disk1_newer = (head_1 >= head_2)
    /\ InitData

Next ==
    /\ is_disk1_newer' = (head_1 >= head_2)
    /\ AppendRaftLog
    /\ PersistLog
    /\ SealOrRewrite
    /\ MaybeAbort
    /\ BackgroundCatchup 
   

Spec ==
  Init /\ Next

-------------------------------------------------------------------------------
DataInvariant ==
    /\ Max(head_1, head_2) = head 
    /\ Max(tail_1, tail_2) = tail
    /\ is_disk1_newer => (sealed_data \cup active_data) = (sealed_data1 \cup active_data1)
    /\ ~is_disk1_newer => (sealed_data \cup active_data) = (sealed_data2 \cup active_data2)

===============================================================================
