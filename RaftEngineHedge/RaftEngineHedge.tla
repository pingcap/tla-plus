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

\* The threshold of items in the disk queue for abort
CONSTANT AbortThreshold

\* max data size of the whole raft-engine, the actual size does not matter in this spec
CONSTANT MaxDataSize

\* Initial persisted data for disk1 and disk2.
\* The normal raft-engine's data is the Max(InitData1, InitData2)
\* For a scratch start, InitData1 and InitData2 are 0.
CONSTANT InitData1, InitData2

\* head, tail for hedge File system's disk1 and disk2's queue 
VARIABLES head_1, head_2, tail_1, tail_2 

\* normal file system's disk queue
VARIABLES head, tail

\* the raft-engine's sealed data (not actively appending data)
VARIABLES sealed_data, sealed_data1, sealed_data2

\* the raft-engine's active data (actively appending data)
VARIABLES active_data, active_data1, active_data2

\* which disk is aborted. 0 means both disks are working normally
VARIABLE abort

-------------------------------------------------------------------------------
\* Helper functions.
Max(a, b) == IF a > b THEN a ELSE b

\* load disk data by simply a random number
\* For simplicity, assuming the data before the nunber is needed
InitData ==
LET
    data1 == InitData1
    data2 == InitData2
    data == Max(data1, data2)
IN
    /\ head_1 = data1
    /\ head_2 = data2
    /\ head = data
    /\ tail_1 = data \* when initialize, the slow disk's queue would be filled data from fast disk
    /\ tail_2 = data \* when initialize, the slow disk's queue would be filled data from fast disk
    /\ tail = data
    /\ sealed_data1 = {i: i \in 0..data1-1}
    /\ sealed_data2 = {i: i \in 0..data2-1}
    /\ sealed_data = {i: i \in 0..data-1}

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
    writes1 == RandomElement(0..tail_1 - head_1)
    writes2 == RandomElement(0..tail_2 - head_2)
IN
    \/  /\ abort = 0
        /\ head_1' = head_1 + writes1
        /\ head_2' = head_2 + writes2
        /\ head' = Max(head_1', head_2') \* for simplicity, the normal file system's queue length is same as max(disk1, disk2) 
        /\ active_data1' =  active_data1 \cup {i : i \in head_1 .. head_1'-1}
        /\ active_data2' =  active_data2 \cup {i : i \in head_2 .. head_2'-1}
        /\ active_data' =  active_data \cup {i : i \in head .. head'-1}
    \/  /\ abort = 1
        /\ head_2' = head_2 + writes2
        /\ head' = Max(head, head_2')
        /\ active_data2' =  active_data2 \cup {i : i \in head_2 .. head_2'-1}
        /\ active_data' =  active_data \cup {i : i \in head .. head'-1}
    \/  /\ abort = 2
        /\ head_1' = head_1 + writes1
        /\ head' = Max(head_1', head) 
        /\ active_data1' =  active_data1 \cup {i : i \in head_1 .. head_1'-1}
        /\ active_data' =  active_data \cup {i : i \in head .. head'-1}

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
    \/ /\ head_1 >= head_2 \* disk1 is primary disk
       /\ abort = 0
       /\ Purge(sealed_data, sealed_data1)
       /\ sealed_data2' = sealed_data1'
       /\ UNCHANGED <<active_data2, active_data1, active_data>>
    \/ /\ head_1 < head_2  \* disk2 is primary disk
       /\ abort = 0
       /\ Purge(sealed_data, sealed_data2)
       /\ sealed_data1' = sealed_data2'
       /\ UNCHANGED <<active_data2, active_data1, active_data>>
    \/ /\ abort = 1
       /\ UNCHANGED <<active_data2, active_data, sealed_data2, sealed_data>>
    \/ /\ abort = 2
       /\ UNCHANGED <<active_data1, active_data, sealed_data1, sealed_data>>
 

\* seal the active_data
\* Note: Seal must be called after PersistLog to ensure active_data1 correct
Seal ==
    \/  /\ abort = 0
        /\ sealed_data1' = sealed_data1 \cup active_data1 \* seal the active_data1
        /\ active_data1' = {}
        /\ sealed_data2' = sealed_data2 \cup active_data2 \* seal the active_data2 
        /\ active_data2' = {}
        /\ sealed_data' = sealed_data \cup active_data 
        /\ active_data' = {}
    \/  /\ abort = 1
        /\ sealed_data2' = sealed_data2 \cup active_data2 \* seal the active_data2 
        /\ active_data2' = {}
        /\ sealed_data' = sealed_data \cup active_data 
        /\ active_data' = {}
        /\ UNCHANGED  <<sealed_data1, active_data1>> 
    \/  /\ abort = 2
        /\ sealed_data1' = sealed_data1 \cup active_data1 \* seal the active_data1
        /\ active_data1' = {}
        /\ sealed_data' = sealed_data \cup active_data 
        /\ active_data' = {}
        /\ UNCHANGED  <<sealed_data2, active_data2>> 

\* seal and rewrite cannot run concurrently due to the contest on sealed_data.
\* In raft-engine's implementation, the file list is protected by the lock
SealOrRewrite ==
LET
    flag == RandomElement(0..1)
IN
    \/  /\ flag = 0
        /\ Rewrite
    \/  /\ flag = 1
        /\ Seal
    
\* check if we need to abort one of the disk
MaybeAbort ==
        \/  /\  head_1 >= head_2
            /\  \/  /\ tail_2 - head_2 > AbortThreshold
                    /\ abort = 0
                    /\ abort' = 2
                \/  /\ tail_2 - head_2 <= AbortThreshold
                    /\ abort' = 0
        \/  /\  head_1 < head_2 
            /\  \/  /\  tail_1 - head_1 > AbortThreshold
                    /\ abort' = 1
                    /\ abort = 0
                \/  /\ tail_1 - head_1 <= AbortThreshold
                    /\ abort' = 0

\* background catch up between two disks after one disk is aborted
BackgroundCatchup ==
    \/  /\ abort = 0
    \/  /\ abort = 1
        /\ sealed_data1' = sealed_data2'
        /\ active_data1' = active_data2'
        /\ head_1' = head_2'
        /\ tail_1' = tail_2'
    \/  /\ abort = 2
        /\ sealed_data2' = sealed_data1'
        /\ active_data2' = active_data1'
        /\ head_2' = head_1'
        /\ tail_2' = tail_1'

Unchanged == 
    \/ /\ abort = 0
       /\ UNCHANGED <<sealed_data, sealed_data1, sealed_data2>>
    \/ /\ abort = 1
       /\ UNCHANGED <<sealed_data, sealed_data2>>
    \/ /\ abort = 2
       /\ UNCHANGED <<sealed_data, sealed_data1>>
-------------------------------------------------------------------------------
Init ==
    /\ active_data = {}
    /\ active_data1 = {}
    /\ active_data2 = {}
    /\ abort = 0
    /\ InitData

Next ==
    /\ tail < MaxDataSize
    \*/\ PrintT("abort=" \o ToString(abort))
    \*/\ PrintT("head_1=" \o ToString(head_1) \o " head_2=" \o ToString(head_2) \o " head_=" \o ToString(head))
    \*/\ PrintT("tail_1=" \o ToString(tail_1) \o " tail_2=" \o ToString(tail_2) \o " tail=" \o ToString(tail))
    /\ AppendRaftLog
    /\ \/ Cardinality(active_data) < 5 /\ PersistLog /\ Unchanged
       \/ Cardinality(active_data) >= 5 /\ SealOrRewrite /\ UNCHANGED <<head_1, head_2, head>>
    /\ MaybeAbort
    /\ BackgroundCatchup 
   

Spec ==
  Init /\ Next

-------------------------------------------------------------------------------
DataInvariant ==
    /\ Max(head_1, head_2) = head 
    /\ Max(tail_1, tail_2) = tail
    /\ head_1 >= head_2 => (active_data \cup sealed_data) = (active_data1 \cup sealed_data1)
    /\ head_1 < head_2 => (active_data \cup sealed_data) = (active_data2 \cup sealed_data2)

===============================================================================
