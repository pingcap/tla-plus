# How to prove the correctness of the hedge file system on top of Raft-Engine

## Basic Idea

Assuming we have two raft-engine instances, one is what TiKV uses today and the other is the one with hedge file system. And if we construct the two instances with exactly same write traffic, at any time, the data of two Raft-Engine instances should be exactly same. 
The TLA module is to assert that, under all different situations, such as one disk is aborted and then recovered, GC/rewrite at the background, and TiKV restart. And in the module, we have the following assumptions or assert:

- Data sent to two disks are exactly same, though they are persisted in different time. For example, it does not handle silent memory error (bit flip), as today's TiKV does not handle it anyway.
- Single Disk's data corruption is handled by Raft-Engine's existing features.
- There're only one write thread and thus all write operations (including renaming, delete, etc) are all serialized.
- All writes are append-only.
- The caller's (TiKV) behavior is out of the scope of this module. For example, we assume the caller needs to wait for the data persisted, but it does not impact the design of this module.
- For simplicity, the write to any disk is guaranteed to be successful. Otherwise TiKV would panic.

## The Module's Abstration

- Raft-Engine
  In this module, it did not consider the Raft-Engine's implementation details. The abstraction of Raft-Engine is:
  - Append-only write function
  - Persist data into disk (two disks for hedge version) at random speed
  - Randomly delete data and rewrite data
  - Abort one disk in hedge version when that disk has large pending data  
- Raft Engine's data entry
  We use an auto increased integer to represent each raft engine's data entry. That integer actually is the index in the disk queue
- Write to Disk
  We use `head`, `tail` to represent the disk queue's head and tail index. They point to the first and last entry in disk queue repectively. For writing an entry to a disk essentially means its write queue's `tail` = `tail` + 1. However, this does not mean the data is persisted. A entry is persisted only when the `head` points to the index that is larger than its index.
- Which disk is the primary disk
  The disk is the primary disk iff its `head` is larger.  Because the head is only increased when the data it points to are all persisted. The larger the head is, the more persisted data the disk has. 
- Raft-Engine's data set
  We use a `set<int>` to represent all data set of Raft-Engine. For the hedge file system backed Raft-Engine, at any specific time, the Raft-Engine's data set is the primary disk (of that time)'s data set. It all comes from the primary disk. It's similar to Raft-protocol that all leader-read are from the current TiKV's leader (not from the leader when the data is persisted).
  There're two data sets per disk: `active_data` and `sealed_data` for active file and sealed file respectively. And Raft-Engine purge/rewrite only happen on sealed data. 
- Raft-Engine's Purge/Rewrite
  Purge is simulated by randomly deleting entrys from the `sealed_data`. To simplify the module, here we define purge is randomly picking an `ID` and then delete all entries whose ID are less than that `ID`. And for rewrite, it simply means `sealed_data` is updated with remainig data. And since all writes are serialized, the update of `sealed_data` by rewrite cannot be done with data persist at the same time.
- Abort one disk
  When one disk is too slow, we have to abort it to avoid the OOM. So we define a constant `AbortThreshod` so that when a disk's `tail` - `head` > `AbortThreshod`, that disk would be aborted. Then its `sealed_data` and `active_data` would be copied from the primary disk's `sealed_data` and `active_data` respectively.
  Please note here we don't abort the disk when there's only one disk remaining. And because the caller only returns when data is persisted, so when there's only one disk, the disk queue length is essentially 1 or 0.
  