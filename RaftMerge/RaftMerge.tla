------------------------------ MODULE RaftMerge -------------------------------

\* This is the formal specification for the multi-raft region merge algorithm
\* of TiKV.
\*
\* The whole data is divided into multiple shards called regions, and each
\* region is replicated to several stores comprising a Raft group. Two regions
\* can merge into a larger one if one region is reasonably small.
\*
\* This specification asserts two regions named A and B are replicated to the
\* same set of stores. Each region has leader on store LeaderA and LeaderB
\* respectively.
\*
\* Notice that TiKV uses a slightly different Raft model compared with Ongaro's
\* original Raft implementation. A log is truly committed if the log is applied
\* to the state machine, and then server will return the result to client.
\* commit_index is only a marker, log may be dropped even if commit_index goes
\* beyond that log.

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS Store, Region
CONSTANTS RegionA, RegionB
CONSTANTS LeaderA, LeaderB

ASSUME /\ Region = {RegionA, RegionB}
       /\ LeaderA \in Store
       /\ LeaderB \in Store

\* If TRUE, a rollback will be performed in place of merge.
CONSTANTS WillPerformRollback
ASSUME WillPerformRollback \in BOOLEAN

\* The minimum size of servers to be a quorum.
\*
\* The motivation of adding this constant is that, Raft with 1 leader and 2
\* followers is rather slow for TLC to verify (the space to explore is fricking
\* big). We relax Raft with only 1 leader and 1 follower. By setting quorum size
\* to 1 as a hack, we can simulate some states that a follower can have some
\* logs lag behind, a scenario which can happen when there are at least 3
\* servers in a Raft group. This setting does not affect the correctness of Raft
\* protocol because we assume there is no leader switch.
\*
\* If set to 0, a set of servers is considered as a quorum if it contains at
\* least half of servers.
CONSTANTS QuorumSize

\* Maximum number of client requests.
CONSTANTS MaxClientRequests

\* The current index of client request, should be smaller than
\* MaxClientRequests.
VARIABLES client_requests_index

\* Message types for Raft log synchronization.
CONSTANTS AppendEntriesRequest, AppendEntriesReply

\* A set of messages representing RPC requests and responses sent from one
\* server to another.
VARIABLES messages

\* The data structures in C. MAXS = |Store|.
\*
\* enum Log { LogNormal, LogPreMerge, LogMerge, LogRollback };
\*
\* enum RegionState { RegionNormal, RegionTombStone, RegionMerging };
\*
\* struct Raft {
\*   bool is_leader;
\*   vector<Log> logs;
\*   int commit_index;
\*   int apply_index;
\*   int num_applied;        // number of applied normal logs
\*   int match_index[MAXS];  // leader only
\* };
\*
\* struct Store {
\*   Raft raft[2];           // 2 for two regions
\*   RegionState region[2];  // 2 for two regions
\* } stores[MAXS];
\*
\* Note for ease of implementation, we use two 2-dimension arrays raft[MAXS][2]
\* and region[MAXS][2].
\*
\* Also note that different from a real-world implementation, we don't
\* introduce the concept of `epoch` here, which is used to figure out whether
\* the configuration of one region has changed. Epoch matters when we are
\* applying the logs into state machine, if it is stale, we will skip all
\* later non-admin logs. Epoch will be changed when we are applying admin logs.

\* Log types.
\* The logs are divided into two categories, normal logs and admin logs.
\* Logs apart from LogNormal are admin logs.
CONSTANTS LogNormal,    \* RegionB only
          LogPreMerge,
          LogMerge,
          LogRollback

\* Region state types.
CONSTANTS RegionNormal,
          RegionTombStone,
          RegionMerging

VARIABLES raft, region

client_vars == <<client_requests_index>>
vars == <<messages, raft, region, client_vars>>

-------------------------------------------------------------------------------
\* Helper functions.

\* Return true if the server set is a quorum.
IsQuorum(svrs) ==
  IF QuorumSize = 0
    THEN Cardinality(svrs) * 2 > Cardinality(Store)
    ELSE Cardinality(svrs) >= QuorumSize

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Add a message to the set of messages.
Send(m) == messages' = messages \cup {m}

\* Remove a message from the set of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = messages \ {m}

\* Combination of Send and Discard.
Reply(reply, request) == messages' = (messages \cup {reply}) \ {request}

-------------------------------------------------------------------------------
\* State transitions and message handlers for Raft.

\* Leader i of region r sends j an AppendEntries request containing 1 entry.
AppendEntries(i, j, r) ==
  /\ i /= j
  /\ raft[i][r].is_leader
  /\ LET
       next_index == raft[i][r].match_index[j] + 1
     IN
       /\ next_index <= Len(raft[i][r].logs)
       /\ Send([type |-> AppendEntriesRequest,
                region       |-> r,
                source       |-> i,
                dest         |-> j,
                entry        |-> raft[i][r].logs[next_index],
                entry_index  |-> next_index,
                commit_index |-> Min({next_index, raft[i][r].commit_index})])
  /\ UNCHANGED <<raft, region, client_vars>>

\* Leader i of region r advances its commitIndex.
AdvanceCommitIndex(i, r) ==
  /\ raft[i][r].is_leader
  /\ LET
       \* The set of servers that agree up through index.
       Agree(index) == {i} \cup {k \in Store : raft[i][r].match_index[k] >= index}
       \* The maximum indexes for which a quorum agrees.
       agree_indexes == {index \in 1..Len(raft[i][r].logs) : IsQuorum(Agree(index))}
       \* New value for commitIndex'[i].
       new_commit_index == Max(agree_indexes \cup {raft[i][r].commit_index})
     IN
       raft' = [raft EXCEPT ![i][r].commit_index = new_commit_index]
  /\ UNCHANGED <<messages, region, client_vars>>

\* Server i of region r receives an AppendEntries request from server j.
HandleAppendEntriesRequest(i, j, r, m) ==
  \/ \* Append this log entry if it is new.
     /\ m.entry_index = Len(raft[i][r].logs) + 1
     /\ LET
          new_logs == Append(raft[i][r].logs, m.entry)
          new_commit_index == Max({raft[i][r].commit_index, m.commit_index})
        IN
          /\ raft' = [raft EXCEPT ![i][r].logs = new_logs,
                                  ![i][r].commit_index = new_commit_index]
          /\ Reply([type        |-> AppendEntriesReply,
                    region      |-> r,
                    source      |-> i,
                    dest        |-> j,
                    match_index |-> Len(new_logs)],
                   m)
     /\ UNCHANGED <<region, client_vars>>
  \/ \* We already have this log entry, discarding this message.
     /\ m.entry_index <= Len(raft[i][r].logs)
     /\ Discard(m)
     /\ UNCHANGED <<raft, region, client_vars>>

\* Server i of region r receives an AppendEntries reply from server j.
HandleAppendEntriesReply(i, j, r, m) ==
  /\ raft' = [raft EXCEPT ![i][r].match_index = [@ EXCEPT ![j] = Max({@, m.match_index})]]
  /\ Discard(m)
  /\ UNCHANGED <<region, client_vars>>

\* Poll a message from message set, and invoke the corresponding RPC handler.
Receive(m) ==
  LET
    i == m.dest
    j == m.source
    r == m.region
  IN
    \/ /\ m.type = AppendEntriesRequest
       /\ HandleAppendEntriesRequest(i, j, r, m)
    \/ /\ m.type = AppendEntriesReply
       /\ HandleAppendEntriesReply(i, j, r, m)

\* Leader i of region r receives a client request to append a log.
ClientRequest(i, r, log) ==
  /\ raft[i][r].is_leader
  /\ region[i][r] = RegionNormal
  /\ client_requests_index < MaxClientRequests
  /\ LET
       new_logs == Append(raft[i][r].logs, log)
       new_match_index == [raft[i][r].match_index EXCEPT ![i] = @ + 1]
     IN
       /\ raft' = [raft EXCEPT ![i][r].logs = new_logs,
                               ![i][r].match_index = new_match_index]
       /\ client_requests_index' = client_requests_index + 1
  /\ UNCHANGED <<messages, region>>

-------------------------------------------------------------------------------
\* State transitions for Raft merge, and log applying.

\* Internal requests for Raft merge.
\* Assume raft[i][r].is_leader, i.e., only leader can handle internal requests.
InternalRequest(i, r, log) ==
  LET
    new_logs == Append(raft[i][r].logs, log)
    new_match_index == [raft[i][r].match_index EXCEPT ![i] = @ + 1]
  IN
    [raft EXCEPT ![i][r].logs = new_logs,
                 ![i][r].match_index = new_match_index]

\* Send merge request to the leader of Region B.
ProposeMergeRequest(i) ==
  /\ raft[i][RegionB].is_leader
  /\ region[i][RegionB] = RegionNormal
  /\ \* This request should be sent only once.
     Len(SelectSeq(raft[i][RegionB].logs, LAMBDA log : log.type = LogPreMerge)) = 0
  /\ raft' = InternalRequest(
               i, RegionB,
               [type      |-> LogPreMerge,
                min_index |-> 1 + Min({raft[i][RegionB].match_index[j] : j \in Store})]
             )
  /\ UNCHANGED <<messages, region, client_vars>>

\* Perform rollback by appending a rollback log on leader B.
PerformRollbackRequest(i) ==
  /\ WillPerformRollback = TRUE
  /\ raft[i][RegionB].is_leader
  /\ region[i][RegionB] = RegionMerging
  /\ \* This log should be appended only once.
     Len(SelectSeq(raft[i][RegionB].logs, LAMBDA log : log.type = LogRollback)) = 0
  /\ raft' = InternalRequest(i, RegionB, [type |-> LogRollback])
  /\ UNCHANGED <<messages, region, client_vars>>

\* Return TRUE if there is a log applicable to the state machine.
\* A log is applicable if it is committed, and the target region is not in
\* TombStone state.
LogAppliable(i, r) ==
  /\ raft[i][r].apply_index < raft[i][r].commit_index
  /\ region[i][r] /= RegionTombStone

\* Apply LogPreMerge.
ApplyPreMergeLog(i) ==
  LET
    next_index == raft[i][RegionB].apply_index + 1
  IN
    /\ LogAppliable(i, RegionB)
    /\ raft[i][RegionB].logs[next_index].type = LogPreMerge
    /\ IF raft[i][RegionA].is_leader
       THEN
         \* If this store is the leader of regionA, make a merge proposal, and
         \* advance apply_index.
         LET
           min_index == raft[i][RegionB].logs[next_index].min_index
           commit_index == next_index
           fetch_logs == SubSeq(raft[i][RegionB].logs, min_index, commit_index)
         IN
           raft' = [InternalRequest(
                      i, RegionA,
                      [type         |-> LogMerge,
                       min_index    |-> min_index,
                       commit_index |-> commit_index,
                       entries      |-> fetch_logs]
                    )
                    EXCEPT ![i][RegionB].apply_index = next_index]
       ELSE
         \* Otherwise, only advance apply_index.
         raft' = [raft EXCEPT ![i][RegionB].apply_index = next_index]
    /\ region' = [region EXCEPT ![i][RegionB] = RegionMerging]
    /\ UNCHANGED <<messages, client_vars>>

\* Apply LogMerge.
\*
\* This action is roughly divided into two sub-actions, and executed separately.
\* The first step copies the logs to region B, to ensure it in sync with leader
\* B. The second step waits until the copied logs in the first step are applied,
\* then advances apply_index and marks this region as tombstone.
ApplyMergeLogStep1(i) ==
  LET
    next_index   == raft[i][RegionA].apply_index + 1
    min_index    == raft[i][RegionA].logs[next_index].min_index
    commit_index == raft[i][RegionA].logs[next_index].commit_index
    new_logs     ==
      LET
        old_logs == raft[i][RegionB].logs
        entries  == raft[i][RegionA].logs[next_index].entries
      IN
        IF commit_index <= Len(raft[i][RegionB].logs)
        THEN old_logs
        ELSE old_logs \o SubSeq(entries, Len(old_logs) - min_index + 2, Len(entries))
  IN
    /\ raft' = [raft EXCEPT ![i][RegionB].logs = new_logs,
                            ![i][RegionB].commit_index = Max({@, commit_index})]
    /\ UNCHANGED <<messages, region, client_vars>>

ApplyMergeLogStep2(i) ==
  LET
    next_index   == raft[i][RegionA].apply_index + 1
    commit_index == raft[i][RegionA].logs[next_index].commit_index
  IN
    /\ \* Lag logs have been applied.
       raft[i][RegionB].apply_index >= commit_index
    /\ raft' = [raft EXCEPT ![i][RegionA].apply_index = next_index]
    /\ IF WillPerformRollback = FALSE
       THEN
         region' = [region EXCEPT ![i][RegionB] = RegionTombStone]
       ELSE
         UNCHANGED <<region>>
    /\ UNCHANGED <<messages, client_vars>>

ApplyMergeLog(i) ==
  LET
    next_index == raft[i][RegionA].apply_index + 1
  IN
    /\ LogAppliable(i, RegionA)
    /\ raft[i][RegionA].logs[next_index].type = LogMerge
    /\ \/ ApplyMergeLogStep1(i)
       \/ ApplyMergeLogStep2(i)

\* Apply LogRollback.
\* As we don't skip all logs after PreMerge log, rollback just marks the state
\* of region as normal.
ApplyRollbackLog(i) ==
  LET
    next_index == raft[i][RegionB].apply_index + 1
  IN
    /\ LogAppliable(i, RegionB)
    /\ raft[i][RegionB].logs[next_index].type = LogRollback
    /\ raft' = [raft EXCEPT ![i][RegionB].apply_index = next_index]
    /\ region' = [region EXCEPT ![i][RegionB] = RegionNormal]
    /\ UNCHANGED <<messages, client_vars>>

\* Apply LogNormal.
\* This log simply increases apply_index.
ApplyNormalLog(i, r) ==
  LET
    next_index == raft[i][r].apply_index + 1
  IN
    /\ LogAppliable(i, r)
    /\ raft[i][r].logs[next_index].type = LogNormal
    /\ LET
         \* Apply this log if this region is in normal state, otherwise skip it.
         \* Notice we don't check for epoch here as what is done in the real
         \* world implementation, but these two approaches are equivalent to
         \* check whether we have applied PreMergeLog, as applying PreMergeLog
         \* will also convert the region state from normal state.
         num_applied_delta == IF region[i][r] = RegionNormal THEN 1 ELSE 0
       IN
         raft' = [raft EXCEPT ![i][r].apply_index = next_index,
                              ![i][r].num_applied = @ + num_applied_delta]
    /\ UNCHANGED <<messages, region, client_vars>>

\* Apply Raft logs to make apply_index catch up with commit_index.
ApplyLog(i) ==
  \/ \E r \in Region : ApplyNormalLog(i, r)
  \/ ApplyPreMergeLog(i)
  \/ ApplyMergeLog(i)
  \/ ApplyRollbackLog(i)

-------------------------------------------------------------------------------

\* Specification of Raft merge.
Next ==
  \* Raft actions.
  \/ \E i, j \in Store : \E r \in Region : AppendEntries(i, j, r)
  \/ \E i \in Store : \E r \in Region : AdvanceCommitIndex(i, r)
  \/ \E m \in messages : Receive(m)

  \* External client can send requests to region B leader, to add a new log
  \* entry in region B.
  \/ \E i \in Store : ClientRequest(i, RegionB, [type |-> LogNormal])

  \* Raft merge actions.
  \/ ProposeMergeRequest(LeaderB)
  \/ PerformRollbackRequest(LeaderB)
  \/ \E i \in Store : ApplyLog(i)

Init ==
  /\ messages = {}
  /\ LET
       \* Mark region r on store i as leader.
       MarkLeader(rafts, i, r) == [rafts EXCEPT ![i] = [@ EXCEPT ![r].is_leader = TRUE]]
       no_leader_raft == [i \in Store |->
                           [r \in Region |->
                             [is_leader    |-> FALSE,
                              logs         |-> << >>,
                              commit_index |-> 0,
                              apply_index  |-> 0,
                              num_applied  |-> 0,
                              match_index  |-> [j \in Store |-> 0]
                             ]
                           ]
                         ]
     IN
       raft = MarkLeader(MarkLeader(no_leader_raft, LeaderA, RegionA),
                         LeaderB,
                         RegionB)
  /\ region = [i \in Store |-> [r \in Region |-> RegionNormal]]
  /\ client_requests_index = 0

Spec ==
  Init /\ [][Next]_vars

-------------------------------------------------------------------------------
\* Type invariants.

LogType ==
  LET
    FlatLogType ==
           [type : {LogNormal}]
      \cup [type : {LogPreMerge}, min_index : Nat]
      \cup [type : {LogRollback}]
  IN
         FlatLogType
    \cup [type : {LogMerge},
          min_index : Nat,
          commit_index : Nat,
          entries : Seq(FlatLogType)]

RaftType ==
  [ is_leader    : BOOLEAN,
    logs         : Seq(LogType),
    commit_index : Nat,
    apply_index  : Nat,
    num_applied  : Nat,
    match_index  : [Store -> Nat]  \* Only available on leader.
                                   \* Initialized to zeroes on followers.
  ]

RegionType ==
  { RegionNormal, RegionTombStone, RegionMerging }

TypeInvariant ==
  /\ raft   \in [Store -> [Region -> RaftType]]
  /\ region \in [Store -> [Region -> RegionType]]

-------------------------------------------------------------------------------
\* Some invariants for our simplified Raft model.

\* There should be only one leader for each raft group.
OneLeaderInvariant ==
  \A r \in Region : Cardinality({s \in Store : raft[s][r].is_leader}) = 1

\* AppendEntries RPC is always sent from leader to follower.
AppendEntriesMessageInvariant ==
  \A m \in messages :
    LET
      r == m.region
      leader == CHOOSE s \in Store : raft[s][r].is_leader
    IN
      /\ m.type = AppendEntriesRequest =>
           /\ m.source = leader
           \* There should be no gap between the log to append in RPC, and the
           \* existing logs.
           /\ m.entry_index <= Len(raft[m.dest][r].logs) + 1
      /\ m.type = AppendEntriesReply =>
           m.dest = leader

\* All known (by leader) replicated logs (logs before match_index) should be on
\* followers, and all replicated logs on followers should be a prefix of logs
\* on leader.
LogInvariant ==
  \A r \in Region :
    LET
      leader == CHOOSE s \in Store : raft[s][r].is_leader
    IN
      \A s \in Store :
        /\ raft[leader][r].match_index[s] <= Len(raft[s][r].logs)
        /\ raft[s][r].logs = SubSeq(raft[leader][r].logs, 1, Len(raft[s][r].logs))

\* apply_index should be equal or less than commit_index.
ApplyIndexInvariant ==
  \A s \in Store :
    \A r \in Region :
      raft[s][r].apply_index <= raft[s][r].commit_index

\* Combination of the above invariants.
SimpliedRaftInvariant ==
  /\ OneLeaderInvariant
  /\ AppendEntriesMessageInvariant
  /\ LogInvariant
  /\ ApplyIndexInvariant

-------------------------------------------------------------------------------
\* Some invariants for Raft region merge.

\* If a region on two different stores have applied the same logs, they should
\* also share the same region state and number of applied normal logs.
RegionApplyInvariant ==
  \A i, j \in Store :
    (
      /\ i /= j
      /\ (\A r \in Region : raft[i][r].apply_index = raft[j][r].apply_index)
    ) =>
      \A r \in Region :
        /\ region[i][r] = region[j][r]
        /\ raft[i][RegionB].num_applied = raft[j][RegionB].num_applied

\* For any two stores of region B, if both done, they should have the same
\* number of applied logs.
MergeLogInvariant ==
  \A i, j \in Store :
    (
      /\ i /= j
      /\ region[i][RegionB] = RegionTombStone
      /\ region[j][RegionB] = RegionTombStone
    ) =>
      raft[i][RegionB].num_applied = raft[j][RegionB].num_applied

\* Combination of the above invariants.
RaftMergeInvariant ==
  /\ RegionApplyInvariant
  /\ MergeLogInvariant

===============================================================================
