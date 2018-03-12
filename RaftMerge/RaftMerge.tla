------------------------------ MODULE RaftMerge -------------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS Store, Region
CONSTANTS RegionA, RegionB
CONSTANTS LeaderA, LeaderB

ASSUME /\ Region = {RegionA, RegionB}
       /\ LeaderA \in Store
       /\ LeaderB \in Store

\* The minimum size of servers to be a quorum.
\*
\* The motivation of adding this constant is that, raft with 1 leader and 2
\* followers is rather slow for TLC to verify (the space to explore is fricking
\* big). We relax the raft with only 1 leader and 1 follower. By setting
\* quorum size to 1 as a backdoor, we can simulate some states that a follower
\* can have some logs lag behind, but does not affect the correctness of raft
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
\* struct Raft {
\*   bool is_leader;
\*   vector<Log> logs;
\*   int commit_index;
\*   int apply_index;
\*   int match_index[MAXS];  // leader only
\* };
\*
\* struct Store {
\*   Raft raft[2];      // 2 for two regions
\* } stores[MAXS];
\*
\* Note for ease of implementation, we use two 2-dimension arrays raft[MAXS][2].

\* Log.
CONSTANTS Log

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

\* Leader i sends j an AppendEntries request containing up to 1 entry.
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

\* Leader i advances its commitIndex.
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

\* Server i receives an AppendEntries request from server j.
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

\* Server i receives an AppendEntries reply from server j.
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

\* Leader i receives a client request to add a log.
ClientRequest(i, r, log) ==
  /\ raft[i][r].is_leader
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

\* Return TRUE if there is a log applicable to the state machine.
LogAppliable(i, r) ==
  raft[i][r].apply_index < raft[i][r].commit_index

\* Apply Raft logs to make apply_index catch up with commit_index.
\* This simply increases apply_index.
ApplyLog(i, r) ==
  LET
    next_index == raft[i][r].apply_index + 1
  IN
    /\ LogAppliable(i, r)
    /\ raft' = [raft EXCEPT ![i][r].apply_index = next_index]
    /\ UNCHANGED <<messages, region, client_vars>>

-------------------------------------------------------------------------------

\* Specification of Raft merge.
Next ==
  \* Raft actions.
  \/ \E i,j \in Store : \E r \in Region : AppendEntries(i, j, r)
  \/ \E i \in Store : \E r \in Region : AdvanceCommitIndex(i, r)
  \/ \E m \in messages : Receive(m)
  \/ \E i \in Store : \E r \in Region : ApplyLog(i, r)

  \* External client can send requests to region leader.
  \/ \E i \in Store : \E r \in Region :
        ClientRequest(i, r, Log)

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
                              match_index  |-> [j \in Store |-> 0]
                             ]
                           ]
                         ]
     IN
       raft = MarkLeader(MarkLeader(no_leader_raft, LeaderA, RegionA),
                         LeaderB,
                         RegionB)
  /\ region = TRUE
  /\ client_requests_index = 0

Spec ==
  Init /\ [][Next]_vars

-------------------------------------------------------------------------------
\* Type invariants.

LogType ==
  {Log}

RaftType ==
  [ is_leader    : BOOLEAN,
    logs         : Seq(LogType),
    commit_index : Nat,
    apply_index  : Nat,
    match_index  : [Store -> Nat]  \* Only available on leader.
                                   \* Initialized to zeroes on followers.
  ]

TypeInvariant ==
  /\ raft   \in [Store -> [Region -> RaftType]]

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

===============================================================================