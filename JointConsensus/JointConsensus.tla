--------------------------------- MODULE JointConsensus ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS InitialServers, NewServers

CONSTANTS ValueEntry,ConfigEntry

\* Servers states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse
      

\* Maximum number of client requests
CONSTANTS MaxClientRequests

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* Servers list all known servers.
VARIABLE allServers

\* The members of the server at that time.
VARIABLE votersOfServer

nodeVars == <<allServers, votersOfServer>>
----
\* The following variables are all per server (functions with domain Servers).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor, allServers, votersOfServer>>

\* The set of requests that can go into the log
VARIABLE clientRequests

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
\* The index that gets committed
VARIABLE committedLog
\* Does the commited Index decrease
VARIABLE committedLogDecrease
logVars == <<log, commitIndex, clientRequests, committedLog, committedLogDecrease>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(Server) == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Send a message.
Send(m) == messages' = messages \cup {m}

\* Remove a message from the set of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = messages \ {m}

\* Combination of Send and Discard.
Reply(reply, request) == messages' = (messages \cup {reply}) \ {request}

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Get the maximum config from log[1..l].
GetMaxConfigIndex(i, l) ==
    LET chonfigIndexes == {index \in 1..l: log[i][index].type = ConfigEntry}
    IN IF chonfigIndexes = {} THEN 0
       ELSE Max(chonfigIndexes)
\* Get the latest config in all log of server i.
GetLatestConfig(i) ==
    LET length == Len(log[i])
        maxIndex == GetMaxConfigIndex(i, length)
    IN IF maxIndex = 0 THEN InitialServers
       ELSE log[i][maxIndex].value
\* Get the latest commit config of server i.
GetLatestCommitConfig(i) ==
    LET length == commitIndex[i]
        maxIndex == GetMaxConfigIndex(i, length)
    IN IF maxIndex = 0 THEN InitialServers
       ELSE log[i][maxIndex].value

----
\* Define initial values for all variables
InitHistoryVars == /\ elections = {}
                   /\ voterLog  = [i \in allServers |-> [j \in {} |-> <<>>]]
                   
InitServerVars == /\ allServers = InitialServers \cup NewServers
                  /\ currentTerm = [i \in allServers |-> 1]
                  /\ state       = [i \in allServers |-> Follower]
                  /\ votedFor    = [i \in allServers |-> Nil]
                  /\ votersOfServer =
                     LET initalVoters == InitialServers
                         newVoters    == (InitialServers \cup NewServers) \ InitialServers  
                     IN [i \in initalVoters |-> initalVoters] @@ [i \in newVoters |-> {}]  
                        
InitCandidateVars == /\ votesResponded = [i \in allServers |-> {}]
                     /\ votesGranted   = [i \in allServers |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in allServers |-> [j \in allServers |-> 1]]
                  /\ matchIndex = [i \in allServers |-> [j \in allServers |-> 0]]
InitLogVars == /\ log          = [i \in allServers |-> << >>]
               /\ commitIndex  = [i \in allServers |-> 0]
               /\ clientRequests = 1
               /\ committedLog = << >>
               /\ committedLogDecrease = FALSE
Init == /\ messages = {}
        /\ InitServerVars
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* Servers i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars, nodeVars>>

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ j \in votersOfServer[i]
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, nodeVars>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in votersOfServer[i]
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN /\ Len(entries) > 0 /\ matchIndex[i][j] < Len(log[i])
          /\ Send([mtype          |-> AppendEntriesRequest,
                   mterm          |-> currentTerm[i],
                   mprevLogIndex  |-> prevLogIndex,
                   mprevLogTerm   |-> prevLogTerm,
                   mentries       |-> entries,
                   mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                   msource        |-> i,
                   mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, nodeVars>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum(votersOfServer[i])
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in allServers |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in allServers |-> 0]]
    /\ elections'  = elections \cup
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],
                           evotes    |-> votesGranted[i],
                           evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, nodeVars>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ clientRequests < MaxClientRequests
    /\ LET entry == [term  |-> currentTerm[i],
                     type  |-> ValueEntry,
                     value |-> clientRequests]
           newLog == Append(log[i], entry)
       IN /\ log' = [log EXCEPT ![i] = newLog]
          /\ clientRequests' = clientRequests + 1
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, committedLog, committedLogDecrease, nodeVars>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in allServers :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum(votersOfServer[i])}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           newCommittedLog ==
              IF newCommitIndex > 1
              THEN
                  [j \in 1..newCommitIndex |-> log[i][j]]
              ELSE
                  <<>>
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ committedLogDecrease' = \/ ( newCommitIndex < Len(committedLog))
                                     \/ \E j \in 1..Len(committedLog) : committedLog[j] /= newCommittedLog[j]
          /\ committedLog' = newCommittedLog
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, clientRequests>>

AdvanceCommitConfig(i) == 
    /\ GetMaxConfigIndex(i,commitIndex[i]) > 0
    /\ LET config == GetLatestCommitConfig(i)
       IN IF votersOfServer[i] /= config.newConf 
          THEN /\ \/ \* leader not in the new configuration.
                     \* switch to Follwer.
                     /\ i \notin config.newConf
                     /\ state[i] = Leader
                     /\ state' = [state EXCEPT ![i] = Follower]
                  \/ /\ i \in config.newConf
                     /\ UNCHANGED <<state>>
               /\ votersOfServer' = [ votersOfServer EXCEPT ![i] = config.newConf]
          ELSE UNCHANGED <<votersOfServer>>
    /\ UNCHANGED <<currentTerm, votedFor, candidateVars, leaderVars, logVars, nodeVars>>

    
\* Leader i add a group servers to cluster.
SetNodes(i, newNodes) ==
    /\ state[i] = Leader
    /\ \* for reducing the state space, just verify once.
       Len(SelectSeq(log[i], LAMBDA logEntry : logEntry.type = ConfigEntry)) = 0
    /\ LET oldConfig == votersOfServer[i]
           entry == [term    |-> currentTerm[i],
                     type    |-> ConfigEntry,
                     newConf |-> newNodes,
                     oldConf |-> oldConfig]
           transitionConfig == oldConfig \cup newNodes
           newLog == Append(log[i], entry)
       IN /\ log' = [log EXCEPT ![i] = newLog]
          /\ votersOfServer = [votersOfServer EXCEPT ![i] = transitionConfig]
    /\ UNCHANGED <<state, leaderVars, logVars, candidateVars, allServers>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, nodeVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, nodeVars>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, clientRequests, committedLog, committedLogDecrease>>
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
                                          log[i][index2]]
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages,clientRequests, committedLog, committedLogDecrease>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease>>
       /\ UNCHANGED <<candidateVars, leaderVars, nodeVars>>

\* Servers i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections, nodeVars>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, nodeVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, nodeVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Defines how the variables may transition.
Next == 
    \* Leader election
    \/ \E i,j \in allServers : RequestVote(i, j)
    \/ \E i \in allServers : BecomeLeader(i)
    \* Client request 
    \/ \E i \in allServers : ClientRequest(i)
    \* Config changed with joint consensus
    \/ \E i \in InitialServers: SetNodes(i, NewServers)
    \* Log replica
    \/ \E i \in allServers : AdvanceCommitIndex(i)
    \/ \E i \in allServers : AdvanceCommitConfig(i)
    \/ \E i,j \in allServers : AppendEntries(i, j)
    \* Network
    \/ \E m \in messages : Receive(m)
    \/ \/ /\ \A i \in allServers : state[i] = Follower
          /\ \E i \in allServers : Timeout(i)
       \/ /\ \E i \in allServers : state[i] /= Follower
          /\ UNCHANGED <<serverVars, candidateVars, messages, leaderVars, logVars, nodeVars>>


\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

----
\* The following are a set of verification.

MoreThanOneLeader ==
  Cardinality({i \in allServers: state[i]=Leader}) > 1

TransitionPhaseChecker == 
  \A i \in allServers: LET inTransition == /\ commitIndex[i] < GetMaxConfigIndex(i,Len(log[i])) 
                                           /\ GetMaxConfigIndex(i,Len(log[i])) > 0
                           configEntry  == GetLatestConfig(i)
                       IN IF inTransition THEN 
                             IF state[i] = Leader THEN
                                votersOfServer[i] = configEntry.oldConf \cup configEntry.newConf
                             ELSE votersOfServer[i] = configEntry.oldConf
                          ELSE TRUE
CommittedPhaseChecker ==
  \A i \in allServers: LET committed   == /\ commitIndex[i] > 0 
                                          /\ GetMaxConfigIndex(i,commitIndex[i]) > 0
                                          /\ commitIndex[i] > GetMaxConfigIndex(i,commitIndex[i]) 
                           configEntry == GetLatestCommitConfig(i)
                       IN IF committed THEN
                            votersOfServer[i] = configEntry.newConf
                          ELSE TRUE
                               
===============================================================================
