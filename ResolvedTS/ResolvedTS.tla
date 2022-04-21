----------------------------- MODULE ResolvedTS -----------------------------
EXTENDS Integers, Sequences

\* RM is a set of keys in a region
CONSTANT RM

VARIABLES
    rmState, \* State of each region keys.
    reState, \* ResolvedTS resolver state.
    nextTS,  \* TSO.
    resolvedQueue, \* A queue where resolved ts saves.
    outputTSQueue, \* A queue where commit ts saves.
    chan,          \* A channel forwards messages to a resolver.
    chanOffset     \* An offset indicates how many messages have been handled.

vars == <<rmState, reState, nextTS,
          resolvedQueue, outputTSQueue,
          chan, chanOffset>>

Messages ==
    [type: {"Prewrite", "Commit", "Rollback"}, rm: RM, ts: Nat]
    \cup
    [type: {"FetchTS"}, ts: Nat]

\* A pair of resolved ts and a index to the outputQueue.
ResolvedItem == [ts: Nat, index: Nat]

RTTypeOK ==
    /\ rmState  \in [RM -> [state: {"prewrited", "committed"},
                           pTS: Nat, cTS: Nat,
                           msgs: Seq(Messages), appliedOffset: Nat]]
    /\ reState  \in [RM -> [minPTS: Nat]]
    /\ nextTS   \in Nat
    /\ resolvedQueue    \in Seq([ts: Nat, index: Nat])
    /\ outputTSQueue    \in Seq(Nat)
    /\ chan             \in Seq(Messages)
    /\ chanOffset       \in Nat

RTInit ==
    /\  rmState = [r \in RM |-> [state |-> "committed",
                   pTS |-> 0, cTS |-> 0,
                   msgs |-> << >>, appliedOffset |-> 0]]
    /\  reState = [r \in RM |-> [minPTS |-> 0]]
    /\  nextTS = 100 \* In practical, nextTS should be a nonzero value.
    /\  resolvedQueue = << >>
    /\  outputTSQueue = << >>
    /\  chan = << >>
    /\ chanOffset = 0

PessimisticPrewrite(r) ==
    LET t == nextTS - 2 \* Pessimistic Txns start TS can be stale.
    IN  /\ rmState[r].state = "committed"
        /\ rmState' = [rmState  EXCEPT  ![r].state = "prewrited",
                                        ![r].pTS = t,
                                        ![r].msgs = Append(rmState[r].msgs,
                                                        [type |-> "Prewrite",
                                                         rm |-> r, ts |-> t])]
        /\ nextTS' = nextTS + 1
        /\ UNCHANGED <<resolvedQueue, outputTSQueue, reState, chan, chanOffset>>

Prewrite(r) ==
    LET t == nextTS + 1
    IN  /\ rmState[r].state = "committed"
        /\ rmState' = [rmState  EXCEPT  ![r].state = "prewrited",
                                        ![r].pTS = t,
                                        ![r].msgs = Append(rmState[r].msgs,
                                                        [type |-> "Prewrite",
                                                         rm |-> r, ts |-> t])]
        /\ nextTS' = nextTS + 1
        /\ UNCHANGED <<resolvedQueue, outputTSQueue, reState, chan, chanOffset>>

\* Before taking Commit or Rollback action,
\* it must ensure all previous prewrites have been applied.
HasLastPrewriteApplied(r) ==
    LET rm == rmState[r]
    IN  /\ rm.state = "prewrited"
        /\ Len(rm.msgs) = rm.appliedOffset
        /\ rm.msgs[Len(rm.msgs)].type = "Prewrite"

Commit(r) ==
    LET t == nextTS + 1
    IN  /\ HasLastPrewriteApplied(r) \* prewrite applied
        /\ rmState' = [rmState  EXCEPT  ![r].state = "committed",
                                        ![r].cTS = t,
                                        ![r].msgs = Append(rmState[r].msgs,
                                                        [type |-> "Commit",
                                                         rm |-> r, ts |-> t])]
        /\ nextTS' = nextTS + 1
        /\ UNCHANGED <<resolvedQueue, outputTSQueue, reState, chan, chanOffset>>

Rollback(r) ==
    /\ HasLastPrewriteApplied(r) \* prewrite applied
    /\ rmState' = [rmState  EXCEPT  ![r].state = "committed",
                                    ![r].pTS = 0,
                                    ![r].msgs = Append(rmState[r].msgs,
                                                    [type |-> "Rollback",
                                                     rm |-> r, ts |-> 0])]
    /\ UNCHANGED    <<nextTS, resolvedQueue, outputTSQueue, reState,
                     chan, chanOffset>>

\* Apply advances appliedOffset and forward corresponding message to the chan.
Apply ==
    /\ \E r \in RM:
        LET appliedOffset == rmState[r].appliedOffset
        IN  /\ appliedOffset < Len(rmState[r].msgs)
            /\ rmState' =
                [rmState  EXCEPT ![r].appliedOffset = appliedOffset + 1]
            /\ chan' = Append(chan, rmState[r].msgs[appliedOffset + 1])
    /\ UNCHANGED <<nextTS, resolvedQueue, outputTSQueue, reState, chanOffset>>

TxnEventsWithPessimistic ==
    \/ \E r \in RM:
        \/ PessimisticPrewrite(r)
        \/ Prewrite(r)
        \/ Commit(r)
        \/ Rollback(r)
    \/ Apply

TxnEvents ==
    \/ \E r \in RM:
        \/ Prewrite(r)
        \/ Commit(r)
        \/ Rollback(r)
    \/ Apply

Min(s) ==
    IF s = {} THEN 0
    ELSE CHOOSE n \in s: \A m \in s: n \leq m

Max(s) ==
    IF s = {} THEN 0
    ELSE CHOOSE n \in s: \A m \in s: n \geq m

FetchTS ==
    /\ nextTS' = nextTS + 1 \* Try not to blew up
                            \* state space by increasing nextTS
    /\ LET resolvedTS == IF Len(resolvedQueue) = 0 THEN 0
                         ELSE resolvedQueue[Len(resolvedQueue)].ts
           cTS == nextTS - 0 \* A random offset, means cTS may be stale.
       IN /\ chan' = Append(chan, [type |-> "FetchTS", ts |-> cTS])
          /\ UNCHANGED <<rmState, reState, chanOffset,
                         resolvedQueue, outputTSQueue>>

TryResolve(cTS) ==
    LET nonZero == {r \in RM: reState[r].minPTS > 0}
        min == Min({reState[re].minPTS: re \in nonZero} \cup {cTS})
    IN  LET nextIndex == Len(outputTSQueue) + 1
            lastResolvedTS ==   IF resolvedQueue = << >> THEN 0
                                ELSE resolvedQueue[Len(resolvedQueue)].ts
            newResolvedTS == Max({lastResolvedTS, min})
        IN  IF newResolvedTS # lastResolvedTS
            THEN /\ outputTSQueue' = Append(outputTSQueue, newResolvedTS)
                 /\ resolvedQueue' = Append(resolvedQueue,
                                                [ts |-> newResolvedTS,
                                                index |-> nextIndex + 1])
            ELSE UNCHANGED <<resolvedQueue, outputTSQueue>>

\* Check if the type of the next message in the chan equals to ty.
CanHandleMsg(ty) ==
    /\ chanOffset < Len(chan)
    /\ chanOffset' = chanOffset + 1
    /\ chan[chanOffset + 1].type = ty

HandleMsgFetchTS ==
    /\ CanHandleMsg("FetchTS")
    /\  LET m == chan[chanOffset + 1]
        IN  /\ TryResolve(m.ts)
            /\ UNCHANGED <<nextTS, rmState, reState, chan>>

HandleMsgPrewrite ==
    /\ CanHandleMsg("Prewrite")
    /\  LET m == chan[chanOffset + 1]
        IN  /\ reState' = [reState EXCEPT ![m.rm].minPTS = m.ts]
            /\ UNCHANGED <<nextTS, rmState, outputTSQueue, resolvedQueue, chan>>

HandleMsgCommit ==
    /\ CanHandleMsg("Commit")
    /\  LET m == chan[chanOffset + 1]
        IN  /\ reState' = [reState EXCEPT ![m.rm].minPTS = 0]
            /\ outputTSQueue' = Append(outputTSQueue, m.ts)
            /\ UNCHANGED <<nextTS, rmState, resolvedQueue, chan>>

HandleMsgRollback ==
    /\ CanHandleMsg("Rollback")
    /\  LET m == chan[chanOffset + 1]
        IN  /\ reState' = [reState EXCEPT ![m.rm].minPTS = 0]
            /\ UNCHANGED <<nextTS, rmState, resolvedQueue, chan>>

HandleMsg ==
    \/ HandleMsgPrewrite
    \/ HandleMsgCommit
    \/ HandleMsgFetchTS

RTNext ==
    \/ TxnEvents
    \/ FetchTS
    \/ HandleMsg

RTNextWithPessimistic ==
    \/ TxnEventsWithPessimistic
    \/ FetchTS
    \/ HandleMsg

RTSpec == RTInit /\ [][RTNext]_vars

RTSpecWithPessimistic == RTInit /\ [][RTNextWithPessimistic]_vars

\* Even if there is no write, it can always output
\* resolved ts solely by FetchTS.
ResolveLiveness ==
    (/\ \A rm \in RM: /\ reState[rm].minPTS = 0
     /\ \E i \in 1..Len(chan): chan[i].type = "FetchTS" /\ i < chanOffset)
        ~> Len(resolvedQueue) # 0

CommitConsistency ==
    \A rm \in RM:
        rmState[rm].state = "committed" =>
            \/ (/\ rmState[rm].pTS < rmState[rm].cTS)
            \/ (/\ rmState[rm].pTS = rmState[rm].cTS
                /\ rmState[rm].pTS = 0)

ResolvedConsistency ==
    \A i \in 1..Len(resolvedQueue):
        LET resolved == resolvedQueue[i]
            index == resolved.index
            resolvedTS == resolved.ts
        IN  index \geq Len(outputTSQueue) =>
                \A j \in index..Len(outputTSQueue):
                    resolvedTS < outputTSQueue[j]

--------------------------------------------------------------------------------
THEOREM Safety ==
  RTSpec => [](/\ CommitConsistency
               /\ ResolvedConsistency
               /\ RTTypeOK)

=============================================================================
\* Modification History
\* Last modified Sat Oct 19 16:12:36 CST 2019 by neil
\* Created Sat Oct 12 14:01:32 CST 2019 by neil
