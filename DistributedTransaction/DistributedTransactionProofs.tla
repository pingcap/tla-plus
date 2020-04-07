--------------------- MODULE DistributedTransactionProofs -------------------
EXTENDS DistributedTransaction, TLAPS

THEOREM SpecTypeOK == Spec => TypeOK
  PROOF OMITTED

LEMMA NextInv == 
  Next =>
    /\ next_ts' = next_ts + 1 \/ UNCHANGED next_ts
    /\ \E reqs : SendReqs(reqs) \/ UNCHANGED req_msgs
    /\ \E resp : SendResp(resp) \/ UNCHANGED resp_msgs
  BY DEF Next, vars, msg_vars,
         ClientPrewriteOptimisistic, ClientPrewrited, ClientCommit, ClientLockKey, 
         ClientLockedKey, ClientRetryLockKey, ClientPrewritePessimistic,
         ClientPrewrited, ClientCommit, ServerLockKey, ServerPrewritePessimistic,
         ServerPrewriteOptimistic, ServerCommit, ServerCleanupStaleLock,
         ServerCleanup, ServerResolveCommitted, ServerResolveRollbacked

LEMMA SpecNextTsMonotonicity == Spec => NextTsMonotonicity
  <1> SUFFICES ASSUME NEW ts \in Ts, TypeOK
               PROVE  (ts <= next_ts) /\ [][Next]_vars => [](ts <= next_ts)
    BY SpecTypeOK DEF NextTsMonotonicity, Spec
  <1>2. (ts <= next_ts) /\ [Next]_vars => (ts <= next_ts)'
    BY NextInv DEF TypeOK, Ts, vars
  <1>3. QED
    BY <1>2, PTL

LEMMA SpecMsgMonotonicity == Spec => MsgMonotonicity
  <1>1. ASSUME NEW req \in ReqMessages
        PROVE  req \in req_msgs /\ [][Next]_vars => [](req \in req_msgs)
    <2>1. req \in req_msgs /\ (\E reqs : SendReqs(reqs)) => (req \in req_msgs)'
      BY DEF SendReqs
    <2>2. req \in req_msgs /\ [Next]_vars => (req \in req_msgs)'
      BY <2>1, NextInv DEF vars, msg_vars
    <2>3. QED
      BY <2>2, PTL
  <1>2. ASSUME NEW resp \in RespMessages
        PROVE  resp \in resp_msgs /\ [][Next]_vars => [](resp \in resp_msgs)
    <3>1. resp \in resp_msgs /\ (\E resp2 : SendResp(resp2)) => (resp \in resp_msgs)'
      BY DEF SendResp
    <3>2. resp \in resp_msgs /\ [Next]_vars => (resp \in resp_msgs)'
      BY <3>1, NextInv DEF vars, msg_vars
    <3>3. QED
      BY <3>2, PTL
  <1>3. QED
    BY <1>1, <1>2, SpecTypeOK DEF MsgMonotonicity, Spec
=============================================================================
