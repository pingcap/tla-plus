-------------------------------- MODULE TwoPC --------------------------------
EXTENDS TLAPS

CONSTANTS RM, RMState, TMState, Msgs

VARIABLES rmState, tmState, tmPrepared, msgs

vars == <<rmState, tmState, tmPrepared, msgs>>

AXIOM RMStateAxiom ==
    /\ RMState = {"working", "prepared", "committed", "aborted"}

AXIOM TMStateAxiom ==
    /\ TMState = {"init", "committed", "aborted"}

AXIOM MsgsAxiom ==
    /\ Msgs = [type: {"prepared"}, rm: RM] \union [type: {"commit", "abort"}]

ExistAbortMsg ==
    /\ [type |-> "abort"] \in msgs

ExistCommitMsg ==
    /\ [type |-> "commit"] \in msgs

Init ==
    /\ rmState = [rm \in RM |-> "working"]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}

TMRcvPrepared(rm) ==
    /\ tmState = "init"
    /\ [type |-> "prepared", rm |-> rm] \in msgs
    /\ tmPrepared' = tmPrepared \union {rm}
    /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "committed"
    /\ msgs' = msgs \union {[type |-> "commit"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ msgs' = msgs \union {[type |-> "abort"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    /\ msgs' = msgs \union {[type |-> "prepared", rm |-> rm]}
    /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(rm) ==
    /\ ExistCommitMsg
    /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(rm) ==
    /\ ExistAbortMsg
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMOp(rm) ==
    \/ TMRcvPrepared(rm)
    \/ RMPrepare(rm)
    \/ RMChooseToAbort(rm)
    \/ RMRcvCommitMsg(rm)
    \/ RMRcvAbortMsg(rm)

ChooseRMOp ==
    /\ \E rm \in RM:
        /\ RMOp(rm)

Next ==
    \/ TMCommit
    \/ TMAbort
    \/ ChooseRMOp

Spec == Init /\ [][Next]_vars

RMStateTypeInvariant ==
    /\ rmState \in [RM -> RMState]

TMStateTypeInvariant ==
    /\ tmState \in TMState

TMPreparedTypeInvariant ==
    /\ tmPrepared \subseteq RM

MsgsTypeInvariant ==
    /\ msgs \subseteq Msgs

TypeInvariant ==
    /\ RMStateTypeInvariant
    /\ TMStateTypeInvariant
    /\ TMPreparedTypeInvariant
    /\ MsgsTypeInvariant

ExistCommittedRM ==
    /\ \E rm \in RM: rmState[rm] = "committed"

ExistAbortedRM ==
    /\ \E rm \in RM: rmState[rm] = "aborted"

Consistency ==
    /\ ExistCommittedRM => ~ExistAbortedRM
    /\ ExistAbortedRM => ~ExistCommittedRM

Invariant ==
    /\ TypeInvariant
    /\ ( tmState = "init" => 
         ( /\ \A rm \in RM : rmState[rm] # "committed"
           /\ \A rm \in RM : [type |-> "prepared", rm |-> rm] \in msgs <=> rmState[rm] = "prepared"
           /\ \A rm \in tmPrepared : rmState[rm] = "prepared" )
       )
    /\ ( tmState = "committed" =>
         ( /\ \A rm \in RM : (rmState[rm] = "committed" \/ rmState[rm] = "prepared") )
       )
    /\ ( tmState = "aborted" =>
         ( /\ \A rm \in RM : rmState[rm] # "committed" )
       )
    /\ tmState = "committed" <=> ExistCommitMsg
    /\ tmState = "aborted" <=> ExistAbortMsg

LEMMA InvariantImpliesConsistency ==
  Invariant => Consistency
<1> USE DEF TypeInvariant, TMStateTypeInvariant, RMStateTypeInvariant, TMPreparedTypeInvariant, MsgsTypeInvariant
<1> USE DEF Invariant, Consistency
<1> USE DEF ExistCommittedRM, ExistAbortedRM
<1>a CASE tmState = "init"
  <2> QED BY <1>a, RMStateAxiom 
<1>b CASE tmState = "committed"
  <2> QED BY <1>b, RMStateAxiom 
<1>c CASE tmState = "aborted"
  <2> QED BY <1>c, RMStateAxiom 
<1> QED BY <1>a, <1>b, <1>c, TMStateAxiom

LEMMA InitStateSatisfiesInvariant ==
  Init => Invariant
<1> USE DEF TypeInvariant, TMStateTypeInvariant, RMStateTypeInvariant, TMPreparedTypeInvariant, MsgsTypeInvariant
<1> USE DEF Init, Invariant, ExistCommitMsg, ExistAbortMsg
<1> QED BY TMStateAxiom, RMStateAxiom, MsgsAxiom

LEMMA StateStepKeepsInvariant ==
  Invariant /\ Next => Invariant'
<1> USE DEF TypeInvariant, TMStateTypeInvariant, RMStateTypeInvariant, TMPreparedTypeInvariant, MsgsTypeInvariant
<1> USE DEF Invariant, Next
<1> USE DEF ExistCommitMsg, ExistAbortMsg
<1> USE DEF TMCommit, TMAbort, ChooseRMOp
<1> USE DEF RMOp, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg
<1> USE TMStateAxiom, RMStateAxiom, MsgsAxiom
<1>a CASE TMCommit BY <1>a
<1>b CASE TMAbort BY <1>b
<1>c CASE ChooseRMOp
  <2> PICK rm \in RM : RMOp(rm) BY <1>c
  <2>a CASE TMRcvPrepared(rm) BY <2>a
  <2>b CASE RMPrepare(rm) BY <2>b
  <2>c CASE RMChooseToAbort(rm) BY <2>c
  <2>d CASE RMRcvCommitMsg(rm) BY <2>d
  <2>e CASE RMRcvAbortMsg(rm) BY <2>e
  <2> QED BY <2>a, <2>b, <2>c, <2>d, <2>e
<1> QED BY <1>a, <1>b, <1>c

THEOREM Safety ==
  Spec => []Consistency
<1> SUFFICES Spec => []Invariant BY InvariantImpliesConsistency, PTL
<1> SUFFICES ASSUME Init /\ [][Next]_vars PROVE []Invariant BY DEF Spec
<1> QED BY InitStateSatisfiesInvariant, StateStepKeepsInvariant, PTL

=============================================================================
