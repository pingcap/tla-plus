Require Import List Bool Arith.
Require Import TwoPC.Crush TwoPC.Learn.

(** The collection of resource managers (RM). *)
Axiom RM : Type.

(** Assumes two RMs are distinguishable. *)
Axiom RMDecidable :
  forall x y : RM, { x = y } + { x <> y }.

Inductive RMState : Set :=
  RMWorking | RMPrepared | RMCommitted | RMAborted.

Inductive TMState : Set :=
| TMInit | TMCommitted | TMAborted.

Inductive Message : Type :=
  MsgPrepared : RM -> Message
| MsgCommit | MsgAbort.

Record State := {
  rmState : RM -> RMState;
  tmState : TMState;
  tmPrepared : RM -> bool;
  msgs : list Message
}.

Inductive StateInit : State -> Prop :=
| InitIntro :
    forall (rmInit : RM -> RMState) (tmPreparedInit : RM -> bool),
    (forall rm, rmInit rm = RMWorking /\ tmPreparedInit rm = false) ->
    StateInit {| rmState := rmInit;
                 tmState := TMInit;
                 tmPrepared := tmPreparedInit;
                 msgs := nil |}.

Inductive StateStep : State -> State -> Prop :=
| TMRcvPrepared :
    forall rm rmState tmState msgs tmPrepared tmPrepared',
      tmState = TMInit ->
      In (MsgPrepared rm) msgs ->
      (forall rm0, rm0 <> rm -> tmPrepared rm0 = tmPrepared' rm0) ->
      tmPrepared' rm = true ->
      StateStep {| rmState := rmState;
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}
                {| rmState := rmState;
                   tmState := tmState;
                   tmPrepared := tmPrepared';
                   msgs := msgs |}

| TMCommit :
    forall rmState tmState tmState' tmPrepared msgs msgs',
      tmState = TMInit ->
      (forall rm, tmPrepared rm = true) ->
      tmState' = TMCommitted ->
      msgs' = cons MsgCommit msgs ->
      StateStep {| rmState := rmState;
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}
                {| rmState := rmState;
                   tmState := tmState';
                   tmPrepared := tmPrepared;
                   msgs := msgs' |}

| TMAbort :
    forall rmState tmState tmState' tmPrepared msgs msgs',
      tmState = TMInit ->
      tmState' = TMAborted ->
      msgs' = cons MsgAbort msgs ->
      StateStep {| rmState := rmState;
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}
                {| rmState := rmState;
                   tmState := tmState';
                   tmPrepared := tmPrepared;
                   msgs := msgs' |}

| RMPrepare :
    forall rm rmState rmState' tmState tmPrepared msgs msgs',
      rmState rm = RMWorking ->
      (forall rm0, rm0 <> rm -> rmState rm0 = rmState' rm0) ->
      rmState' rm = RMPrepared ->
      msgs' = cons (MsgPrepared rm) msgs ->
      StateStep {| rmState := rmState;
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}
                {| rmState := rmState';
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs' |}

| RMChooseToAbort :
    forall rm rmState rmState' tmState tmPrepared msgs,
      rmState rm = RMWorking ->
      (forall rm0, rm0 <> rm -> rmState rm0 = rmState' rm0) ->
      rmState' rm = RMAborted ->
      StateStep {| rmState := rmState;
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}
                {| rmState := rmState';
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}

| RMRcvCommitMsg :
    forall rm rmState rmState' tmState tmPrepared msgs,
      In MsgCommit msgs ->
      (forall rm0, rm0 <> rm -> rmState rm0 = rmState' rm0) ->
      rmState' rm = RMCommitted ->
      StateStep {| rmState := rmState;
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}
                {| rmState := rmState';
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}

| RMRcvAbortMsg :
    forall rm rmState rmState' tmState tmPrepared msgs,
      In MsgAbort msgs ->
      (forall rm0, rm0 <> rm -> rmState rm0 = rmState' rm0) ->
      rmState' rm = RMAborted ->
      StateStep {| rmState := rmState;
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}
                {| rmState := rmState';
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}.

Inductive StateMultiStep : State -> State -> Prop :=
| StateMultiStep0 :
    forall state,
      StateMultiStep state state
| StateMultiStep1 :
    forall state state1 state2,
      StateMultiStep state1 state2 ->
      StateMultiStep state state1 ->
      StateMultiStep state state2.

Inductive Consistency : State -> Prop :=
| ConsistencyIntro :
    forall rmState tmState tmPrepared msgs,
      ( (* if one RM is committed, other RMs cannot be aborted. *)
        (exists rm, rmState rm = RMCommitted) ->
        (forall rm, rmState rm <> RMAborted)
      ) ->
      ( (* if one RM is aborted, other RMs cannot be committed. *)
        (exists rm, rmState rm = RMAborted) ->
        (forall rm, rmState rm <> RMCommitted)
      ) ->
      Consistency {| rmState := rmState;
                     tmState := tmState;
                     tmPrepared := tmPrepared;
                     msgs := msgs |}.

Inductive Invariant : State -> Prop :=
| InvariantIntro :
    forall rmState tmState tmPrepared msgs,
      (
        tmState = TMInit -> (* 1PC *)
        (
          (forall rm, rmState rm <> RMCommitted) /\
          (forall rm, (In (MsgPrepared rm) msgs <-> rmState rm = RMPrepared)) /\
          (forall rm, tmPrepared rm = true -> rmState rm = RMPrepared)
        )
      ) ->
      ( (* 2PC: Commit *)
        tmState = TMCommitted ->
        (
          forall rm, rmState rm = RMCommitted \/ rmState rm = RMPrepared
        )
      ) ->
      ( (* 2PC: Abort *)
        tmState = TMAborted ->
        (
          forall rm, rmState rm <> RMCommitted
        )
      ) ->
      ( (* Abort message in message list <==> TM is aborted *)
        In MsgAbort msgs <-> tmState = TMAborted
      ) ->
      ( (* Committed message in message list <==> TM is committed *)
        In MsgCommit msgs <-> tmState = TMCommitted
      ) ->
      Invariant {| rmState := rmState;
                   tmState := tmState;
                   tmPrepared := tmPrepared;
                   msgs := msgs |}.

Ltac inst_rm x :=
  repeat
    ( match goal with
      | [ H: forall rm, _ |- _ ] => learn (H x)
      end
    );
  repeat
    ( match goal with
      | [ H : Learnt |- _ ] => clear H
      end
    ).

Ltac invert H := inversion H; subst; clear H.

Lemma InvariantImpliesConsistency :
  forall state, Invariant state -> Consistency state.
Proof.
  intros.
  invert H. constructor; crush.
  + destruct tmState0; crush;
      try (inst_rm x; crush);
      try (inst_rm rm; crush).
  + destruct tmState0; crush;
      try (inst_rm x; crush);
      try (inst_rm rm; crush).
Qed.

Lemma InitStateSatisfiesInvariant :
  forall state, StateInit state -> Invariant state.
Proof.
  intros.
  invert H; constructor; crush;
    try (inst_rm x); try (inst_rm rm); crush.
Qed.

Lemma StateStepKeepsInvariant :
  forall state state',
    StateStep state state' ->
    Invariant state ->
    Invariant state'.
Proof.
  intros.
  invert H0; invert H.
  + constructor; crush.
    destruct (RMDecidable rm0 rm).
    - inst_rm rm; crush.
    - inst_rm rm0; eauto.
  + constructor; crush.
  + constructor; crush.
  + destruct tmState0.
    - constructor; crush;
      destruct (RMDecidable rm0 rm); crush; inst_rm rm; inst_rm rm0; crush.
    - crush. inst_rm rm; crush.
    - constructor; crush;
      destruct (RMDecidable rm0 rm); crush; inst_rm rm; inst_rm rm0; crush.
  + destruct tmState0.
    - constructor; crush;
      destruct (RMDecidable rm0 rm); crush; inst_rm rm; inst_rm rm0; crush.
    - crush. inst_rm rm; crush.
    - constructor; crush;
      destruct (RMDecidable rm0 rm); crush; inst_rm rm; inst_rm rm0; crush.
  + constructor; crush.
    destruct (RMDecidable rm0 rm).
    - crush.
    - inst_rm rm0; crush.
      left; crush.
      right; crush.
  + constructor; crush.
    destruct (RMDecidable rm0 rm).
    - crush.
    - inst_rm rm0; crush.
Qed.

Lemma Safety' :
  forall state state',
    StateMultiStep state state' ->
    Invariant state ->
    Invariant state'.
Proof.
  induction 1; crush.
Qed.

Theorem Safety :
  forall state state',
    StateMultiStep state state' ->
    StateInit state ->
    Consistency state'.
Proof.
  intros.
  apply InvariantImpliesConsistency.
  apply InitStateSatisfiesInvariant in H0.
  eapply Safety'; eauto.
Qed.
