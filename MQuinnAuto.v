Set Warnings "-notation-overridden,-parsing".
Require Import Coq.omega.Omega.
Require Import MQuinnMaps.
Require Import MQuinnImp.

Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic : forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2.
  - reflexivity.
  - reflexivity.
  - assert (st' = st'0) as EQ1.
    { apply IHE1_1; apply H1. }
  subst st'0.
  apply IHE1_2. assumption.
  - apply IHE1. assumption.
  - rewrite H in H5. inversion H5.
  - rewrite H in H5. inversion H5.
  - apply IHE1. assumption.
  - reflexivity.
  - rewrite H in H2. inversion H2.
  - rewrite H in H4. inversion H4.
  - assert (st' = st'0) as EQ1.
    { apply IHE1_1. assumption. }
    subst st'0.
    apply IHE1_2. assumption.
Qed.

Example auto_example_1 : forall (P Q R : Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.

Example auto_example_1' : forall (P Q R : Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof.
  auto.
Qed.

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  auto.
  auto 6.
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q \/ R).
Proof. auto. Qed.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto using le_antisym.
Qed.

Hint Resolve le_antisym.

Example auto_example_6' : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto.
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7 : forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7' : forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof. auto. Qed.

