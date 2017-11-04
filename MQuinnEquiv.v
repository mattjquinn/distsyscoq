Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import MQuinnMaps.
Require Import MQuinnImp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof. intros st. simpl. omega. Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof. intros st. unfold beval.
  rewrite aequiv_example. reflexivity. Qed.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

Theorem skip_left : forall c,
  cequiv (SKIP ;; c) c.
Proof.
  intros c st st'. split; intros H.
  - inversion H. subst.
    inversion H2. subst.
    assumption.
  - apply E_Seq with st.
    apply E_Skip. apply H.
Qed.

Theorem skip_right : forall c, cequiv (c ;; SKIP) c.
Proof.
  intros c st st'. split; intros H.
  - inversion H. subst.
    inversion H5. subst. apply H2.
  - apply E_Seq with st'.
    apply H. apply E_Skip.
Qed.

Theorem IFB_true_simple : forall c1 c2,
  cequiv (IFB BTrue THEN c1 ELSE c2 FI) c1.
Proof.
  intros c1 c2 st st'. split; intros H.
  - inversion H; subst.
    + assumption.
    + inversion H5.
  - apply E_IfTrue; try reflexivity; assumption.
Qed.

Theorem IFB_true : forall b c1 c2,
  bequiv b BTrue -> cequiv (IFB b THEN c1 ELSE c2 FI) c1.
Proof.
  intros b1 c1 c2. unfold bequiv. intros HBTrue st st'.
  split; intros H.
  - inversion H; subst.
    + assumption.
    + rewrite HBTrue in H5. inversion H5.
  - specialize (HBTrue st). inversion HBTrue.
    apply E_IfTrue; assumption.
Qed.

Theorem IFB_false : forall b c1 c2,
  bequiv b BFalse ->
  cequiv (IFB b THEN c1 ELSE c2 FI) c2.
Proof.
  intros b c1 c2. unfold bequiv. intros HBFalse st st'.
  split; intros H; specialize (HBFalse st).
  - inversion H; subst.
    + rewrite HBFalse in H5. inversion H5.
    + assumption.
  - inversion HBFalse. apply E_IfFalse; assumption.
Qed.