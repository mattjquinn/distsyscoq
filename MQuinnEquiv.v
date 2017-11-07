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

Theorem swap_if_branches : forall b e1 e2,
  cequiv (IFB b THEN e1 ELSE e2 FI)
         (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2 st st'. split; intros H.
  - inversion H; subst.
    + apply E_IfFalse.
      * simpl. rewrite H5. reflexivity.
      * assumption.
    + apply E_IfTrue.
      * simpl. rewrite H5. reflexivity.
      * assumption.
  - inversion H; subst; simpl in *.
    + apply E_IfFalse.
      * simpl. symmetry in H5. apply negb_sym in H5.
        rewrite H5. reflexivity.
      * assumption.
    + apply E_IfTrue.
      * simpl. symmetry in H5. apply negb_sym in H5.
        rewrite H5. reflexivity.
      * assumption.
Qed.

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
    cequiv (WHILE b DO c END) SKIP.
Proof.
  intros b c HBFalse st st'. split; intros H; unfold bequiv in HBFalse.
  - inversion H; subst.
    + apply E_Skip.
    + rewrite HBFalse in H2. inversion H2.
  - inversion H. subst. apply E_WhileEnd.
    rewrite HBFalse. reflexivity.
Qed.

(* Informal proof of WHILE_false:

   Theorem: If b is equivalent to False, WHILE b DO c END is equivalent
            to SKIP.

   Proof: By case analyzing the possible constructions WHILE and SKIP.
    ( -> ) : We have assumed (WHILE b DO c END) / st \\ st'; b
             could be either True or False.
          ( b = False ) -> Then our goal is SKIP / st' \\ st',
                           which is trivially true.
          ( b = True ) -> This contradicts our assumption that b is
                          equivalent to False, so it can be discharged.
    ( <- ) : We now assume SKIP / st \\ st'. By definition of SKIP,
             st must be equal to st', so we can rewrite our assumption
             to SKIP / st' \\ st' and our goal to (WHILE ... ) / st' \\ st'.
             This is provable if b is equivalent to False, which
             is indeed our original assumption.
Qed.
*)

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  intros b c st st' Hb H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H; inversion Heqcw; subst; clear Heqcw.
  - unfold bequiv in Hb.
    rewrite Hb in H. inversion H.
  - apply IHceval2. reflexivity.
Qed.

(* WHILE_true_nonterm -> in English:
   For all boolean expressions equivalent to True, there
   is no WHILE loop that will bring any state st to any other
   state st' by way of executing any command c.
*)

Theorem WHILE_true : forall b c,
  bequiv b BTrue ->
  cequiv (WHILE b DO c END) (WHILE BTrue DO SKIP END).
Proof.
  intros b c HBTrue st st'. split; intros H.
  - apply (WHILE_true_nonterm b c st st') in HBTrue.
    unfold not in HBTrue. apply HBTrue in H. destruct H.
  - remember (WHILE BTrue DO SKIP END) as cw eqn:Heqcw.
    induction H; inversion Heqcw; subst.
    + inversion H.
    + inversion H0. subst. apply IHceval2. reflexivity.
Qed.

Theorem loop_unrolling : forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'. split; intros H.
  - inversion H; subst.
    + apply E_IfFalse. assumption. apply E_Skip.
    + apply E_IfTrue.
      * assumption.
      * apply E_Seq with st'0; assumption.
  - inversion H; subst; inversion H6; subst.
    + apply E_WhileLoop with st'0; assumption.
    + apply E_WhileEnd. assumption.
Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros c1 c2 c3 st st'. split; intros H.
  - inversion H; subst. inversion H2; subst.
    apply E_Seq with st'1. assumption.
    apply E_Seq with st'0; assumption.
  - inversion H; subst. inversion H5. subst.
    apply E_Seq with st'1; try assumption.
    apply E_Seq with st'0; assumption.
Qed.

Theorem identity_assignment : forall (X : id),
  cequiv (X ::= AId X) SKIP.
Proof.
  intros X st st'. split; intros H.
  - inversion H. subst. simpl. rewrite t_update_same.
    apply E_Skip.
  - replace st' with (t_update st' X (aeval st' (AId X))).
    + inversion H. subst. apply E_Ass. reflexivity.
    + simpl. rewrite t_update_same. reflexivity.
Qed.

Theorem assign_equiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  intros X e H st st'. split; intros H1; unfold aequiv in H.
  - replace st' with (t_update st X (aeval st e)).
    + apply E_Ass. reflexivity.
    + rewrite <- H. simpl.
      rewrite t_update_same.
      inversion H1. subst. reflexivity.
  - inversion H1. subst. rewrite <- H. simpl.
    rewrite t_update_same. apply E_Skip.
  (* I got stuck on this one because I tried to replace
     (AId X) with e; I could apply identity_assignment, but then
     needed to prove (AId X)'s equality with e. This of course is
     not possible; only the outcomes of their evaluation are equivalent.
     By replacing the final st' with its corresponding form of
     t_update, we can switch (aeval st e) out with (aeval st (AId X))
     [via our assumption that (AId X) and e are equivalent expressions]
     as necessary to prove its reduction to starting state st. *)
Qed.

Definition prog_a : com :=
  WHILE BNot (BLe (AId X) (ANum 0)) DO
    X ::= APlus (AId X) (ANum 1)
  END.
  (* While X > 0, x = x + 1 (INFINITE LOOP). *)

Definition prog_b : com :=
  IFB BEq (AId X) (ANum 0) THEN
    X ::= APlus (AId X) (ANum 1);;
    Y ::= ANum 1
  ELSE
    Y ::= ANum 0
  FI;;
  X ::= AMinus (AId X) (AId Y);;
  Y ::= ANum 0.
  (* If X is 0, then X and Y are set to 1.
      otherwise, X remains same and Y is set to 0.
     X is set to X - Y.
     Y is set to 0. *)

Definition prog_c : com :=
  SKIP.

Definition prog_d : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= APlus (AMult (AId X) (AId Y)) (ANum 1)
  END.
  (* While X != 0, X is set to (X*Y) + 1. (INFINITE LOOP) *)

Definition prog_e : com :=
  Y ::= ANum 0.
  (* Y is set to 0. *)

Definition prog_f : com :=
  Y ::= APlus (AId X) (ANum 1);;
  WHILE BNot (BEq (AId X) (AId Y)) DO
    Y ::= APlus (AId X) (ANum 1)
  END.
  (* Y is set to X + 1.
     While X != Y, Y is set to X + 1. (INFINITE LOOP) *)

Definition prog_g : com :=
  WHILE BTrue DO
    SKIP
  END. (* INFINITE LOOP *)

Definition prog_h : com :=
  WHILE BNot (BEq (AId X) (AId X)) DO
    X ::= APlus (AId X) (ANum 1)
  END. (* While X != X, X = X + 1 (EQUIV TO SKIP) *)

Definition prog_i : com :=
  WHILE BNot (BEq (AId X) (AId Y)) DO
    X ::= APlus (AId Y) (ANum 1)
  END. (* While X != Y, X = Y + 1.
          (Equivalent to SKIP or INFINITE LOOP depending
           on initial state. *)

Definition equiv_classes : list (list com) :=
  [ [prog_a; prog_d; prog_f; prog_g] ; [prog_b] ;
    [prog_c; prog_h] ; [prog_e] ; [prog_i] ].

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof. unfold aequiv. intros. reflexivity. Qed.

Lemma sym_equiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof. unfold aequiv. intros. symmetry. apply H. Qed.

Lemma trans_equiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof. unfold aequiv. intros. rewrite H. apply H0. Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof. unfold bequiv. intros. reflexivity. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof. unfold bequiv. intros. symmetry. apply H. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof. unfold bequiv. intros. rewrite H. apply H0. Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof. unfold cequiv. intros. reflexivity. Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof. unfold cequiv. intros. symmetry. apply H. Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof. intros. rewrite H. apply H0. Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof. unfold cequiv. intros.
  apply iff_trans with (c2 / st \\ st'). apply H. apply H0. Qed.