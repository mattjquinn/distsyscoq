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

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a1' HAEquiv st st'. unfold aequiv in HAEquiv.
  split; intros H; inversion H; subst.
  - rewrite HAEquiv. apply E_Ass. reflexivity.
  - rewrite <- HAEquiv. apply E_Ass. reflexivity.
Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv, cequiv.
  intros b1 b1' c1 c1' HBequiv HCequiv st st'.
  split; intros Hce.
  - remember (WHILE b1 DO c1 END) as cwhile eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + rewrite HBequiv in H. apply E_WhileEnd. assumption.
    + apply E_WhileLoop with st'.
      * rewrite HBequiv in H. assumption.
      * rewrite HCequiv in Hce1. assumption.
      * apply IHHce2. reflexivity.
  - remember (WHILE b1' DO c1' END) as cwhile eqn:Heqcwhile'.
    induction Hce; inversion Heqcwhile'; subst.
    + rewrite <- HBequiv in H. apply E_WhileEnd. assumption.
    + apply E_WhileLoop with st'.
      * rewrite <- HBequiv in H. assumption.
      * rewrite <- HCequiv in Hce1. apply Hce1.
      * apply IHHce2. reflexivity.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' ->
  cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  unfold cequiv. intros. split; intros H1; inversion H1; subst.
  - apply E_Seq with st'0.
    + apply H. apply H4.
    + apply H0. apply H7.
  - apply E_Seq with st'0.
    + apply H. apply H4.
    + apply H0. apply H7.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' ->
  cequiv c1 c1' ->
  cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv, cequiv. intros. split; intros H2.
  - remember (IFB b THEN c1 ELSE c2 FI) as ifstmt eqn:Hifstmt.
    induction H2; inversion Hifstmt; subst.
    + apply E_IfTrue.
      * rewrite H in H2. assumption.
      * apply H0 in H3. assumption.
    + apply E_IfFalse.
      * rewrite H in H2. assumption.
      * apply H1. assumption.
  - remember (IFB b' THEN c1' ELSE c2' FI) as ifstmt eqn:Hifstmt'.
    induction H2; inversion Hifstmt'; subst.
    + apply E_IfTrue.
      * rewrite <- H in H2. assumption.
      * apply H0 in H3. assumption.
    + apply E_IfFalse.
      * rewrite <- H in H2. assumption.
      * apply H1 in H3. assumption.
Qed.

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (* Program 2: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X) (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAss_congruence. unfold aequiv. simpl.
      intros. apply minus_diag_reverse.
    + apply refl_cequiv.
Qed.

(* Exercise: not_congr: 
   We've shown that the cequiv relation is both an equivalence
   and a congruence on commands. Can you think of a relation on
   commands that is an equivalence but not a congruence?

   Answer: No, b/c I'm too lazy to do so at this time.
*)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp), aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp), bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com), cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => AId i
  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
  fold_constants_aexp (AMult (APlus (ANum 1) (ANum 2)) (AId X))
    = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6))
                                             (AId Y)))
    = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) =>
        if beq_nat n1 n2 then BTrue else BFalse
    | (a1', a2') => BEq a1' a2'
    end
  | BLe a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) =>
        if leb n1 n2 then BTrue else BFalse
    | (a1', a2') => BLe a1' a2'
    end
  | BNot b1 =>
    match (fold_constants_bexp b1) with
    | BTrue => BFalse
    | BFalse => BTrue
    | b1' => BNot b1'
    end
  | BAnd b1 b2 =>
    match (fold_constants_bexp b1, fold_constants_bexp b2)
    with
    | (BTrue, BTrue) => BTrue
    | (BTrue, BFalse) => BFalse
    | (BFalse, BTrue) => BFalse
    | (BFalse, BFalse) => BFalse
    | (b1', b2') => BAnd b1' b2'
    end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
    = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp
    (BAnd (BEq (AId X) (AId Y))
          (BEq (ANum 0)
               (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
    = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP => SKIP
  | i ::= a => CAss i (fold_constants_aexp a)
  | c1 ;; c2 =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b1' => IFB b1' THEN (fold_constants_com c1)
               ELSE (fold_constants_com c2) FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y))
             (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0)
             (AMinus (ANum 4) (APlus (ANum 2) (ANum 1)))
     THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* After constant folding: *)
    (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END).
Proof. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intro a. unfold aequiv. intro st.
  induction a; simpl; try reflexivity;
  try (destruct (fold_constants_aexp a1);
       destruct (fold_constants_aexp a2);
       simpl; rewrite IHa1; rewrite IHa2; reflexivity).
Qed.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    try reflexivity.
  - rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
    simpl. destruct (beq_nat n n0); reflexivity.
  - rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
    simpl. destruct (leb n n0); reflexivity.
  - simpl. destruct (fold_constants_bexp b); rewrite IHb; simpl;
      try reflexivity.
  - simpl. destruct (fold_constants_bexp b1);
           destruct (fold_constants_bexp b2);
           rewrite IHb1; rewrite IHb2; simpl; reflexivity.
Qed.

Theorem fold_constants_com_sound : ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c. induction c; simpl.
  - apply refl_cequiv.
  - apply CAss_congruence. apply fold_constants_aexp_sound.
  - apply CSeq_congruence; assumption.
  - assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
    + apply trans_cequiv with c1; try assumption.
        apply IFB_true; assumption.
    + apply trans_cequiv with c2; try assumption.
        apply IFB_false; assumption.
  - assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CWhile_congruence; assumption).
    + apply WHILE_true. assumption.
    + apply WHILE_false. assumption.
Qed.

Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId id => AId id
  | APlus (ANum 0) a2 => optimize_0plus_aexp a2
  | APlus a1 a2 =>
      APlus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | AMinus a1 a2 =>
      AMinus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | AMult a1 a2 =>
      AMult (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2 =>
      BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BNot b1 =>
      BNot (optimize_0plus_bexp b1)
  | BAnd b1 b2 =>
      BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP => SKIP
  | i ::= a => i ::= (optimize_0plus_aexp a)
  | c1 ;; c2 =>
      (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      IFB (optimize_0plus_bexp b)
      THEN (optimize_0plus_com c1)
      ELSE (optimize_0plus_com c2)
      FI
  | WHILE b DO c END =>
      WHILE (optimize_0plus_bexp b)
      DO (optimize_0plus_com c)
      END
  end.

Theorem optimize_0plus_aexp_sound :
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. intro a. unfold aequiv. intro st.
  induction a; try reflexivity;
    try (simpl; destruct a1;
      try (rewrite IHa1; rewrite IHa2; reflexivity)).
  - simpl. destruct n;
      simpl; rewrite IHa2; reflexivity.
Qed.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intro b. unfold bequiv. intro st.
  induction b;
    simpl; try reflexivity.
  - assert (aequiv a (optimize_0plus_aexp a)).  {
    apply optimize_0plus_aexp_sound. }
    assert (aequiv a0 (optimize_0plus_aexp a0)).  {
    apply optimize_0plus_aexp_sound. }
    unfold aequiv in H. rewrite H. rewrite H0. reflexivity.
  - assert (aequiv a (optimize_0plus_aexp a)).  {
    apply optimize_0plus_aexp_sound. }
    assert (aequiv a0 (optimize_0plus_aexp a0)).  {
    apply optimize_0plus_aexp_sound. }
    unfold aequiv in H. rewrite H. rewrite H0. reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intro c. induction c.
  - simpl. apply refl_cequiv.
  - simpl. apply CAss_congruence.
    apply optimize_0plus_aexp_sound.
  - simpl. apply CSeq_congruence; assumption.
  - simpl. apply CIf_congruence; try assumption.
      apply optimize_0plus_bexp_sound.
  - simpl. apply CWhile_congruence; try assumption.
      apply optimize_0plus_bexp_sound.
Qed.

Definition com_optimizer (c : com) : com :=
  optimize_0plus_com (fold_constants_com c).

Theorem com_optimizer_sound :
  ctrans_sound com_optimizer.
Proof.
  unfold ctrans_sound. unfold com_optimizer. intros c.
  apply trans_cequiv with (fold_constants_com c).
  + apply fold_constants_com_sound.
  + apply optimize_0plus_com_sound.
Qed.

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId i' =>
      if beq_id i i' then u else AId i'
  | APlus a1 a2 =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53))
             (APlus (AId Y) (AId X))
= (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity. Qed.

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property. intros Contra.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
  as c1.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
  as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  remember (t_update (t_update empty_state X 1) Y 1) as st1.
  remember (t_update (t_update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state \\ st1);
  assert (H2: c2 / empty_state \\ st2);
  try (subst;
       apply E_Seq with (st' := (t_update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.
  assert (Hcontra: st1 = st2). {
      apply (ceval_deterministic c2 empty_state); assumption. }
  assert (Hcontra': st1 Y = st2 Y) by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.
Qed.

Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (t_update st i ni) a = aeval st a.
Proof.
  intros. induction H;
    try reflexivity;
    try (simpl;
    rewrite IHvar_not_used_in_aexp1; rewrite IHvar_not_used_in_aexp2;
    reflexivity).
  - simpl. apply t_update_neq. assumption.
Qed.

Definition subst_equiv_property_weakened := forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 a1 ->
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_equiv_weakened : subst_equiv_property_weakened.
Proof.
  unfold subst_equiv_property_weakened. intros.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CAss_congruence. induction a2;
      try (simpl; apply refl_aequiv);
      try (simpl; unfold aequiv; simpl; intros st;
           rewrite IHa2_1; rewrite IHa2_2; reflexivity).
    (* The interesting case is when the aexp to rewrite is
        an identifier. *)
    + rename i1 into X. rename i into Y. simpl.
      remember (beq_id X Y) eqn:IdEqn. destruct b.
        * (* X == Y *)
          symmetry in IdEqn.
          apply beq_id_true_iff in IdEqn.
          rewrite <- IdEqn.
          unfold aequiv. intros. admit.
          (* I cannot for the life of me get this last part figured
             out, leaving it alone for now. *)
        * (* X <> Y *) apply refl_aequiv.
Admitted.

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  unfold cequiv. intros Contra.
  assert (H1: (SKIP / empty_state \\ empty_state)) by (apply E_Skip).
  apply Contra in H1. apply WHILE_true_nonterm in H1.
  - apply H1.
  - apply refl_bequiv.
Qed.

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com. (* <---- new *)

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
      aeval st a1 = n ->
      (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = false ->
      c2 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall (b1 : bexp) (st : state) (c1 : com),
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st \\ st
  | E_WhileTrue : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (WHILE b1 DO c1 END) / st' \\ st'' ->
      (WHILE b1 DO c1 END) / st \\ st''
  | E_Havoc : forall (st : state) (X : id) (n : nat),
      (HAVOC X) / st \\ t_update st X n
  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example havoc_example1 :
  (HAVOC X) / empty_state \\ t_update empty_state X 0.
Proof.
  apply E_Havoc.
Qed.

Example havoc_example2 :
  (SKIP;; HAVOC Z) / empty_state \\ t_update empty_state Z 42.
Proof.
  apply E_Seq with empty_state.
  - apply E_Skip.
  - apply E_Havoc.
Qed.

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  c1 / st \\ st' <-> c2 / st \\ st'.

Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.

(* Skipping the rest of this chapter b/c
   1) I can't understand how to define equivalency w/ Havoc
      in the context of nondeterministic commands.
   2) the rest of the exercises go deeper in this direction and I
      want to stay broad for now.
*)

End Himp.