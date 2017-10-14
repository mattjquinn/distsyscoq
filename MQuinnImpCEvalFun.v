Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith.
Require Import MQuinnImp.
Require Import MQuinnMaps.

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        t_update st l (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
        st (* bogus *)
  end.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_state
  | S i' =>
    match c with
    | SKIP => st
    | l ::= a1 => t_update st l (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step2 st c1 i'
          else ceval_step2 st c2 i'
    | WHILE b1 DO c1 END =>
        if (beval st b1)
        then let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c i'
        else st
    end
  end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
    | SKIP => Some st
    | l ::= a1 => Some (t_update st l (aeval st a1))
    | c1 ;; c2 =>
        match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step3 st c1 i'
          else ceval_step3 st c2 i'
    | WHILE b1 DO c1 END =>
        if (beval st b1)
        then match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c i'
          | None => None
          end
        else Some st
  end
end.

Notation "'LETOPT' x <== e1 'IN' e2"
  := (match e1 with
      | Some x => e2
      | None => None
    end)
  (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP => Some st
      | l ::= a1 => Some (t_update st l (aeval st a1))
      | c1 ;; c2 => LETOPT st' <== ceval_step st c1 i' IN
                    ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
  end
end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
    | None => None
    | Some st => Some (st X, st Y, st Z)
  end.

Compute
     (test_ceval empty_state
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3
            ELSE Z ::= ANum 4
          FI)).

Definition pup_to_n : com :=
  WHILE (BNot (BEq (ANum 0) (AId X))) DO
    Y ::= (APlus (AId Y) (AId X)) ;;
    X ::= (AMinus (AId X) (ANum 1))
  END.

Compute (test_ceval (t_update empty_state X 5) pup_to_n).

Example pup_to_n_1 :
  test_ceval (t_update empty_state X 5) pup_to_n = Some (0, 15, 0).
Proof. reflexivity. Qed.

Definition peven : com :=
  WHILE (BAnd (BNot (BEq (ANum 0) (AId X)))
              (BNot (BEq (ANum 1) (AId X)))) DO
    X ::= (AMinus (AId X) (ANum 2))
  END ;;
  IFB (BEq (AId X) (ANum 1)) THEN
    Z ::= ANum 1
  ELSE
    Z ::= ANum 0
  FI.

Compute (test_ceval (t_update empty_state X 6) peven).
Compute (test_ceval (t_update empty_state X 7) peven).
Compute (test_ceval (t_update empty_state X 8) peven).
Compute (test_ceval (t_update empty_state X 9) peven).

Theorem ceval_step__ceval : forall c st st',
  (exists i, ceval_step st c i = Some st') ->
  c / st \\ st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].
  - intros c st st' H. inversion H.
  - intros c st st' H.
    destruct c; simpl in H; inversion H; subst; clear H.
    + apply E_Skip.
    + apply E_Ass. reflexivity.
    + destruct (ceval_step st c1 i') eqn:Heqr1.
      * (* Evaluation of c1 terminates normally. *)
        apply E_Seq with s.
          apply IHi'. apply Heqr1.
          apply IHi'. assumption.
      * (* Otherwise, contradiction. *)
        inversion H1.
    + destruct (beval st b) eqn:HEqr.
      * (* r = true *)
        apply E_IfTrue. rewrite HEqr. reflexivity.
        apply IHi'. apply H1.
      * (* r = false *)
        apply E_IfFalse. rewrite HEqr. reflexivity.
        apply IHi'. apply H1.
    + destruct (beval st b) eqn:HEqr.
      * (* r = true *)
        destruct (ceval_step st c i') eqn:Heqr1.
        { (* r1 = Some s *)
          apply E_WhileLoop with s. rewrite HEqr. reflexivity.
          apply IHi'. apply Heqr1.
          apply IHi'. apply H1. }
        { (* r1 = None *) inversion H1. }
      * (* r = false *)
        inversion H1.
        apply E_WhileEnd. rewrite <- HEqr. subst.
        reflexivity. Qed.

(* Exercise: ceval_step__ceval_inf
   Theorem: For all c st st',
   if there exists an i st. ceval_step st c i = Some st',
   then c / st \\ st'.

   Proof: by induction on i.
     - Base case: i = 0.
       Then our assumption states that ceval_step st c 0 = Some st'.
       But if i is 0, ceval_step yields None, not Some st', so
       we dispose of this contradictory case.
     - Inductive case: i = (S i').
       Then our assumption states that ceval_step st c' = Some st',
       and our inductive assumption states that
       for all c, st, st', ceval_step st c i' = Some st' -> c / st \\ st'.

       We proceed by case analysis on c:
       - Case SKIP : trivial, by definition.
       - Case (i ::= a) : trivial, by definition.
       - Case (c1 ;; c2) : If c1 terminates normally, the inductive
         hypothesis tells us that applying ceval_step to this same
         c1 yields the same final state s. Then for c2, applying
         the inductive hypothesis tells us that applying ceval_step
         to c2 takes us from s to st', which matches our assumption.
         We dispense with the possibility that c1 *doesn't* terminate
         normally, as this contradicts our assumption that c2
         terminates normally.
       - Case IF statement: We case analyze the boolean expression
         of the conditional to reach both statement bodies; for both,
         proof proceeds by applying the inductive hypothesis to get
         restatements of the goal in terms of ceval_step, which follow
         immediately by assumption.
       - Case WHILE statement: We case analyze the boolean expresion
         of the conditional. If the expression is true, the loop either
         takes a step (and modifies the state) or doesn't. The former
         proceeds as usual by application of our inductive hypothesis,
         followed by assumption. The latter is a contradiction; we assume
         the WHILE statement as a whole modifies the state, which is
         not possible if the loop doesn't take a step, so we dispense
         with it.
         If the boolean expression is false, then the WHILE statement as
         a whole returns unmodified the state in which the expression is
         false, which follows from our definition of the evaluation
         of WHILE.
*)

Theorem ceval_step_more : forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
  induction i1 as [| i1']; intros i2 st st' c Hle Hceval.
  - inversion Hceval.
  - destruct i2 as [| i2']. inversion Hle.
    assert (Hle' : i1' <= i2') by omega.
    destruct c.
    + (* SKIP *)
      simpl in Hceval. inversion Hceval. reflexivity.
    + (* ::= *)
      simpl in Hceval. inversion Hceval. simpl. reflexivity.
    + (* ;; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. apply IHi1'; assumption.
      * inversion Hceval.
    + (* IFB *)
      simpl in Hceval. simpl. destruct (beval st b);
      apply (IHi1' i2') in Hceval; assumption.
    + (* WHILE *)
      simpl in Hceval. simpl. destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. apply IHi1'; assumption.
      * inversion Hceval.
Qed.

Theorem ceval__ceval_step : forall c st st',
  c / st \\ st' ->
  exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce. induction Hce.
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. rewrite H. reflexivity.
  - destruct IHHce1 as [i1 IHHce1].
    destruct IHHce2 as [i2 IHHce2].
    admit.
  - destruct IHHce as [i IHHce].
    rewrite <- IHHce. exists i.
    destruct i.
    + reflexivity.
    + simpl. destruct (beval st b).
      * destruct c1.
Abort. (* Getting impatient, so aborting for now to move on to
          extraction and automation chapters. *)