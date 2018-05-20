Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import MQuinnImp.
Require Import MQuinnMaps.

Definition Assertion := state -> Prop.

Module ExAssertions.

Definition as1 : Assertion := fun st => st X = 3.
(* Holds for every state in which X is 3. *)

Definition as2 : Assertion := fun st => st X <= st Y.
(* Holds for every state in which X is <= Y. *)

Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
(* Holds for every state in which X is 3 or X is <= Y. *)

Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
(* Holds for every state in which Z*Z is <= X
     AND (Z+1*Z+1) is NOT <= X. *)

Definition as5 : Assertion := fun st => True.
(* Holds for every state. *)

Definition as6 : Assertion := fun st => False.
(* Does not hold for any state. *)

End ExAssertions.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
     c / st \\ st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(*
1) {{True}} c {{X = 5}}
   If c is run in any state, it results in a state in which X is 5.

2) {{X = m}} c {{X = m + 5)}}
   If c is run in a state where X is m, it results in a state where
   X is m + 5.

3) {{X ≤ Y}} c {{Y ≤ X}}
   If c is run in a state where X is <= Y, it results in state where
   Y <= X.

4) {{True}} c {{False}}
   If c is run in any state, it does not result in any state.

5) {{X = m}}
   c
   {{Y = real_fact m}}
   If c is run in any state where X = m, it results in a state where
   Y is (real_fact m).

6) {{True}}
   c
   {{(Z * Z) ≤ m ∧ ¬ (((S Z) * (S Z)) ≤ m)}}
   If c is run in any state, it results in a state where
   (Z * Z) ≤ m ∧ ¬ (((S Z) * (S Z)) ≤ m).
*)

(*
1) {{True}} X ::= 5 {{X = 5}}
   VALID

2) {{X = 2}} X ::= X + 1 {{X = 3}}
   VALID

3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}
   VALID

4) {{X = 2 ∧ X = 3}} X ::= 5 {{X = 0}}
   INVALID

5) {{True}} SKIP {{False}}
   INVALID

6) {{False}} SKIP {{True}}
   INVALID

7) {{True}} WHILE True DO SKIP END {{False}}
   VALID

8) {{X = 0}}
    WHILE X == 0 DO X ::= X + 1 END
    {{X = 1}}
    VALID

9) {{X = 1}}
    WHILE X ≠ 0 DO X ::= X + 1 END
    {{X = 100}} 
    INVALID
*)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple. intros. apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP. Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (t_update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst. unfold assn_sub in HQ. assumption.
Qed.

Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_ex1 :
  {{(fun st => st X <= 5) [X |-> APlus (AId X) (ANum 1)]}}
  (X ::= (APlus (AId X) (ANum 1)))
  {{(fun st => st X <= 5)}}.
Proof. apply hoare_asgn. Qed.

Example assn_sub_ex2 :
  {{(fun st => (0 <= st X /\ st X <= 5)) [X |-> ANum 3] }}
  (X ::= (ANum 3))
  {{(fun st => 0 <= st X /\ st X <= 5)}}.
Proof. apply hoare_asgn. Qed.

(*
   hoare_asgn_wrong

   {{ True }} X ::= a {{ X = a }}

   Proof: by contradiction.
   Assume a is X + 1 for any value of X.
    - Our precondition is True and hence satisfied.
    - Our postcondition is X = X + 1. When the assignment is made,
      X ::= a brings state st to a st' where X' equals X + 1. The
      postcondition applies to this state st', and thus can be transformed
      to X' + 1. X' + 1 <> X + 1, and so this type of forward rule will
      not work correctly in all instances.
*)

Theorem hoare_asgn_fwd :
  forall m a P,
  {{ fun st => P st /\ st X = m }}
    X ::= a
  {{ fun st => P (t_update st X m)
              /\ st X = aeval (t_update st X m) a }}.
Proof.
  intros. unfold hoare_triple. intros st st' Hcom [H1 H2]. split;
    inversion Hcom; subst.
  - rewrite t_update_shadow. rewrite t_update_same. apply H1.
  - rewrite t_update_shadow. rewrite t_update_eq. rewrite t_update_same.
    reflexivity.
Qed.

Theorem hoare_asgn_fwd_exists :
  forall a P,
  {{ fun st => P st }}
    X ::= a
  {{ fun st => exists m, P (t_update st X m) /\
                st X = aeval (t_update st X m) a }}.
Proof.
  intros. unfold hoare_triple. intros st st' Hcom H1.
  remember (st X) as m'. exists m'.
  (* Note that everything after and including this split is identical to
     to the steps in hoare_asgn_fwd above; ideally should apply that
     theorem directly or extract those steps as a lemma here. *)
  split;
      inversion Hcom; subst.
  - rewrite t_update_shadow. rewrite t_update_same. apply H1.
  - rewrite t_update_shadow. rewrite t_update_eq. rewrite t_update_same.
    reflexivity.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold assert_implies. unfold hoare_triple. intros.
  apply H0 in H2. generalize dependent H2. apply H.
  assumption.
Qed.

Theorem hoare_consequence_pre_from_book : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp st st' Hc HP.
  apply Himp. apply (Hhoare st st'); assumption.
Qed.

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> ANum 1]).
  apply hoare_asgn. intros st H.
  unfold assn_sub. unfold t_update. reflexivity.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hhoare HPimp HQimp.
  apply (hoare_consequence_pre P P' Q).
  apply (hoare_consequence_post P' Q Q').
  apply Hhoare. apply HQimp. apply HPimp.
Qed.

Example hoare_asgn_example1' :
  {{ fun st => True }}
  (X ::= (ANum 1))
  {{ fun st => st X = 1 }}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn. intros st H. reflexivity.
Qed.

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP.
Abort.

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

Lemma silly2_eassumption :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ.
  eassumption.
Qed.

Theorem assn_sub_ex1' : 
  {{ fun st => st X + 1 <= 5 }} 
  (X ::= (APlus (AId X) (ANum 1)))
  {{ fun st => st X <= 5 }}.
Proof.
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros st H. eassumption.
Qed.

Theorem assn_sub_ex2' :
  {{ fun st => 0 <= 3 /\ 3 <= 5 }}
  (X ::= (ANum 3))
  {{ fun st => 0 <= st X /\ st X <= 5 }}.
Proof.
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros st H. eassumption.
Qed.

Theorem hoare_skip : forall P, {{P}} SKIP {{P}}.
Proof. unfold hoare_triple. intros. inversion H. subst. assumption. Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;;c2 {{R}}.
Proof.
  unfold hoare_triple. intros.
  inversion H1. subst.
  eapply H. eassumption.
  eapply H0. apply H5. assumption.
Qed.

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  (X ::= a;; SKIP)
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - apply hoare_skip.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

Example hoare_asgn_example_4 : 
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2))
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  eapply hoare_seq.
  - apply hoare_asgn.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + intros st H. unfold assn_sub. split; reflexivity.
Qed.

Definition swap_program : com :=
  Z ::= AId X ;;
  X ::= AId Y ;;
  Y ::= AId Z.

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  eapply hoare_seq.
  - eapply hoare_seq; apply hoare_asgn.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + intros st H. unfold assn_sub. simpl.
      unfold t_update. simpl. assumption.
Qed.

(* Exercise hoarestate1:
   Explain why the following proposition can't be proven:

      forall (a : aexp) (n : nat),
         {{fun st ⇒ aeval st a = n}}
         (X ::= (ANum 3);; Y ::= a)
         {{fun st ⇒ st Y = n}}.

   Answer: Because a could be an aexp involving X; assigning
   3 to X may cause a to still equal n, or it may not. Without
   knowing more about a, we can't prove one direction or the other.
*)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros. unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe Hcontra.
  unfold bassn in Hcontra.
  rewrite -> Hcontra in Hbe. inversion Hbe.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 Hif Helse st st' Hcom HP.
  inversion Hcom; subst.
  - apply (Hif st st'); try split; assumption.
  - apply (Helse st st').
    + assumption.
    + split. assumption.
      apply bexp_eval_false. assumption.
Qed.

Theorem if_minus_plus :
  {{ fun st => True }}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  apply hoare_if.
  - intros st st' H1 [_ H2]. inversion H1. subst. simpl.
    unfold t_update. simpl. rewrite Nat.add_sub_assoc.
    + omega.
    + inversion H2. apply leb_complete in H0. assumption.
  - intros st st' H1 [_ H2]. inversion H1. subst. simpl.
    unfold t_update. simpl. reflexivity.
Qed.

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.
Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity).

 Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st \\ st
  | E_WhileTrue : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st \\ st' ->
                  (WHILE b1 DO c1 END) / st' \\ st'' ->
                  (WHILE b1 DO c1 END) / st \\ st''
  | E_If1True : forall (st st' : state) (b : bexp) (c : com),
                beval st b = true ->
                c / st \\ st' ->
                (IF1 b THEN c FI) / st \\ st'
  | E_If1False : forall (st : state) (b : bexp) (c : com),
                 beval st b = false ->
                 (IF1 b THEN c FI) / st \\ st
  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st \\ st' ->
       P st ->
       Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

Theorem hoare_if1 : forall P Q b c,
  {{fun st => P st /\ bassn b st}} c {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} SKIP {{Q}} ->
  {{P}} (IF1 b THEN c FI) {{Q}}.
Proof.
  intros P Q b c Hif Helse st st' Hcom HP. inversion Hcom; subst.
  - apply (Hif st st').
    + assumption.
    + apply bexp_eval_true in H1. split; assumption.
  - apply (Helse st').
    + apply E_Skip.
    + apply bexp_eval_false in H3. split; assumption.
Qed.

Lemma not_bassn_bnot__bassn : forall b st,
  ~ bassn (BNot b) st -> bassn b st.
Proof.
  unfold not. unfold bassn. simpl. intros b st H.
  destruct (beval st b); simpl in H.
  - reflexivity.
  - exfalso. apply H. reflexivity.
    (* OR: contradict H. reflexivity. *)
Qed.

Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  IF1 BNot (BEq (AId Y) (ANum 0)) THEN
    X ::= APlus (AId X) (AId Y)
  FI
  {{ fun st => st X = st Z }}.
Proof.
  apply hoare_if1.
  - intros st st' H1 [H2 H3]. inversion H1. subst.
    simpl. rewrite t_update_eq. rewrite t_update_neq.
    + assumption.
    + apply beq_id_false_iff. reflexivity.
  - intros st st' H1 [H2 H3]. inversion H1. subst.
    rewrite <- H2. apply not_bassn_bnot__bassn in H3.
    inversion H3. apply beq_nat_true in H0. rewrite H0.
    rewrite <- plus_n_O. reflexivity.
Qed.

End If1.

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He; try inversion Heqwcom; subst; clear Heqwcom.
  - split. assumption. apply bexp_eval_false. assumption.
  - apply IHHe2; try reflexivity.
    apply (Hhoare st st'). assumption. split. assumption.
    apply bexp_eval_true. assumption.
Qed.

Example while_example :
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  - unfold bassn. unfold assn_sub. unfold assert_implies.
    unfold t_update. simpl. intros st [H1 H2]. apply leb_complete in H2.
    omega.
  - simpl. unfold bassn. unfold assert_implies. intros st [HLe Hb].
    simpl in Hb. destruct (leb (st X) 2) eqn : Heqle.
    + exfalso. apply Hb. reflexivity.
    + apply leb_iff_conv in Heqle. omega.
Qed.

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  intros.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    apply hoare_post_true. intros st. apply I.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl. intros st [Hinv Hguard]. contradict Hguard. reflexivity.
  - (* Precondition implies invariant *)
    intros st H. constructor.
Qed.

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (t_update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ;; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileFalse : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileTrue : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatInitial : forall st st' st'' b c,
      ceval st c st' ->
      ceval st' (REPEAT c UNTIL b END) st'' ->
      ceval st (REPEAT c UNTIL b END) st''
  | E_RepeatContinue : forall st st' st'' b c,
      beval st b = false ->
      ceval st c st' ->
      ceval st' (REPEAT c UNTIL b END) st'' ->
      ceval st (REPEAT c UNTIL b END) st
  | E_RepeatEnd : forall st b c,
      beval st b = true ->
      ceval st (REPEAT c UNTIL b END) st.

Notation "c1 '/' st '\\' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion)
                        : Prop :=
  forall st st', (c / st \\ st') -> P st -> Q st'.
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).


Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;;
    Y ::= APlus (AId Y) (ANum 1)
  UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state \\
               t_update (t_update empty_state X 1) Y 1.
Proof.
  unfold ex1_repeat. apply E_RepeatInitial
    with (st' := (t_update (t_update empty_state X 1) Y 1)).
  - apply E_Seq with (t_update empty_state X 1); apply E_Ass; reflexivity.
  - apply E_RepeatEnd. reflexivity.
Qed.