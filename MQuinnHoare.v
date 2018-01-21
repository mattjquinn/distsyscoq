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