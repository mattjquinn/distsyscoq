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

