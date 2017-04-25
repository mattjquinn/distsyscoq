Require Export MQuinnTactics.

Check 3 = 3.
Check forall n m : nat, n + m = m + n.

Check forall n : nat, n = 2.
Check 3 = 4.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true : plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop := n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. split. reflexivity. reflexivity. Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split. apply HA. apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro. reflexivity. reflexivity.
Qed.

Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. induction n.
  - split. reflexivity. simpl in H. apply H.
  - split. inversion H. inversion H. Qed.

Lemma and_example2 : forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H. destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm. reflexivity. Qed.

Lemma and_example2' : forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm]. rewrite Hn. rewrite Hm. reflexivity. Qed.

Lemma and_example2'' : forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm. rewrite Hn. rewrite Hm. reflexivity. Qed.

Lemma and_example3 : forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity. Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof. intros P Q [HP HQ]. apply HP. Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof. intros P Q [HP HQ]. apply HQ. Qed.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ]. split.
  - apply HQ.
  - apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split. apply HP. apply HQ.
  - apply HR. Qed.

Check and.

Lemma or_example : forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O.
    reflexivity. Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left. apply HA. Qed.

Lemma zero_or_succ : forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity. Qed.

Lemma mult_eq_0 : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n] m H.
  - left. reflexivity.
  - right. destruct m. reflexivity. inversion H. Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ. Qed.

Module MyNot.

Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.

End MyNot.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra. Qed.

Fact not_implies_our_not : forall (P : Prop),
  ~P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P H1 Q H2.
  destruct H1. apply H2. Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra. Qed.

Check (0 <> 1).

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H. Qed.

Theorem not_False : ~False.
Proof.
  unfold not. intros H. inversion H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [H1 H2]. destruct H2. apply H1. Qed.

Theorem contradiction_implies_anything' : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H1. unfold not. intros H2. apply H2. apply H1. Qed.

(* Theorem: P implies ~~P, for any proposition P.
   Proof: Let P be a proposition. P could be either True or False.

   If P is True, we have True -> ~~True
                         True -> ~False
                         True -> True
   which follows trivially from application of the predicate.

   If P is False, we have False -> ~~False. By ex falso quodlibet,
   assuming False allows us to assert anything, including ~~False.
*)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2. unfold not. intros H3. destruct H2. apply H1 in H3.
  apply H3. Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  intros P [H1 H2]. destruct H2. apply H1. Qed.

(* Theorem: ~(P /\ ~P) for any proposition P.
   Proof: Let P be a proposition. P could be either True or False.

   If P is True, we have ~(True /\ ~True)
                         ~(True /\ False)
                         ~False
   which is True.

   If P is False, we have ~(False /\ ~False)
                          ~(False /\ True)
                          ~False
   which is True.
*)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet. apply H. reflexivity.
  - (* b = false *)
    reflexivity. Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H. exfalso. apply H. reflexivity.
  - reflexivity. Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity) : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HA HB].
  unfold iff. split.
  apply HB. apply HA. Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'. inversion H'. Qed.

Theorem iff_rel : forall P : Prop, P <-> P.
Proof.
  intros P. split.
  - intros H. apply H.
  - intros H. apply H. Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R. split.
  - destruct H. destruct H0. intros H3. apply H0. apply H. apply H3.
  - destruct H. destruct H0. intros H3. apply H1. apply H2. apply H3. Qed.

(* Got this one by myself, proving the reverse implication
   (second case) stumped me for awhile but after applying
   the nested intros destructor it all made sense. *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HL | HR].
    + { split.
      - left. apply HL.
      - left. apply HL. }
    + { destruct HR. split.
      - right. apply H.
      - right. apply H0. }
  - intros [[HP1 | HQ][HP2 | HR]].
    + (* P (and P) are true *) left. apply HP1.
    + (* P and R are true *) left. apply HP1.
    + (* P and Q are true *) left. apply HP2.
    + (* Q and R are true *) right. { split.
      - apply HQ.
      - apply HR. } Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example. Qed.

Lemma or_assoc : forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H. Qed.

Lemma mult_03 : forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p. rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity. Qed.

Lemma apply_iff_example : forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H. Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. exists (2 + m). apply Hm. Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H1. unfold not. intros [x H2]. apply H2. apply H1. Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ. Qed.

