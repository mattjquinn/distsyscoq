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