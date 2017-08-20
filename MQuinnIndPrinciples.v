Require Export MQuinnProofObjects.

Check nat_ind.

Theorem mult_0_r' : forall n : nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. rewrite -> IHn'. reflexivity. Qed.

Lemma n_eq_m__S_n_eq_S_m : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros n. apply nat_ind.
  - intros. rewrite H. reflexivity.
  - intros. rewrite H0. reflexivity.
  - apply n.
Qed.

Theorem plus_one_r' : forall n : nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. apply n_eq_m__S_n_eq_S_m.
    apply IHn'.
Qed.