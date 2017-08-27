Require Export MQuinnIndProp.

Definition relation (X : Type) := X -> X -> Prop.

Print le.
Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
Check next_nat : relation nat.

Theorem next_nat_partial_function : partial_function next_nat.
Proof.
  unfold partial_function. intros.
  inversion H. inversion H0. reflexivity.
Qed.

Theorem le_not_a_partial_function : ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  inversion Nonsense. Qed.

Theorem total_relation_not_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (1 = 2) as Nonsense. {
    apply Hc with (x := 0).
    - apply tr_1.
    - apply tr_1. }
  inversion Nonsense. Qed.

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function. unfold empty_relation. intros.
  unfold not in H. exfalso. apply H. apply tr_1. Qed.
(* I don't completely (intuitively) understand this proof,
   but moving on. *)

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Theorem le_reflexive : reflexive le.
Proof.
  unfold reflexive. intros. apply le_n. Qed.

Definition transitive {X : Type} (R : relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans : transitive le.
Proof.
  unfold transitive. intros. induction H0.
  - apply H.
  - apply le_S. apply IHle. Qed.

Theorem lt_trans : transitive lt.
Proof.
  unfold transitive. intros. induction H0.
  - apply lt_S. apply H.
  - apply lt_S. apply IHle. Qed.

Theorem lt_trans'' : transitive lt.
Proof.
  unfold lt. unfold transitive. intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - apply le_S. apply IHo'. Abort.
(* Can't figure this out right now and am out of patience. *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros. induction H.
  - apply le_S. apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem le_S_n : forall n m, (S n <= S m) -> (n <= m).
Proof.
  intros. induction m.
  - inversion H. apply le_n. inversion H1.
  - apply le_S_n. apply H.
Qed.

(*
  Theorem : forall n : nat, ~ (S n <= n)
  Proof. By induction on n.
  - Suppose n = 0. We must show ~ (S 0) <= 0, or ~ 1 <= 0.
    This follows trivially.
  - Suppose n = S n'. Suppose further that ~ (S n' <= n') holds.
    We must show ~ (S (S n') <= (S n')). This simplifies to
    ~ (S n' <= n'), and is true by application of the induction hypothesis.
  Qed.
*)

Theorem le_Sn_n : forall n, ~ (S n <= n).
Proof.
  intros. induction n as [| n' IHn'].
  - unfold not. intros H. inversion H.
  - unfold not. intros H. apply le_S_n in H.
    generalize dependent H. apply IHn'.
Qed.

Definition symmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric : ~ (symmetric le).
Proof.
  unfold not. unfold symmetric. intros Hc.
  assert (1 <= 0) as Nonsense. {
    apply Hc. apply le_S. apply le_n. }
  inversion Nonsense.
Qed.

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Lemma n_eq_m__S_n_eq_S_m : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros n. apply nat_ind.
  - intros. rewrite H. reflexivity.
  - intros. rewrite H0. reflexivity.
  - apply n.
Qed.

Theorem le_antisymmetric : antisymmetric le.
Proof.
  unfold antisymmetric. intros. generalize dependent b. induction a.
  - intros. inversion H0. reflexivity.
  - destruct b.
    + intros. inversion H.
    + intros. apply n_eq_m__S_n_eq_S_m. apply IHa.
      * apply le_S_n in H. apply H.
      * apply le_S_n in H0. apply H0.
Qed.

Theorem le_step : forall n m p, n < m -> m <= S p -> n <= p.
Proof.
  intros. apply Lt.lt_le_S in H. apply Le.le_S_n.
  generalize dependent H0. generalize dependent H.
  apply (le_trans (S n) m (S p)). Qed.

Definition equivalence {X : Type} (R : relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X : Type} (R : relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X : Type} (R : relation X) :=
  (reflexive R) /\ (transitive R).

