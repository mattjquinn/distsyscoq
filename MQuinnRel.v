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