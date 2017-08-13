Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive id : Type :=
  | Id : string -> id.

Definition beq_id x y :=
  match x, y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Check string_dec.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros id. destruct id. simpl. destruct (string_dec s s).
  - reflexivity.
  - unfold not in n. exfalso. apply n. reflexivity.
Qed.

Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Proof.
  intros [s1] [s2].
  unfold beq_id.
  destruct (string_dec s1 s2).
  - subst. split. reflexivity. reflexivity.
  - split.
    + intros contra. inversion contra.
    + intros H. inversion H. subst. destruct n. reflexivity.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

