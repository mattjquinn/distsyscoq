Require Import List Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Print unit.
Print True.

Section Propositional.
  Variables P Q R : Prop.

  Theorem obvious : True.
    apply I.
  Qed.

  Theorem obvious' : True.
    constructor.
  Qed.

  Print False.

  Theorem False_imp : False -> 2 + 2 = 5.
    destruct 1.
  Qed.

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
    intro.
    elimtype False.
    crush.
  Qed.

  Print not.

  Theorem arith_neq' : ~ (2 + 2 = 5).
    unfold not.
    crush.
  Qed.

  Print and.
  Print prod.

  Theorem and_comm : P /\ Q -> Q /\ P.
    destruct 1.
    split; assumption.
  Qed.

  Print or.
  Print sum.

  Theorem or_comm : P \/ Q -> Q \/ P.
    destruct 1.
    right; assumption.
    left; assumption.
  Qed.

  Theorem or_comm' : P \/ Q -> Q \/ P.
    tauto.
  Qed.

  Theorem arith_comm : forall ls1 ls2 : list nat,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6
      -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    intuition.
    rewrite app_length.
    tauto.
  Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6
      -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length.
    crush.
  Qed.
End Propositional.

Print ex.

Theorem exist1 : exists x : nat, x + 1 = 2.
  exists 1.
  reflexivity.
Qed.

Theorem exist2 : forall n m : nat, (exists x : nat, n + x = m) -> n <= m.
  destruct 1.
  crush.
Qed.

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
  constructor.
Qed.

Print eq.

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
  destruct 1.
  crush.
Qed.

Theorem isZero_contra : isZero 1 -> False.
  destruct 1.
  Undo.
  inversion 1.
Qed.

Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
  destruct 1.
Abort.

Check isZero_ind.

Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).

Theorem even_0 : even 0.
  constructor.
Qed.

Theorem even_4 : even 4.
  repeat constructor.
Qed.

Hint Constructors even.

Theorem even_4' : even 4.
  auto.
Qed.

Theorem even_plus : forall n m, even n -> even m -> even (n + m).
  induction n; crush.
  inversion H. simpl.
  constructor.
  Restart.
  induction 1. crush.
  intros. simpl. constructor. crush.
  Restart.
  induction 1; crush.
Qed.

Theorem even_contra : forall n, even (S (n + n)) -> False.
  induction 1.
Abort.

Lemma even_contra' : forall n', even n' -> forall n, n' = S (n + n) -> False.
  induction 1; crush.
  destruct n; destruct n0; crush.
  SearchRewrite (_ + S _).
  rewrite <- plus_n_Sm in H0.
  apply IHeven with n0. assumption.
  Restart.
  Hint Rewrite <- plus_n_Sm.
  induction 1; crush;
    match goal with
    | [H : S ?N = ?N0 + ?N0 |- _ ] => destruct N; destruct N0
    end;
    crush.
Qed.

Theorem even_contra : forall n, even (S (n + n)) -> False.
  intros; eapply even_contra'; eauto.
Qed.