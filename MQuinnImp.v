Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import MQuinnMaps.

Module AExp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1 : aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => leb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus : optimize_0plus
  (APlus (ANum 2) (APlus (ANum 0) (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound : forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - reflexivity.
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. apply HP.
Qed.

Lemma foo : forall n, leb 0 n = true.
Proof.
  intros. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma foo' : forall n, leb 0 n = true.
Proof.
  intros. destruct n; simpl; reflexivity.
Qed.

Theorem optimize_0plus_sound' : forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - reflexivity.
  - destruct a1;
      try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n; simpl; rewrite IHa2; reflexivity.
Qed.

Theorem optimize_0plus_sound'' : forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  - (* The interesting case is when a = APlus a1 a2. *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros. induction b;
    repeat reflexivity;
    repeat (simpl; rewrite (optimize_0plus_sound a);
      rewrite (optimize_0plus_sound a0); reflexivity).
  - simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Fixpoint aexp_optimizer (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus e1 e2 => APlus (aexp_optimizer e1) (aexp_optimizer e2)
  | AMinus e1 (ANum 0) => aexp_optimizer e1 (* OPTIMIZATION #2 *)
  | AMinus e1 e2 => AMinus (aexp_optimizer e1) (aexp_optimizer e2)
  | AMult (ANum 0) e2 => ANum 0 (* OPTIMIZATION #1 *)
  | AMult e1 (ANum 0) => ANum 0 (* OPTIMIZATION #3 *)
  | AMult e1 e2 => AMult (aexp_optimizer e1) (aexp_optimizer e2)
  end.

Theorem aexp_optimizer_sound : forall a,
  aeval (aexp_optimizer a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  - (* aeval (aexp_optimizer (AMinus a1 a2)) = aeval (AMinus a1 a2) *)
    simpl. destruct a2;
      try (simpl; simpl in IHa2; rewrite IHa2; rewrite IHa1; reflexivity).
    + simpl. destruct n.
      * rewrite IHa1. apply minus_n_O. (* OPTIMIZATION #2 *)
      * simpl. rewrite IHa1. reflexivity.
  - (* -> aeval (aexp_optimizer (AMult a1 a2)) = aeval (AMult a1 a2) *)
    (* NOTE: Large portions of this subproof are repetitive, but at this
       time I do not know how to repeat large blocks of tacticals. *)
    simpl. destruct a1.
    + simpl. destruct n.
      * reflexivity.
      * simpl. { destruct a2;
        try (simpl; simpl in IHa2; rewrite IHa2; reflexivity).
        - simpl. destruct n0.
          + apply mult_n_O.
          + reflexivity. }
     + simpl. { destruct a2;
        try (simpl; simpl in IHa2; rewrite IHa2;
                    simpl in IHa1; rewrite IHa1; reflexivity).
        - simpl. destruct n.
          + apply mult_n_O.
          + simpl. simpl in IHa1. rewrite IHa1. reflexivity. }
     + simpl. destruct a2;
       try (simpl; simpl in IHa1; rewrite IHa1; simpl in IHa2;
              rewrite IHa2; reflexivity).
       * simpl. { destruct n.
         - apply mult_n_O.
         - simpl. destruct a1_2;
             try (simpl; simpl in IHa1; rewrite IHa1; reflexivity). }
     + simpl. destruct a2;
       try (simpl; simpl in IHa1; rewrite IHa1; simpl in IHa2;
              rewrite IHa2; reflexivity).
       * simpl. { destruct n.
         - apply mult_n_O.
         - simpl. destruct a1_2;
             try (simpl; simpl in IHa1; rewrite IHa1; reflexivity). }
Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl; try c.

Require Import Coq.omega.Omega.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 -> m <= p.
Proof.
  intros. omega.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat), aevalR (ANum n) n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMult e1 e2) (n1 * n2).

Notation "e '\\' n"
  := (aevalR e n) (at level 50, left associativity) : type_scope.

End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat), (ANum n) \\ n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
    (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
    (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
    (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
where "e '\\' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall a n, (a \\ n) <-> aeval a = n.
Proof.
  intros. split.
  - intros H. induction H;
      simpl; subst; reflexivity.
  - intros H.
    generalize dependent n. (* Forgot to do this, got stuck as a result. *)
    induction a.
    + intros n' H. subst n'. constructor.
    + intros n' H. simpl in H. subst n'. apply E_APlus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + intros n' H. simpl in H. subst n'. apply E_AMinus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + intros n' H. simpl in H. subst n'. apply E_AMult.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n, (a \\ n) <-> aeval a = n.
Proof.
  split.
  - intros H; induction H; subst; reflexivity.
  - generalize dependent n.
    induction a; simpl; intros; subst; constructor;
      try apply IHa1; try apply IHa2; reflexivity.
Qed.

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq : forall (a1 a2 : aexp),
      bevalR (BEq a1 a2) ((aeval a1) =? (aeval a2))
  | E_BLe : forall (a1 a2 : aexp),
      bevalR (BLe a1 a2) ((aeval a1) <=? (aeval a2))
  | E_BNot : forall b : bexp,
      bevalR (BNot b) (negb (beval b))
  | E_BAnd : forall (b1 b2 : bexp),
      bevalR (BAnd b1 b2) ((beval b1) && (beval b2)).

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  intros. split.
  - intros H. induction H; reflexivity.
  - intros H. induction b;
      subst; simpl; constructor.
Qed.

End AExp.

Module aevalR_division.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat), (ANum n) \\ n
  | E_APlus : forall (a1 a2 : aexp) (n1 n2 : nat),
    (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2 : aexp) (n1 n2 : nat),
    (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult : forall (a1 a2 : aexp) (n1 n2 : nat),
    (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv : forall (a1 a2 : aexp) (n1 n2 n3 : nat),
    (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
    (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3
where "e '\\' n" := (aevalR e n) : type_scope.

End aevalR_division.

Module aevalR_extended.

Inductive aexp : Type :=
  | AAny : aexp
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_AAny : forall (n : nat), AAny \\ n
  | E_ANum : forall (n : nat), (ANum n) \\ n
  | E_APlus : forall (a1 a2 : aexp) (n1 n2 : nat),
    (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2 : aexp) (n1 n2 : nat),
    (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult : forall (a1 a2 : aexp) (n1 n2 : nat),
    (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
where "e '\\' n" := (aevalR e n) : type_scope.

End aevalR_extended.

Definition state := total_map nat.
Definition empty_state : state := t_empty 0.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1 : aeval (t_update empty_state X 5)
                      (APlus (ANum 3) (AMult (AId X) (ANum 2))) = 13.
Proof. reflexivity. Qed.

Example bexp1 : beval (t_update empty_state X 5)
                      (BAnd BTrue (BNot (BLe (AId X) (ANum 4)))) = true.
Proof. reflexivity. Qed.