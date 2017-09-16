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

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" := CSkip.
Notation "x '::=' a" := (CAss x a) (at level 60).
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
  | SKIP => st
  | x ::= a1 => t_update st x (aeval st a1)
  | c1 ;; c2 =>
      let st' := ceval_fun_no_while st c1 in ceval_fun_no_while st' c2
  | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b)
        then ceval_fun_no_while st c1
        else ceval_fun_no_while st c2
  | WHILE b DO c END => st (* bogus *)
      (* if (beval st b)
        then ceval_fun_no_while st (c;; WHILE b DO c END)
        else st *)
  end.

Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, SKIP / st \\ st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''
where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example ceval_example1:
  (X ::= ANum 2;;
    IFB BLe (AId X) (ANum 1)
      THEN Y ::= ANum 3
      ELSE Z ::= ANum 4
    FI)
  / empty_state
  \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (t_update empty_state X 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
      + reflexivity.
      + apply E_Ass. reflexivity.
Qed.

Example ceval_example2 :
  (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
  (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (t_update empty_state X 0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (t_update (t_update empty_state X 0) Y 1).
    + apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity.
Qed.

Definition pup_to_n : com :=
  Y ::= ANum 0 ;;
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Y ::= APlus (AId Y) (AId X) ;;
    X ::= AMinus (AId X) (ANum 1)
  END.

Example pup_to_n_ex1 : pup_to_n / (t_update empty_state X 1) \\
  (t_update (t_update (t_update (t_update empty_state X 1) Y 0) Y 1) X 0).
Proof.
  unfold pup_to_n.
  apply E_Seq with (t_update (t_update empty_state X 1) Y 0).
  - apply E_Ass. reflexivity.
  - apply E_WhileLoop with (t_update (t_update (t_update (t_update empty_state X 1) Y 0) Y 1) X 0).
    + reflexivity.
    + apply E_Seq with (t_update (t_update (t_update empty_state X 1) Y 0) Y 1).
      * apply E_Ass. reflexivity.
      * apply E_Ass. reflexivity.
    + apply E_WhileEnd. reflexivity.
Qed.

Theorem pup_to_2_ceval : pup_to_n / (t_update empty_state X 2) \\
  t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  unfold pup_to_n.
  apply E_Seq with (t_update (t_update empty_state X 2) Y 0).
  - apply E_Ass. reflexivity.
  - apply E_WhileLoop with (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1).
    + reflexivity.
    + apply E_Seq with (t_update (t_update (t_update empty_state X 2) Y 0) Y 2).
      * apply E_Ass. reflexivity.
      * apply E_Ass. reflexivity.
    + apply E_WhileLoop with (t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
      * reflexivity.
      * { apply E_Seq with (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3).
        - apply E_Ass. reflexivity.
        - apply E_Ass. reflexivity. }
      * apply E_WhileEnd. reflexivity.
Qed.

Theorem ceval_deterministic : forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 H1 H2.
  generalize dependent st2.
  induction H1; intros st2 H2; inversion H2; subst.
  - reflexivity.
  - reflexivity.
  - assert (st' = st'0) as HQ1. { apply IHceval1. apply H1. }
    apply IHceval2. subst st'. assumption.
  - apply IHceval. assumption.
  - rewrite H in H7. inversion H7.
  - rewrite H in H7. inversion H7.
  - apply IHceval. assumption.
  - reflexivity.
  - rewrite H in H3. inversion H3.
  - rewrite H in H5. inversion H5.
  - assert (st' = st'0) as HQ1. { apply IHceval1. assumption. }
    subst st'. apply IHceval2. assumption.
Qed.

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. simpl. unfold t_update. reflexivity. Qed.

Theorem XtimesYinZ_spec : forall st st' a b,
  st X = a ->
  st Y = b ->
  XtimesYinZ / st \\ st' ->
  st' Z = a * b.
Proof.
  intros. inversion H1. subst.
  simpl. apply t_update_eq. Qed.

Theorem loop_never_stops : forall st st', ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
  induction contra; inversion Heqloopdef.
  - subst. inversion H.
  - subst. apply IHcontra2. reflexivity.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1 ;; c2 => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END => false
  end.

Inductive no_whilesR : com -> Prop :=
  | R_NoWhilesSkip : no_whilesR SKIP
  | R_NoWhilesAss : forall id val, no_whilesR (id ::= val)
  | R_NoWhilesSeq : forall c1 c2,
      no_whilesR c1 ->
      no_whilesR c2 ->
      no_whilesR (c1 ;; c2)
  | R_NoWhilesIf : forall exp ct cf,
      no_whilesR ct ->
      no_whilesR cf ->
      no_whilesR (IFB exp THEN ct ELSE cf FI).

Theorem no_whiles_eqv : forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intros. split.
  - intros H. induction c; try constructor.
    + apply IHc1. simpl in H. apply andb_true_iff in H.
      destruct H as [H1 H2]. apply H1.
    + apply IHc2. simpl in H. apply andb_true_iff in H.
      destruct H as [H1 H2]. apply H2.
    + apply IHc1. simpl in H. apply andb_true_iff in H.
      destruct H as [H1 H2]. apply H1.
    + apply IHc2. simpl in H. apply andb_true_iff in H.
      destruct H as [H1 H2]. apply H2.
    + inversion H.
  - intros H. induction H; try reflexivity; simpl;
      rewrite IHno_whilesR1; rewrite IHno_whilesR2;
      reflexivity.
Qed.

Theorem no_whiles_terminating : forall prog st,
  no_whiles prog = true ->
  exists st', prog / st \\ st'.
Proof.
  intros. induction prog.
  - exists st. apply E_Skip.
  - exists (t_update st i (aeval st a)).
    apply E_Ass. reflexivity.
  - simpl in H. apply andb_true_iff in H.
    destruct H as [H1 H2]. specialize (IHprog1 H1).
    specialize (IHprog2 H2). 
Abort.

Theorem no_whiles_terminating : forall c st,
  no_whilesR c ->
  exists st', c / st \\ st'.
Proof.
  intros c st H.
  generalize dependent st. induction c; intros.
  - exists st. apply E_Skip.
  - exists (t_update st i (aeval st a)).
    apply E_Ass. reflexivity.
  - (* Had to get help online for this case. I was originally doing
       induction on H (above) when I should have been doing it on c.
       That allows for inversion on H here in this case. *)
    inversion H. subst.
    (* These next two lines are immensely important to remember.
       I adapted this and made it simpler than the source I found
       online. I had tried this before, but hadn't specialized with
       the third argument {st, st'}, which prevented me from actually
       making use of the hypotheses once specialized. *)
    specialize (IHc1 H2 st). destruct IHc1 as [st' IHc1].
    specialize (IHc2 H3 st'). destruct IHc2 as [st'' IHc2].
    exists st''. apply E_Seq with st'; assumption.
  - (* Got this case completely on my own, though what I learned in
       the previous case was crucial here too. I did this a lot simpler
       than the person who did the source I found online. *)
    apply no_whiles_eqv in H. simpl in H.
    apply andb_true_iff in H. destruct H as [H1 H2].
    apply no_whiles_eqv in H1. apply no_whiles_eqv in H2.
    specialize (IHc1 H1 st). destruct IHc1 as [st' IHc1].
    specialize (IHc2 H2 st). destruct IHc2 as [st'' IHc2].
    destruct (beval st b) eqn:HBranch.
    + exists st'. apply E_IfTrue; assumption.
    + exists st''. apply E_IfFalse; assumption.
  - inversion H.
Qed.

Inductive sinstr : Type :=
  | SPush : nat -> sinstr
  | SLoad : id -> sinstr
  | SPlus : sinstr
  | SMinus : sinstr
  | SMult : sinstr.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr) : list nat :=
  match prog with
  | [] => stack
  | i::prog' =>
    match i with
    | SPush n => s_execute st (n::stack) prog'
    | SLoad id => s_execute st ((st id)::stack) prog'
    | SPlus =>
      match stack with
      | e1 :: e2 :: stack' => s_execute st ((e2 + e1) :: stack') prog'
      | _ => []
      end
    | SMinus =>
      match stack with
      | e1 :: e2 :: stack' => s_execute st ((e2 - e1) :: stack') prog'
      | _ => []
      end
    | SMult =>
      match stack with
      | e1 :: e2 :: stack' => s_execute st ((e2 * e1) :: stack') prog'
      | _ => []
      end
    end
  end.

Example s_execute1 : s_execute empty_state []
    [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (t_update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus] = [15; 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId id => [SLoad id]
  | APlus a1 a2 =>
      (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 =>
      (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 =>
      (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Example s_compile1 : s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.

Theorem s_compile_correct_lem1 :
  (* Found this lemma online when looking for help; the original
     author didn't actually finish his/her own s_compile_correct,
     so this lemma may or not be actually helpful. *)
  forall (st : state) (stack : list nat) (prog1 prog2 : list sinstr),
    s_execute st stack (prog1 ++ prog2)
      = s_execute st (s_execute st stack prog1) prog2.
Admitted.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. induction e.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite app_assoc.
    rewrite (s_compile_correct_lem1 st [] (s_compile e1 ++ s_compile e2) ([SPlus])). 
    rewrite (s_compile_correct_lem1 st [] (s_compile e1) (s_compile e2)).
    rewrite IHe1.
    rewrite <- (s_compile_correct_lem1 st [aeval st e1] (s_compile e2) ([SPlus])).
    rewrite (s_compile_correct_lem1 st [aeval st e1] (s_compile e2) ([SPlus])).
    rewrite (app_nil_end (s_compile e2)).
    rewrite (s_compile_correct_lem1 st [aeval st e1] (s_compile e2) []).
    Abort. (* Aborting for now, struggled with this for too long. *)

