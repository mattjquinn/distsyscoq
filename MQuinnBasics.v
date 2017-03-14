Inductive day : Type :=
 | monday : day
 | tuesday : day
 | wednesday: day
 | thursday: day
 | friday: day
 | saturday: day
 | sunday: day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true)  = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true  true)  = true.
Proof. simpl. reflexivity. Qed.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb(b2)
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | _, _, _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check (negb true).
Check andb.

Module Playground1.
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).

Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.
Check Playground1.pred.
Compute (pred 5).

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).
Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | 0 => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S power' => mult base (exp base power')
  end.

Example test_exp1: (exp 2 8) = 256.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity) : nat_scope.
Check ((0 + 1) + 1).
Compute ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
          | O => true
          | S m' => false
          end
  | S n' => match m with
          | O => false
          | S m' => beq_nat n' m'
          end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  match beq_nat n m with
  | true => false
  | false => leb n m
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros. simpl. reflexivity. Qed.

Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_n_0 : forall n, n = n + 0.
Proof.
  intros n. simpl. Abort.

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros m n.
  rewrite -> plus_0_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  simpl.
  rewrite <- H.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity. Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [|n].
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

(* Calculates factorial in ascending order; inital value of i
 * should be 1. Rejected by Coq due to no decreasing fixpoint args.
 *)
(* Fixpoint factorial_nondec (n:nat) (i:nat) :=
  match n with
  | 0 => 1
  | S n' =>
    match leb i n with
    | true => mult i (factorial_nondec n (S i))
    | false => 1
    end
  end. *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  destruct b.
  - rewrite x. rewrite x. reflexivity.
  - rewrite x. rewrite x. reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  destruct b.
  - rewrite x. rewrite x. simpl. reflexivity.
  - rewrite x. rewrite x. simpl. reflexivity.
Qed.

Lemma and_false_is_false : forall b : bool,
  b && false = false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Lemma or_true_is_true : forall b : bool,
  b || true = true.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct c.
  - rewrite or_true_is_true. destruct b.
    + reflexivity.
    + simpl. intros H. rewrite H. reflexivity.
  - rewrite and_false_is_false. destruct b.
    + simpl. intros H. rewrite H. reflexivity.
    + reflexivity.
Qed.

Inductive bin : Type :=
  | Z : bin
  | D : bin -> bin
  | I : bin -> bin.

Fixpoint incr (b : bin) : bin :=
  match b with
  | Z => I Z
  | D b' => I b'
  | I b' => D (incr b')
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
  | Z => 0
  | D b' => 2 * (bin_to_nat b')
  | I b' => 2 * (bin_to_nat b') + 1
  end.

Example test_incr0: incr Z = I Z.
Proof. simpl. reflexivity. Qed.
Example test_incr1: incr (I Z) = (D (I Z)).
Proof. simpl. reflexivity. Qed.
Example test_incr2: incr (D (I Z)) = (I (I Z)).
Proof. simpl. reflexivity. Qed.
Example test_incr3: incr (I (I Z)) = (D (D (I Z))).
Proof. simpl. reflexivity. Qed.
Example test_incr4: incr (D (D (I Z))) = (I (D (I Z))).
Proof. simpl. reflexivity. Qed.
Example test_incr5: incr (I (D (I Z))) = (D (I (I Z))).
Proof. simpl. reflexivity. Qed.
Example test_incr6: incr (D (I (I Z))) = (I (I (I Z))).
Proof. simpl. reflexivity. Qed.
Example test_incr7: incr (I (I (I Z))) = (D (D (D (I Z)))).
Proof. simpl. reflexivity. Qed.

Example test_bin_to_nat0: bin_to_nat Z = 0.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat1: bin_to_nat (I Z) = 1.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat2: bin_to_nat (D (I Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat3: bin_to_nat (I (I Z)) = 3.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat4: bin_to_nat (D (D (I Z))) = 4.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat5: bin_to_nat (I (D (I Z))) = 5.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat6: bin_to_nat (D (I (I Z))) = 6.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat7: bin_to_nat (I (I (I Z))) = 7.
Proof. simpl. reflexivity. Qed.