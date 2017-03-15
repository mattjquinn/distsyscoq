Require Export MQuinnBasics.

Theorem plus_n_0_firsttry : forall n : nat,
  n = n + 0.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_n_0_secondtry : forall n : nat,
  n = n + 0.
Proof.
  intros n. destruct n as [|n'].
  - reflexivity.
  - simpl.
Abort.

Theorem plus_n_0 : forall n : nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
 intros n m. induction n as [| n' IHn'].
 - simpl. rewrite <- plus_n_0. reflexivity.
 - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite IHn'. rewrite negb_involutive. simpl. reflexivity.
Qed.

(* Difference b/w destruct and induction tactics.
   - destruct: replaces a function application with the individual match
     cases that comprise its function definition; each match case becomes a subgoal.
   - induction: generates two subgoals for a proposition: one for the base case
     and the other for the inductive case.
*)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite plus_comm. reflexivity. }
  rewrite H. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H1: m + (n + p) = n + p + m). {
    rewrite plus_comm. reflexivity. }
  (* LHS has m and p last; this moves m over so the
   * RHS also has m and p last. *)
  rewrite H1.
  (* Now that the RHS has m and p last, use associativity
   * to group them together into a single subterm. *)
  rewrite <- plus_assoc.
  assert (H2: m + p = p + m). {
    rewrite plus_comm. reflexivity. }
  (* By commutativity, the final terms on each side are identical. *)
  rewrite H2.
  reflexivity.
Qed.

Theorem mult_dist : forall a b : nat,
  a * (1 + b) = a + a * b.
Proof.
  intros a b. induction a as [|a' IHa'].
  - reflexivity.
    (* This simpl step was something I failed to do in
       my initial (lengthy) attempts to solve this. It appears
       to do a lot of simplifcation here. *)
  - simpl.
    (* Use plus_swap to switch the a' and b terms on the RHS
       to match up with the LHS. *)
    rewrite plus_swap.
    (* Use the inductive hypothesis to rewrite the RHS to match the left. *)
    rewrite <- IHa'.
    (* Simplify the 1 + b term to S b so the RHS completely matches the LHS. *)
    simpl. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction n as [| n' IHn'].
  - simpl. rewrite mult_0_r. reflexivity.
  - rewrite <- plus_1_l. rewrite mult_dist. simpl. rewrite IHn'. reflexivity.
Qed.

(* Reflection: Only simplification required.
 * INCORRECT: Induction required; must show for all n that leb n n is true. *)
Theorem leb_refl : forall n : nat,
  true = leb n n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.

(* Reflection: Destruct also required.
 * CORRECT *)
Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n. destruct n.
  - reflexivity.
  - reflexivity. Qed.

(* Reflection: Destruct also required.
 * CORRECT *)
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.

(* Reflection: Destruct and induction required.
   INCORRECT: Only induction required, above and beyond simple rewriting.
   Using destruct merely gives us our original hypothesis for the second case. *)
Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p. intros H. induction p as [| p' IHp' ].
  - simpl. rewrite H. reflexivity.
    (* This simpl looks at leb and see that if n is S n' and m is S m',
       we can rewrite as leb n' m'. Here, the S (meaning +1) is applied to
       p' + n and p' + m respectively, yielding p' + n and p' + m respectively. *)
  - simpl.
    (* The simplified output is identical to our induction hypothesis, allowing
       us to replace it with true. *)
    rewrite IHp'.
    reflexivity. Qed.

(* Reflection: Rewriting and destruct required.
   INCORRECT: Only rewriting required. Reflexivity auto-simplifies here. *)
Theorem S_nbeq_0: forall n : nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n. reflexivity. Qed.

(* Reflection: Rewriting and destruct required.
   CORRECT *)
Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros n. destruct n.
  - reflexivity.
  - simpl. rewrite plus_comm. rewrite plus_n_Sm. reflexivity. Qed.

(* Reflection: Rewriting and destruct required.
   CORRECT *)
Theorem all3_spec : forall b c : bool ,
  orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity. Qed.

(* Reflection: Induction required. 
   CORRECT *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite plus_assoc. reflexivity. Qed.

(* Reflection: Induction required.
   CORRECT *)
Theorem mult_assoc : forall n m p: nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite mult_plus_distr_r. rewrite IHn'. reflexivity. Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite plus_comm. rewrite <- plus_assoc.
  replace (p + n) with (n + p). reflexivity.
  rewrite plus_comm. reflexivity. Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b. induction b.
  - reflexivity.
  - simpl. rewrite <- plus_n_0. rewrite plus_n_Sm.
    rewrite <- plus_assoc.
    replace (bin_to_nat b + 1) with (S (bin_to_nat b)).
    + reflexivity.
    + rewrite <- plus_1_l. rewrite plus_comm. reflexivity.
  - simpl. rewrite <- plus_n_0. rewrite <- plus_n_0.
    rewrite <- plus_1_l. rewrite IHb. rewrite plus_assoc.
    rewrite plus_assoc. replace (1 + bin_to_nat b)
    with (S (bin_to_nat b)). rewrite <- plus_assoc.
    replace (bin_to_nat b + 1) with (S (bin_to_nat b)).
    + reflexivity.
    + rewrite plus_comm. reflexivity.
    + reflexivity.
Qed.

(* Part a. *)
Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.
Example test_nat_to_bin0: nat_to_bin 0 = Z.
Proof. simpl. reflexivity. Qed.
Example test_nat_to_bin1: nat_to_bin 1 = (I Z).
Proof. simpl. reflexivity. Qed.
Example test_nat_to_bin2: nat_to_bin 2 = (D (I Z)).
Proof. simpl. reflexivity. Qed.
Example test_nat_to_bin3: nat_to_bin 3 = (I (I Z)).
Proof. simpl. reflexivity. Qed.
Example test_nat_to_bin4: nat_to_bin 4 = (D (D (I Z))).
Proof. simpl. reflexivity. Qed.
Example test_nat_to_bin5: nat_to_bin 5 = (I (D (I Z))).
Proof. simpl. reflexivity. Qed.
Example test_nat_to_bin6: nat_to_bin 6 = (D (I (I Z))).
Proof. simpl. reflexivity. Qed.
Example test_nat_to_bin7: nat_to_bin 7 = (I (I (I Z))).
Proof. simpl. reflexivity. Qed.

Theorem nat_to_bin_to_nat_eq : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite bin_to_nat_pres_incr. rewrite IHn'. reflexivity.
Qed.

(* Part b: The problem with attempting to prove:

that starting with a binary number, converting to
a natural, and then back to binary yields the
same number we started with.

  is that the definition of binary allows for infinite
  representations of every natural number by starting with a
  prefix of D...DZ. For instance:

0: Z, DZ, DDZ, DDDZ, ...
1: IZ, IDZ, IDDZ, IDDDZ, ...
2: DIZ, DIDZ, DIDDZ, DIDDDZ, ...
...

*)

(* Part c. *)
Fixpoint normalize (b:bin) : bin := 
  match b with
  | Z => Z
  | I b' => I (normalize b')
  | D b' => match (bin_to_nat b') with
            | O => Z
            | S _ => D (normalize b')
            end
  end.
Example test_normalize1: normalize (D Z) = Z.
Proof. simpl. reflexivity. Qed.
Example test_normalize2: normalize (D (D Z)) = Z.
Proof. simpl. reflexivity. Qed.
Example test_normalize3: normalize (D (D (D Z))) = Z.
Proof. simpl. reflexivity. Qed.
Example test_normalize4: normalize (I (D (D (D Z)))) = I Z.
Proof. simpl. reflexivity. Qed.
Example test_normalize5: normalize (D (I (D (D (D Z))))) = D (I Z).
Proof. simpl. reflexivity. Qed.
Example test_normalize6: normalize (I Z) = (I Z).
Proof. simpl. reflexivity. Qed.

Lemma nat_even_sum_to_bin_always_d_prefix: forall n:nat,
  nat_to_bin ((S n) + (S n)) = D (nat_to_bin (S n)).
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. replace (n + S (S n)) with (S n + S n).
    + rewrite IHn. simpl. reflexivity.
    + rewrite <- plus_1_l. rewrite plus_n_Sm.
      rewrite plus_1_l. rewrite plus_swap.
      rewrite plus_assoc. rewrite <- plus_1_l.
      reflexivity.
Qed.

Lemma nat_odd_sum_to_bin_always_i_prefix: forall n:nat,
  nat_to_bin (n + n + 1) = I (nat_to_bin n).
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. replace (n + S n + 1) with (S n + n + 1).
    + simpl. rewrite IHn. simpl. reflexivity.
    + rewrite <- plus_assoc. rewrite plus_swap.
      rewrite plus_assoc. reflexivity.
Qed.

Theorem normalize_eq_bin_to_nat_to_bin: forall b:bin,
  (nat_to_bin (bin_to_nat b)) = normalize b.
Proof.
  intros b. induction b.
  - reflexivity.
  - simpl. rewrite <- plus_n_0. destruct (bin_to_nat b).
    + reflexivity.
    + rewrite <- IHb. rewrite nat_even_sum_to_bin_always_d_prefix.
      reflexivity.
  - simpl. rewrite <- plus_n_0. rewrite <- IHb.
    rewrite nat_odd_sum_to_bin_always_i_prefix.
    reflexivity. Qed.

(* Exericse: plus_comm_informal
   Reproduced here:

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
 intros n m. induction n as [| n' IHn'].
 - simpl. rewrite <- plus_n_0. reflexivity.
 - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

  Informally:
  Theorem: for any natural numbers n and m,
    n + m = m + n.
  Proof" By induction on n.
    First, suppose n = 0.
      Then, 0 + m = m + 0. Any m + 0 is m, so this case is true
        by reflexivity.
    Second, suppose n = 1 + n.
      Then (1 + n) + m = m + (1 + n).
      By definition of plus, we can rewrite this as 1 + (n + m) = m + (1 + n).
      By our induction hypothesis, we can rearrange to 1 + (m + n) = m + (1 + n).
      By definition of plus, the RHS can be written as 1 + (m + n). Qed.

*)

(* Exercise: beq_nat_refl_informal
   Reproduced here:

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.

   Informally:
   Theorem: for any natural number n, true = beq_nat n n.
   Proof: by induction on n.
     Base case: n = 0
       Given two arguments of 0, beq_nat 0 0 simplifies immediately to true.
     Inductive case: n = 1 + n.
       Given two arguments of 1 + n, beq_nat (1+n) (1+n) simplifies to
       beq_nat n' m'. This is true immediately from our inductive hypothesis. Qed.

*)