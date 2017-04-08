Require Export MQuinnPoly.

Theorem silly1 : forall (n m o p : nat),
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2. rewrite <- eq1.
  apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m -> (forall(q r : nat), q = r -> [q;o] = [r;p])
              -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2_rewrite_only : forall (n m o p : nat),
  n = m -> (forall(q r : nat), q = r -> [q;o] = [r;p])
              -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. Abort. (* Cannot bind vars with rewrite, apparently. *)

Theorem silly2a : forall (n m : nat),
  (n, n) = (m, m) ->
    (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
      [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex : 
  (forall n, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true -> oddb 4 = true.
Proof.
  intros n eq1.
  (* Note: must not use simpl. *)
  apply eq1. Qed.

Theorem silly3_firsttry : forall (n : nat),
  true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl. symmetry. apply H. Qed.

Theorem rev_exercise1 : forall (l l': list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H. rewrite H. symmetry. apply rev_involutive.
  Qed.

(* Exercise apply_rewrite:
   Apply is used when the goal to be proved is exactly the same
   as some hypothesis or lemma. It is essentially a combination of
   rewrite and reflexivity.
   Rewrite allows us to replace a term with one side or the other of
   a hypothesis or previously proved lemma. It does not automatically
   simplify afterwards.
   Apply is especially useful when applying hypotheses with bound variables,
   as apply automatically maps variables in the context to these variables,
   similar to a function application.
*)

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Example trans_eq_example' : forall(a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with(m:=[c;d]).
  apply eq1. apply eq2. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m.
  - apply eq2.
  - apply eq1. Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H. reflexivity. Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall(n m : nat),
  [n] = [m] -> n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity. Qed.

Example inversion_ex3 : forall (X: Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq2. reflexivity. Qed.

Theorem beq_nat_0_l : forall n,
  beq_nat 0 n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - intros H. reflexivity.
  - simpl. intros H. inversion H. Qed.

Theorem inversion_ex4 : forall (n : nat),
  S n = 0 -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true -> [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

Example inversion_ex6: forall(X : Type)
                             (x y z : X) (l j : list X),
  x :: y :: l = [] -> y :: l = z :: j -> x = z.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1. Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall(n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 -> true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H. symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

(* This was my failed attempt; was unable to finish this. *)
Theorem plus_n_n_injective_failed : forall n m,
  n + n = m + m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m eq1. simpl in eq1. destruct m. reflexivity. inversion eq1.
  - intros m eq1. inversion eq1. rewrite <- plus_n_Sm in H0.
    symmetry in H0. Abort.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n'].
  - simpl. intros eq. destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  - intros eq. destruct m as [| m'].
    + inversion eq.
    + apply f_equal. Abort.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m eq. destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  - simpl. intros m eq. destruct m as [| m'].
    + inversion eq.
    + apply f_equal. apply IHn'. inversion eq. reflexivity. Qed.

Theorem beq_nat_true : forall n m, beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + inversion H.
  - intros m H. destruct m as [| m'].
    + inversion H.
    + apply IHn' in H. rewrite H. reflexivity. Qed.

(* Exercise: beq_nat_true_informal
   Theorem: ∀X n m, beq_nat n m = true -> n = m.
   Proof: By induction on n.
     Base: Our induction hypothesis is:
        beq_nat 0 m = true -> 0 = m
     Any natural number m is either zero or greater than zero.
     The first case trivially satisfies the implication 0 = m. The second
     implication 0 = S m' would only result if beq_nat 0 (S m') = true,
     which it does not.

     Inductive: Our induction hypothesis is:
        beq_nat (S n') m = true -> S n' = m
     Again, any natural number is either zero or grater than zero.
     The first case is trivially false: S n' = 0 would only arise
     if beq_nat (S n') 0 = true, contrary to its definition. The scecond
     case S n' = S m' is true if our value for S n' = S m'. And if
     S n' = S m', then n' = m', concluding our proof.
*)

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction m as [| m'].
  - simpl. intros eq. destruct n as [| n'].
    + reflexivity.
    + inversion eq.
  - intros eq. destruct n as [| n'].
    + inversion eq.
    + apply f_equal. Abort.

Theorem double_injective_take2 : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m'].
  - simpl. intros n eq. destruct n as [| n'].
    + reflexivity.
    + inversion eq.
  - simpl. intros n eq. destruct n as [| n'].
    + inversion eq.
    + simpl in eq. apply f_equal. apply IHm'.
      inversion eq. reflexivity. Qed.

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H': m = n). {apply beq_nat_true. apply H. }
  rewrite H'. reflexivity. Qed.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l. generalize dependent n. induction l as [| l'].
  - intros n H1. reflexivity.
  - intros n H1. simpl. simpl in H1. rewrite <- H1. simpl.
    apply IHl. reflexivity. Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m. simpl. unfold square.
  rewrite mult_assoc. assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity. Qed.

Definition foo (x : nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m. simpl. reflexivity. Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m. simpl. Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m. destruct m.
  - reflexivity.
  - reflexivity. Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m. unfold bar. destruct m.
  - reflexivity.
  - reflexivity. Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. destruct (beq_nat n 3).
  - reflexivity.
  - destruct (beq_nat n 5).
    + reflexivity.
    + reflexivity. Qed.

Theorem combine_split_MY_FAILED_ATTEMPT : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| l'].
  - intros l1 l2 H1. simpl in H1. inversion H1. reflexivity.
  - intros l1 l2 H1. Abort. (* Couldn't figure out what compound expressio
                               to destruct. *)

(* Second attempt, with guidance from online solution. *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].
  (* NOTE: Destructing as [x y] l' is critical here; I didn't do that
     before, so I got stuck b/c there wasn't much to work with: (l' :: l)
     rather than ([x y] :: l'). *)
  - intros l1 l2 H. inversion H. reflexivity.
  - intros l1 l2. simpl. (* The solution works with H before putting it
    in the context. *)
    destruct (split l').
    destruct l1. intros H. inversion H.
    destruct l2. intros H. inversion H.
    intros H. inversion H. simpl. rewrite IHl'.
    + reflexivity.
    + rewrite H2. rewrite H4. reflexivity.
Qed. (* Although I understand how this proof works, I have no idea
        how to provide a natural language explanation of it. *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true else if beq_nat n 5 then true else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3). Abort.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  - apply beq_nat_true in Heqe3.
    rewrite Heqe3. reflexivity.
  - destruct (beq_nat n 5) eqn:Heqe5.
    + apply beq_nat_true in Heqe5.
      rewrite Heqe5. reflexivity.
    + inversion eq. Qed.

Theorem bool_fn_applied_twice : forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b.
  - destruct (f true) eqn:Htrue.
    + rewrite Htrue. apply Htrue.
    + destruct (f false) eqn:Hfalse.
      apply Htrue. apply Hfalse.
  - destruct (f false) eqn:Hfalse.
    + destruct (f true) eqn:Htrue.
      apply Htrue. apply Hfalse.
    + rewrite Hfalse. apply Hfalse. Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m. destruct m.
    + reflexivity.
    + reflexivity.
  - simpl. intros m. destruct m.
    + reflexivity.
    + simpl. apply IHn'. Qed.

(* Theorem: For any nats n m, beq_nat n m = beq_nat m n.
   Proof: Let n be a nat. We prove by induction on n that, for any
          m, beq_nat n m = beq_nat m n.
   - First suppose n is 0, and m is a number such that beq_nat n m =
     beq_nat m n. We must show that both sides are equivalent, and thus
     order of parameters doesn't matter.

     When n = 0, m could be either 0 or non-zero. If m is 0, we have
        beq_nat 0 0 = beq_nat 0 0
     which is trivially equal. If m is non-zero, we have
        beq_nat 0 (S m') = beq_nat (S m') 0;
     both sides are false due to disjointedness of constructors for nat,
     and thus trivially equally.

   - Second, suppose n is non-zero, and m is again a number such that
     beq_nat n m = beq_nat m n. We must again show that both sides are
     equivalent, and thus order of parameters doesn't matter, with the
     unduction hypothesis being that all m, beq_nat n' m = beq_nat m n'.

     When n = (S n'), m could be either 0 or non-zero. If m is 0, we have
        beq_nat (S n') 0 = beq_nat 0 (S n')
     which is false on both sides and thus trivially equally. If m is
     non-zero, we have
        beq_nat n' m = beq_nat (S m) (S n')
     which, by injectivity of constructors, allows us to restate the
     equality as:
        beq_nat n' m = beq_nat m n'
     This is our induction hypothesis, and the proof is complete.
*)

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true -> beq_nat m p = true -> beq_nat n p = true.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m. destruct m.
    + simpl. intros p. destruct p. reflexivity.
      intros H1 H2. apply H2.
    + simpl. intros p. destruct p. reflexivity.
      intros H1 H2. apply H1.
  - intros m. destruct m.
    + intros p. destruct p.
      intros H1 H2. apply H1.
      intros H1 H2. simpl. apply IHn' with (m:=0).
      inversion H1. inversion H2.
    + intros p. destruct p.
      intros H1 H2. inversion H2.
      intros H1 H2. simpl. simpl in H1. simpl in H2.
      apply IHn' in H1. apply IHn' in H2.
      apply H2. apply H1. symmetry. apply beq_nat_refl. Qed.

Definition split_combine_statement : Prop := 
  forall X Y (l : list (X * Y)) l1 l2,
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).

Compute (split (combine [1;2] [false;false;true;true])).
Compute (split (combine [false;false;true;true] [1;2])).

Lemma split_combine_involutive :
  forall (X Y : Type) (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof.
  intros X Y. induction l1.
  - intros l2 H. simpl. destruct l2.
    + reflexivity.
    + inversion H.
  - intros l2 H. simpl. destruct l2.
    + inversion H.
    + simpl in H. simpl. rewrite IHl1.
      reflexivity. inversion H. reflexivity. Qed.

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l l1 l2 H1 H2. inversion H2. 
  apply split_combine_involutive. apply H1. Qed.


      