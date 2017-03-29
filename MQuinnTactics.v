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


