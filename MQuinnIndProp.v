Require Export MQuinnLogic.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn. Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn. Qed.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev 0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'. Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev 0 *) simpl. apply ev_0.
  - (* E = ev)SS n' E' *) simpl. apply E'. Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *)
    (* We must prove that n is even from no assumptions! *)
Abort.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E'].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'. Qed.

Theorem one_not_even : ~ ev 1.
Proof. intros H. inversion H. Qed.

Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [| n' E'].
  inversion E' as [| n'' E'']. apply E''. Qed.

Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros E. inversion E. inversion H0. inversion H2. Qed.

Lemma ev_even_firsttry : forall n, ev n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [| n' E'].
  - exists 0. reflexivity.
  - simpl. assert (I: (exists k', n' = double k') ->
                      (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. Abort.

Lemma ev_even : forall n, ev n -> exists k, n = double k.
Proof.
  intros n E. induction E as [| n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' Hk']. rewrite Hk'. exists (S k').
    reflexivity. Qed.

Theorem ev_even_iff : forall n, ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - apply ev_even.
  - intros [k Hk]. rewrite Hk. apply ev_double. Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2. induction H1 as [| n' E' IH].
  - simpl. apply H2.
  - simpl. apply ev_SS. apply IH. Qed.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - intros E. induction E.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply IHE1.
      * apply IHE2.
  - intros E. induction E.
    + apply ev'_0.
    + assert (H1 : S (S n) = n + 2). {
        rewrite <- plus_1_l. rewrite plus_comm. rewrite <- plus_1_l.
        rewrite <- plus_assoc. rewrite plus_comm. rewrite <- plus_assoc.
        simpl. reflexivity. }
      rewrite H1. apply ev'_sum.
      * apply IHE.
      * apply ev'_2.
Qed. (* Got this one by myself. *)

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m E1 E2. induction E2.
  - simpl in E1. apply E1.
  - apply IHE2. inversion E1. apply H0. Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p H1 H2.
  apply ev_sum with (n := n + m) (m := n + p) in H1.
  replace (n + m + (n + p)) with ((n + n) + (m + p)) in H1.
  apply ev_ev__ev with (n:=n + n) (m:=m + p) in H1.
  - apply H1.
  - apply ev_sum.
Abort. (* Unable to solve this one right now. *)

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 : 3 <= 3.
Proof. apply le_n. Qed.

Theorem test_le2 : 3 <= 6.
Proof. apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 : (2 <= 1) -> 2 + 2 = 5.
Proof. intros H. inversion H. inversion H2. Qed.

End Playground.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n : nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n : nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
  | tr_1 : forall n m, total_relation n m
  | tr_2 : forall m n, total_relation m n.

Definition empty_relation (n m : nat) := ~total_relation n m.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2.
  - apply H1.
  - apply le_S. apply IHle. Qed.

Theorem O_le_n : forall n, 0 <= n.
Proof.
  intros n. induction n.
  - apply le_n.
  - apply le_S. apply IHn. Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros m n H. induction H.
  - apply le_n.
  - apply le_S. apply IHle. Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. induction m.
  - inversion H.
    + apply le_n.
    + inversion H1.
  - inversion H.
    + apply le_n.
    + apply le_S. apply IHm. apply H1. Qed.

Theorem le_plus_l : forall a b, a <= a + b.
Proof.
  intros a b. induction b.
  - rewrite <- plus_n_0. apply le_n.
  - rewrite <- plus_n_Sm. apply le_S. apply IHb. Qed.

Theorem plus_lt : forall n1 n2 m, n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt. intros n1 n2 m H. split.
  + induction H.
    - rewrite plus_comm. rewrite plus_n_Sm. rewrite plus_comm.
      apply le_plus_l.
    - apply le_S. apply IHle.
  + induction H.
    - rewrite plus_n_Sm. rewrite plus_comm. apply le_plus_l.
    - apply le_S. apply IHle.
Qed. (* Finally got this myself, good example of induction on hypothesis. *)

Theorem lt_S : forall n m, n < m -> n < S m.
Proof.
  unfold lt. intros n m H. apply le_S in H. apply H.
Qed.

Theorem leb_complete : forall n m, leb n m = true -> n <= m.
Proof.
  intros n. (* NOTICE: m not being introduced, it must be kept
      general, otherwise you will not be able to apply IHn at the end. *)
  induction n.
  - induction m as [| m' IHm'].
    + intros H. apply le_n.
    + intros H. apply le_S. apply IHm'.
      (* This is the tricky part. If you look at the definition of
         le above, by the second constructor we know that if we have
         leb 0 m' = true, it follows that leb 0 (S m') is also true; this
         is true by assumption (hypothesis H). *)
      apply H.
  - induction m as [| m' IHm'].
    + simpl. intros H. inversion H.
    + simpl. intros H. apply n_le_m__Sn_le_Sm. apply IHn. apply H. Qed.

Theorem leb_correct : forall n m, n <= m -> leb n m = true.
Proof.
  intros.
  (* NOTICE: You must keep n general, otherwise you won't be able
     to apply IHm' at the end. *)
  generalize dependent n. 
  induction m as [| m' IHm'].
  - intros n H. inversion H. symmetry. apply leb_refl.
  - intros n H. induction n as [| n' IHn'].
    + reflexivity.
    + simpl. apply IHm'. apply Sn_le_Sm__n_le_m in H. apply H. Qed.

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros n m o H1 H2. apply leb_complete in H1.
  apply leb_complete in H2. apply leb_correct.
  generalize dependent H2. generalize dependent H1.
  apply le_trans. Qed.

Theorem leb_iff : forall n m, leb n m = true <-> n <= m.
Proof.
  split.
  - apply leb_complete.
  - apply leb_correct. Qed.