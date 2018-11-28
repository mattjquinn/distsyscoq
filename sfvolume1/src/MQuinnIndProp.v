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
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    + intros H. apply le_n.
    + intros H. apply le_S. apply IHm'.
      (* This is a tricky part. If you look at the definition of
         le above, by the second constructor we know that if we have
         leb 0 m' = true, it follows that leb 0 (S m') is also true; this
         is true by assumption (hypothesis H). *)
      apply H.
  - destruct m.
    + simpl. intros H. inversion H.
    + simpl. intros H. apply n_le_m__Sn_le_Sm. apply IHn'. apply H. Qed.

Theorem leb_correct : forall n m, n <= m -> leb n m = true.
Proof.
  intros.
  (* NOTICE: You must keep n general, otherwise you won't be able
     to apply IHm' at the end. *)
  generalize dependent n. 
  induction m as [| m' IHm'].
  - intros n H. inversion H. symmetry. apply leb_refl.
  - intros n H. destruct n.
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
  - apply leb_correct.
Qed.

Lemma Sn_eq_Sm__n_eq_m : forall n m : nat, S n = S m -> n = m.
Proof.
  intros. induction n as [| n' IHn'].
  - inversion H. reflexivity.
  - inversion H. reflexivity. Qed.

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall m n o, R m n o -> R (S m) n (S o)
  | c3 : forall m n o, R m n o -> R m (S n) (S o)
  | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
  | c5 : forall m n o, R m n o -> R n m o.

Example R_ex1 : R 1 1 2.
Proof. apply c2. apply c3. apply c1. Qed.

Example R_ex2 : R 2 2 6.
Proof. apply c2. apply c3. apply c2. apply c3.
       (* Not provable. *) Abort.

(* If we dropped c5, the set of provable propositions would not change;
   any reduction of o also involves a reduction of m (c2) or n (c3). *)

(* If we dropped c4, the set of provable propositions would not change;
   it increases m, n, and o rather than decreasing them towards 0. *)

Definition fR : nat -> nat -> nat := plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros m n o. split.
  - intros H. induction H.
    + reflexivity.
    + simpl. rewrite IHR. reflexivity.
    + unfold fR. rewrite <- plus_n_Sm. fold fR.
      rewrite IHR. reflexivity.
    + simpl in IHR. unfold fR in IHR. rewrite <- plus_n_Sm in IHR.
      fold fR in IHR. apply Sn_eq_Sm__n_eq_m in IHR.
      apply Sn_eq_Sm__n_eq_m in IHR. apply IHR.
    + unfold fR. unfold fR in IHR. rewrite plus_comm. apply IHR.
  - generalize dependent n. generalize dependent m.
    induction o as [| o' IHo'].
    + intros m n H. unfold fR in H.
      apply and_exercise in H. destruct H as [HA HB].
      rewrite HA. rewrite HB. apply c1.
    + intros m n H. destruct m.
      * { destruct n.
          - inversion H.
          - apply c3. apply IHo'. inversion H. reflexivity. }
      * apply c2. apply IHo'. inversion H. reflexivity.
Qed.

End R.

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq1 : forall l, subseq [] l
  | subseq2 : forall a t1 t2, subseq t1 t2 -> subseq (a :: t1) (a :: t2)
  | subseq3 : forall a l1 t2, subseq l1 t2 -> subseq l1 (a :: t2).

Example subseq_test1 : subseq [1;2;3] [1;2;3].
Proof. apply subseq2. apply subseq2. apply subseq2. apply subseq1. Qed.
Example subseq_test2 : subseq [1;2;3] [1;1;1;2;2;3].
Proof. apply subseq2. apply subseq3. apply subseq3. apply subseq2.
       apply subseq3. apply subseq2. apply subseq1. Qed.
Example subseq_test3 : subseq [1;2;3] [1;2;7;3].
Proof. apply subseq2. apply subseq2. apply subseq3.
       apply subseq2. apply subseq1. Qed.
Example subseq_test4 : subseq [1;2;3] [5;6;1;9;9;2;7;3;8].
Proof. apply subseq3. apply subseq3. apply subseq2. apply subseq3.
       apply subseq3. apply subseq2. apply subseq3. apply subseq2.
       apply subseq1. Qed.

Example subseq_fail1 : subseq [1;2;3] [1;2].
Proof. apply subseq2. apply subseq2. Abort.
Example subseq_fail2 : subseq [1;2;3] [1;3].
Proof. apply subseq2. apply subseq3. Abort.
Example subseq_fail3 : subseq [1;2;3] [5;6;2;1;7;3;8].
Proof. apply subseq3. apply subseq3. apply subseq3. apply subseq2.
       apply subseq3. apply subseq3. apply subseq3. Abort.

Theorem subseq_refl : forall l : list nat, subseq l l.
Proof.
  intros l. induction l.
  - apply subseq1.
  - apply subseq2. apply IHl.
Qed.

Theorem subseq_app : forall l1 l2 l3, subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros. induction H.
    (* By inducting on H, we aim to show that for each of the 3
       inductive constructors, appending an arbitrary list l3 to the
       second list does not change the fact that l1 is still a subseq. *)
  - apply subseq1.
  - simpl. apply subseq2. apply IHsubseq.
  - simpl. apply subseq3. apply IHsubseq.
Qed.

Theorem subseq_trans : forall l1 l2 l3,
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2. generalize dependent l1. induction H2.
  - intros l1 H1. inversion H1. apply subseq1.
  - intros l1 H1. 
    (* Here, H2: subseq t1 t2 links IHsubseq: subseq l1 t1 -> subseq l1 t2
       together, so to speak. *)
    inversion H1. (* Now we break apart the possibilities for l1. *)
    + apply subseq1.
    + apply subseq2. apply IHsubseq. apply H3.
    + apply subseq3. apply IHsubseq. apply H3.
  - intros. apply subseq3. apply IHsubseq. apply H1.
Qed. (* I got this by myself, but I have only a vague idea of why/how it
        works; by breaking up each inductive definition case
        (with induction H2), then once more in the second
        (with inversion H1), a "full analysis" is possible. *)

Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n l, R n l -> R (S n) (n :: l)
  | c3 : forall n l, R (S n) l -> R n l.

Example Rprov_ex1 : R 2 [1;0].
Proof. apply c2. apply c2. apply c1. Qed.
Example Rprov_ex2 : R 1 [1;2;1;0].
Proof. apply c3. apply c2. apply c3. apply c3. apply c2.
       apply c2. apply c2. apply c1. Qed.
Example Rprov_ex3 : R 6 [3;2;1;0].
Proof. Abort.
(* Propositions 1 and 2 are provable, because n is less than or equal to
   (list_head + 1) at all times. In Proposition 3 n is greater than
   (list_head + 1), and since there is no rule allowing us to reduce n
   independently of modifying the list, R does not hold. *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet : reg_exp T
  | EmptyStr : reg_exp T
  | Char : T -> reg_exp T
  | App : reg_exp T -> reg_exp T -> reg_exp T
  | Union : reg_exp T -> reg_exp T -> reg_exp T
  | Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar : forall x, exp_match [x] (Char x)
  | MApp : forall s1 re1 s2 re2,
            exp_match s1 re1 ->
            exp_match s2 re2 ->
            exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL : forall s1 re1 re2,
            exp_match s1 re1 ->
            exp_match s1 (Union re1 re2)
  | MUnionR : forall re1 s2 re2,
            exp_match s2 re2 ->
            exp_match s2 (Union re1 re2)
  | MStar0 : forall re, exp_match [] (Star re)
  | MStarApp : forall s1 s2 re,
                  exp_match s1 re ->
                  exp_match s2 (Star re) ->
                  exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof. apply (MApp [1] _ [2]). (* Notice how these align with
                                  MApp forall s1 re1 s2 re2 above;
                                  fourth wildcard underscore is implied. *)
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1;2] =~ Char 1).
Proof. intros H. inversion H. Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof. simpl. apply (MApp [1]). { apply MChar. } apply (MApp [2]).
  { apply MChar. } apply (MApp[3]). { apply MChar. } apply MEmpty.
Qed.

Lemma MStar1 : forall T s (re : reg_exp T), s =~ re -> s =~ Star re.
Proof.
  intros T s re H. rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T), ~(s =~ EmptySet).
Proof. intros. unfold not. intros H. inversion H. Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
  intros. destruct H as [| HL HR].
  - apply MUnionL. apply H.
  - apply MUnionR. apply HL.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) -> fold app ss [] =~ Star re.
Proof.
  intros. induction ss.
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros. apply H. simpl. right. apply H0.
Qed.

Lemma x_l1_x_l2__eq__l1_l2 : forall T (x : T) (l1 l2 : list T),
  x :: l1 = x :: l2 <-> l1 = l2.
Proof.
  intros T x l1 l2. split.
  - generalize dependent l2. induction l1.
    + intros l2 H. inversion H. reflexivity.
    + intros l2 H. inversion H. reflexivity.
  - generalize dependent l2. induction l1.
    + intros l2 H. inversion H. reflexivity.
    + intros l2 H. inversion H. reflexivity.
Qed.

Lemma x_hd_l_tl__eq__xl_app_tll : forall T (x : T) (l : list T),
  x :: l = [x] ++ l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. split.
  - generalize dependent s1. induction s2.
    + simpl. intros. inversion H. reflexivity.
    + simpl. intros. (* Got stuck here. *)  inversion H. inversion H3.
      simpl. apply x_l1_x_l2__eq__l1_l2. apply IHs2. apply H4.
  - generalize dependent s1. induction s2.
    + simpl. intros. inversion H. apply MEmpty.
    + simpl. intros. rewrite H. rewrite x_hd_l_tl__eq__xl_app_tll.
      apply MApp.
      * apply MChar.
      * apply IHs2. reflexivity.
Qed. (* I got most of this by myself, but had to get help when I got
        stuck before inverting on H then H3 above. Moral of the story:
        look at all the inversion evidence carefully to see if further
        inverting will yield useful evidence / goal. I was overwhelmed
        by all the generated hypotheses here originally and thought it
        was a dead-end, and thus didn't continue down that route. *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH
        |re1 s2 re2 Hmatch IH
        |re
        |s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - inversion Hin.
  - apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + left. apply (IH1 Hin).
    + right. apply (IH2 Hin).
  - simpl. rewrite in_app_iff. left. apply (IH Hin).
  - simpl. rewrite in_app_iff. right. apply (IH Hin).
  - destruct Hin.
  - (* NOTICE HERE: TWO induction hypotheses are generated,
       the second one useful in proving In xs2 for the recursive case. *)
    simpl. rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + apply (IH1 Hin).
    + apply (IH2 Hin).
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App re1 re2 => re_not_empty re1 && re_not_empty re2
  | Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star re' => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intros H. inversion H. induction H0.
    + reflexivity.
    + reflexivity.
    + simpl. apply andb_true_iff. split.
      * apply IHexp_match1. exists s1. apply H0_.
      * apply IHexp_match2. exists s2. apply H0_0.
    + simpl. apply orb_true_iff. left. apply IHexp_match.
      exists s1. apply H0.
    + simpl. apply orb_true_iff. right. apply IHexp_match.
      exists s2. apply H0.
    + reflexivity.
    + apply IHexp_match2. exists s2. apply H0_0.
  - intros H. induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + inversion H. apply andb_true_iff in H1.
      destruct H1 as [H1A H1B].
      destruct IHre1 as [s1 IHre1]. apply H1A.
      destruct IHre2 as [s2 IHre2]. apply H1B.
      exists (s1 ++ s2). apply MApp.
      apply IHre1. apply IHre2.
    + inversion H. apply orb_true_iff in H1.
      destruct H1 as [| H1A H1B].
      * destruct IHre1 as [s1 IHre1]. apply H0.
        exists s1. apply MUnionL. apply IHre1.
      * destruct IHre2 as [s2 IHre2]. apply H1A.
        exists s2. apply MUnionR. apply IHre2.
    + exists []. apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH | re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - simpl. intros. assumption.
  - simpl. intros. Abort.

Lemma star_app : forall T (s1 s2 : list T) (re re' : reg_exp T),
  s1 =~ re' -> re' = Star re -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re re' H1 H2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH | re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - intros. assumption.
  - inversion H2.
  - inversion H2.
  - inversion H2.
  - inversion H2.
  - simpl. intros. assumption.
  - Abort. (* Rather than doing this, use the remember tactic. *)

Lemma star_app : forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - simpl. intros. assumption.
  - inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc. apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
    s =~ Star re ->
    exists ss : list (list T),
      s = fold app ss []
      /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H. remember (Star re) as re'. induction H.
  inversion Heqre'.
  inversion Heqre'.
  inversion Heqre'.
  inversion Heqre'.
  inversion Heqre'.
  inversion Heqre'. exists []. simpl. intuition.
  specialize (IHexp_match2 Heqre'). destruct IHexp_match2 as [ss IHx]. 
  destruct IHx. exists (s1:: ss). split.
  simpl. rewrite H1. reflexivity.
 intros s' Hin. simpl in Hin. destruct Hin. congruence.
Abort.

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re -> exists ss : list (list T),
    s = fold app ss [] /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H1. remember (Star re) as re'. induction H1.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'. exists []. simpl. split.
    + reflexivity.
    + intros. inversion H.
  - (* Stuck in this case, had to seek help elsewhere. *)
    specialize (IHexp_match2 Heqre').
    (* Didn't know how to use specialize before, this is useful. *)
    destruct IHexp_match2 as [ss [IHxa IHxb]].
    (* This I had originally, but in a later step. Apparently too late. *)
    exists (s1 :: ss).
    (* This was my biggest mistake. I was trying to say that (s1 :: s2)
       exists; easily got the s1 case, but wasn't able to prove for s2. *)
    split.
    + simpl. rewrite IHxa. reflexivity.
    + simpl. intros s' Hin. destruct Hin.
      * rewrite <- H. inversion Heqre'. rewrite <- H1. apply H1_.
        (* Apparently this can all be done with just the congruence
           tactic, but I can't figure out exactly how it works. *)
      * apply IHxb. apply H.
        (* This makes me feel dumb; only two tactics applied, whereas
           my attempts spanned 4 or 5 entire lines. I think all the problems
           stemmed from my using exists (s1 :: s2) instead of (s1 :: ss). *)
Qed.

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => pumping_constant re1 + pumping_constant re2
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
end.

Lemma napp_plus : forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l. induction n.
  - reflexivity.
  - simpl. rewrite <- app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma a_plus_b_0__a_b_0 : forall a b : nat,
  a + b = 0 -> a = 0 /\ b = 0.
Proof.
  intros. destruct a.
  - simpl in H. rewrite H. split. reflexivity. reflexivity.
  - inversion H.
Qed.

Lemma pumping_lem1 : forall T (re1 re2 : reg_exp T) (s1 s2 : list T),
  s1 =~ re1 ->
  s2 =~ re2 ->
  pumping_constant (App re1 re2) <= length (s1 ++ s2) ->
  pumping_constant re1 <= length s1 /\ pumping_constant re2 <= length s2.
Proof.
  intros T re1 re2 s1 s2 H1 H2 H3.
  Admitted.

Lemma a_b_le_c__a_le_c : forall a b c : nat,
  a + b <= c -> a <= c.
Proof.
  intros. generalize dependent a. induction b.
  - intros a H. rewrite <- plus_n_0 in H. apply H.
  - intros a H. rewrite <- plus_n_Sm in H. rewrite plus_comm in H.
    rewrite plus_n_Sm in H. rewrite plus_comm in H. apply IHb in H.
    apply le_S in H. apply le_S_n in H. apply H.
Qed.

Lemma pumping_lem3 : forall T (re : reg_exp T) (s1 s2 : list T),
  s1 =~ re ->
  s2 =~ Star re ->
  pumping_constant (Star re) <= length (s1 ++ s2) ->
  pumping_constant re <= length s1
    /\ pumping_constant (Star re) <= length s2.
Proof.
  simpl. intros. induction H.
Admitted.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
Require Import Coq.omega.Omega.
  intros T re s Hmatch. induction Hmatch.
  - simpl. omega.
  - simpl. omega.
  - intros H. apply pumping_lem1 in H as [Hlen1 Hlen2].
    specialize (IHHmatch1 Hlen1). specialize (IHHmatch2 Hlen2).
    destruct IHHmatch1 as [a1 [a2 [a3 [IHH1A [IHH1B IHH1C]]]]].
    destruct IHHmatch2 as [b1 [b2 [b3 [IHH2A [IHH2B IHH2C]]]]].
    exists a1, a2, (a3 ++ b1 ++ b2 ++ b3). split.
    + rewrite IHH1A. rewrite <- app_assoc. rewrite <- app_assoc.
      rewrite IHH2A. reflexivity.
    + split.
      * apply IHH1B.
      * intros m. rewrite <- IHH2A.
        rewrite app_assoc. rewrite app_assoc.
        { apply (MApp ((a1 ++ (napp m a2)) ++ a3) re1 s2 re2).
          - rewrite <- app_assoc. apply IHH1C.
          - apply Hmatch2. }
    + apply Hmatch1.
    + apply Hmatch2.
  - simpl. intros H. apply a_b_le_c__a_le_c in H.
    specialize (IHHmatch H).
    destruct IHHmatch as [a1 [a2 [a3 [IHH1A [IHH1B IHH1C]]]]].
    exists a1, a2, a3. split.
    + apply IHH1A.
    + split.
      * apply IHH1B.
      * intros m. apply (MUnionL (a1 ++ napp m a2 ++ a3) re1 re2).
        apply IHH1C.
  - simpl. intros H. rewrite plus_comm in H. apply a_b_le_c__a_le_c in H.
    specialize (IHHmatch H).
    destruct IHHmatch as [b1 [b2 [b3 [IHH2A [IHH2B IHH2C]]]]].
    exists b1, b2, b3. split.
    + apply IHH2A.
    + split.
      * apply IHH2B.
      * intros m. apply (MUnionR re1 (b1 ++ napp m b2 ++ b3) re2).
        apply IHH2C.
  - simpl. intros. inversion H.
  - intros. apply pumping_lem3 in H as [H1 H2].
    specialize (IHHmatch1 H1).
    specialize (IHHmatch2 H2).
    destruct IHHmatch1 as [a1 [a2 [a3 [IHH1A [IHH1B IHH1C]]]]].
    destruct IHHmatch2 as [b1 [b2 [b3 [IHH2A [IHH2B IHH2C]]]]].
    exists a1, a2, (a3 ++ b1 ++ b2 ++ b3). split.
    + rewrite IHH1A. rewrite IHH2A. rewrite <- app_assoc.
      rewrite <- app_assoc. reflexivity.
    + split.
      * apply IHH1B.
      * intros m.
        rewrite app_assoc. rewrite app_assoc.
        { apply (MStarApp ((a1 ++ napp m a2) ++ a3) (b1 ++ b2 ++ b3) re).
          - rewrite <- app_assoc. apply IHH1C.
          - rewrite <- IHH2A. apply Hmatch2. }
    + apply Hmatch1.
    + apply Hmatch2.
Qed.
(* NOTE: I tried this for a long time but eventually had to move on.
   I'm 99% confident that the proof used for Lemma 'pumping' directly
   above is correct. However, I had to admit supporting lemmas 1 and 3.
   For lemma 1, I realize that the premises stated are not actually
   provable; ie., [] =~ EmptyStr for s1 and re1 are valid inputs to an
   Append expression, so breaking them apart for arbitrary s2 and re2
   is not possible b/c pumping_constant(EmptyStr) (which is 1) is not
   greater than the length of [] (which is 0). I do not know how to
   resolve this at this time.
*)
End Pumping.

Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] -> In n l.
Proof.
  intros n l. induction l as [| m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (beq_nat n m) eqn:H.
    + intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Module FirstTry.

Inductive reflect : Prop -> bool -> Prop :=
  | ReflectT : forall (P:Prop), P -> reflect P true
  | ReflectF : forall (P:Prop), ~P -> reflect P false.

End FirstTry.

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. unfold not. intros. inversion H0.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split.
  - destruct b.
    + intros _. reflexivity.
    + intros. inversion H. generalize dependent P.
      intros P H1 H2 []. apply H2.
  - destruct b.
    + intros. inversion H. apply H1.
    + intros H1. rewrite H1 in H. inversion H. apply H0.
Qed.

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] -> In n l.
Proof.
  intros n l. induction l as [| m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (beq_natP n m) as [H | H].
    + intros _. rewrite H. left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : forall n l, count n l = 0 -> ~(In n l).
Proof.
  intros. induction l.
  - intros H1. inversion H1.
  - simpl. intros [H1 | H2].
    + inversion H. generalize dependent H2. destruct (beq_natP n x).
      * intros H2. inversion H2.
      * unfold not in H0. rewrite H1 in H0. intros _. apply H0. reflexivity.
    + inversion H. generalize dependent H1. destruct (beq_natP n x).
      * intros H3. inversion H3.
      * intros H3. rewrite plus_0_n' in H3. apply IHl in H3.
        unfold not in H3. apply H3. apply H2.
Qed.

Inductive nostutter {X : Type} : list X -> Prop :=
  | NoStutter1 : nostutter []
  | NoStutter2 : forall (x : X), nostutter (x :: [])
  | NoStutter3 : forall (a b : X) (l : list X),
                 a <> b -> nostutter (b :: l) -> nostutter (a :: b :: l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply beq_nat_false_iff; auto. Qed.
Example test_nostutter_2: nostutter (@nil nat).
Proof. repeat constructor; apply beq_nat_false_iff; auto. Qed.
Example test_nostutter_3: nostutter [5].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.
Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.

Inductive in_order_merge {X : Type} : list X -> list X -> list X -> Prop :=
  | IOM1 : in_order_merge [] [] []
  | IOM2 : forall x : X, in_order_merge [] [x] [x]
  | IOM3 : forall x : X, in_order_merge [x] [] [x]
  | IOM4 : forall (x : X) (l1 l2 l3 : list X),
      in_order_merge l1 l2 l3 -> in_order_merge (x::l1) l2 (x::l3)
  | IOM5 : forall (x : X) (l1 l2 l3 : list X),
      in_order_merge l1 l2 l3 -> in_order_merge l1 (x::l2) (x::l3).

Example test_inordermerge_1 : in_order_merge [1;6;2] [4;3] [1;4;6;2;3].
Proof. apply IOM4. apply IOM5. apply IOM4. apply IOM4. apply IOM2. Qed.
Example test_inordermerge_2 : in_order_merge [4;3] [1;6;2] [1;4;6;2;3].
Proof. apply IOM5. apply IOM4. apply IOM5. apply IOM5. apply IOM3. Qed.

Lemma x_l_implies_x_in_l : forall (X : Type) (x : X) (l : list X),
  [x] = l -> In x l.
Proof.
  intros. induction l.
  - inversion H.
  - simpl. inversion H. left. reflexivity. Qed.

Lemma in_order_merge_x_l_implies_x_in_l1_or_l2 : forall (X : Type)
  (l l1 l1' l2 l2' : list X) (x : X),
  in_order_merge l1 l2 (x::l) -> l1 = x::l1' \/ l2 = x::l2'.
Admitted.

Lemma mq_lem1 : forall (X : Type) (l l1 l2 : list X) (x : X),
  in_order_merge l1 l2 (x :: l) -> In x l1 \/ In x l2.
Admitted.

Theorem filter_test_l__eq__l1_of_in_order_merge : forall (X : Type)
  (l l1 l2 : list X) (test : X -> bool),
  in_order_merge l1 l2 l ->
  All (fun x : X => test x = true) l1 ->
  All (fun x : X => test x = false) l2 ->
  filter test l = l1.
Proof.
  intros. induction l.
  - inversion H. simpl. reflexivity.
  - simpl. destruct (test x) eqn:TestEqn.
    + apply mq_lem1 in H as [|].
      * admit.
      * admit.
    + apply IHl. apply mq_lem1 in H. Abort.

(*
Theorem filter_test_l__eq__l1_of_in_order_merge : forall (X : Type)
  (l l1 l2 : list X) (test : X -> bool),
  in_order_merge l1 l2 l ->
  All (fun x : X => test x = true) l1 ->
  All (fun x : X => test x = false) l2 ->
  filter test l = l1.
Proof.
  intros. inversion H.
  - simpl. reflexivity.
  - simpl. rewrite <- All_In in H1. apply x_l_implies_x_in_l in H3.
    apply H1 in H3. rewrite H3. reflexivity.
  - simpl. rewrite <- All_In in H0. apply x_l_implies_x_in_l in H2.
    apply H0 in H2. rewrite H2. reflexivity.
  - 
*)

(*
 * MQUINN 08-13-2017 : In the interest of not getting so bogged down
   that I give up on Coq entirely, I am skipping the exercises after
   nostutter for now.
   TODO: Come back to these at a later date, especially for practice
   with inductive propositions.
*)