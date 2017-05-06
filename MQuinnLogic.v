Require Export MQuinnTactics.

Check 3 = 3.
Check forall n m : nat, n + m = m + n.

Check forall n : nat, n = 2.
Check 3 = 4.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true : plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop := n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. split. reflexivity. reflexivity. Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split. apply HA. apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro. reflexivity. reflexivity.
Qed.

Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. induction n.
  - split. reflexivity. simpl in H. apply H.
  - split. inversion H. inversion H. Qed.

Lemma and_example2 : forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H. destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm. reflexivity. Qed.

Lemma and_example2' : forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm]. rewrite Hn. rewrite Hm. reflexivity. Qed.

Lemma and_example2'' : forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm. rewrite Hn. rewrite Hm. reflexivity. Qed.

Lemma and_example3 : forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity. Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof. intros P Q [HP HQ]. apply HP. Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof. intros P Q [HP HQ]. apply HQ. Qed.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ]. split.
  - apply HQ.
  - apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split. apply HP. apply HQ.
  - apply HR. Qed.

Check and.

Lemma or_example : forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O.
    reflexivity. Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left. apply HA. Qed.

Lemma zero_or_succ : forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity. Qed.

Lemma mult_eq_0 : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n] m H.
  - left. reflexivity.
  - right. destruct m. reflexivity. inversion H. Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ. Qed.

Module MyNot.

Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.

End MyNot.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra. Qed.

Fact not_implies_our_not : forall (P : Prop),
  ~P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P H1 Q H2.
  destruct H1. apply H2. Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra. Qed.

Check (0 <> 1).

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H. Qed.

Theorem not_False : ~False.
Proof.
  unfold not. intros H. inversion H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [H1 H2]. destruct H2. apply H1. Qed.

Theorem contradiction_implies_anything' : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H1. unfold not. intros H2. apply H2. apply H1. Qed.

(* Theorem: P implies ~~P, for any proposition P.
   Proof: Let P be a proposition. P could be either True or False.

   If P is True, we have True -> ~~True
                         True -> ~False
                         True -> True
   which follows trivially from application of the predicate.

   If P is False, we have False -> ~~False. By ex falso quodlibet,
   assuming False allows us to assert anything, including ~~False.
*)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2. unfold not. intros H3. destruct H2. apply H1 in H3.
  apply H3. Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  intros P [H1 H2]. destruct H2. apply H1. Qed.

(* Theorem: ~(P /\ ~P) for any proposition P.
   Proof: Let P be a proposition. P could be either True or False.

   If P is True, we have ~(True /\ ~True)
                         ~(True /\ False)
                         ~False
   which is True.

   If P is False, we have ~(False /\ ~False)
                          ~(False /\ True)
                          ~False
   which is True.
*)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet. apply H. reflexivity.
  - (* b = false *)
    reflexivity. Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H. exfalso. apply H. reflexivity.
  - reflexivity. Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity) : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HA HB].
  unfold iff. split.
  apply HB. apply HA. Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'. inversion H'. Qed.

Theorem iff_rel : forall P : Prop, P <-> P.
Proof.
  intros P. split.
  - intros H. apply H.
  - intros H. apply H. Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R. split.
  - destruct H. destruct H0. intros H3. apply H0. apply H. apply H3.
  - destruct H. destruct H0. intros H3. apply H1. apply H2. apply H3. Qed.

(* Got this one by myself, proving the reverse implication
   (second case) stumped me for awhile but after applying
   the nested intros destructor it all made sense. *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HL | HR].
    + { split.
      - left. apply HL.
      - left. apply HL. }
    + { destruct HR. split.
      - right. apply H.
      - right. apply H0. }
  - intros [[HP1 | HQ][HP2 | HR]].
    + (* P (and P) are true *) left. apply HP1.
    + (* P and R are true *) left. apply HP1.
    + (* P and Q are true *) left. apply HP2.
    + (* Q and R are true *) right. { split.
      - apply HQ.
      - apply HR. } Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example. Qed.

Lemma or_assoc : forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H. Qed.

Lemma mult_03 : forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p. rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity. Qed.

Lemma apply_iff_example : forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H. Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. exists (2 + m). apply Hm. Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H1. unfold not. intros [x H2]. apply H2. apply H1. Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ. Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity. Qed.

Example In_example_2 : forall n, In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl. intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity. Qed.

Lemma In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H. Qed.

Lemma In_map_iff : forall (A B : Type) (f: A->B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. induction l as [| x' l' IHl']. split.
  - simpl. intros H. exfalso. apply H.
  - simpl. intros H. destruct H. inversion H. apply H1.
  - split.
    + simpl. rewrite IHl'. intros H. { destruct H.
        - exists x'. split. apply H. left. reflexivity.
        - destruct H. exists x. destruct H. split.
          apply H. right. apply H0. }
    + simpl. intros H. destruct H. inversion H.
      (* When f x = y and x' = x, LHS will be true. *)
      (* When f x = y and In x l', RHS will be true.*)
      { destruct H1.
        - left. rewrite H1. apply H0.
        - right. apply IHl'. exists x. split. apply H0. apply H1. }
Qed.

Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a. induction l.
  - split.
    + simpl. intros H. right. apply H.
    + simpl. intros H. destruct H. destruct H. apply H.
  - split.
    + simpl. intros H. { destruct H.
      - left. left. apply H.
      - rewrite <- or_assoc. right. apply IHl. apply H. }
    + simpl. intros H. { destruct H. 
      - { destruct H.
        + left. apply H.
        + right. apply IHl. left. apply H. }
      - right. apply IHl. right. apply H. } Qed.

Fixpoint All {T:Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' /\ All P l'
  end.

Lemma All_In : forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l. induction l as [| x' l' IHl'].
  - split.
    + intros H. simpl. apply I.
    + intros H1 x. simpl. intros H2. destruct H2.
  - split.
    + simpl. intros H. { split.
      - apply H. left. reflexivity.
      - apply IHl'. intros x H2. apply H. right. apply H2. }
    + simpl. intros H x H2. inversion H. { destruct H2.
      - rewrite <- H2. apply H0.
      - apply IHl'. apply H1. apply H2. }
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => match oddb n with
           | true => Podd n 
           | false => Peven n
           end.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
  (oddb n = true -> Podd n) ->
  (oddb n = false -> Peven n) ->
  combine_odd_even Podd Peven n.
Proof.
  intros. induction n as [| n'].
  + unfold combine_odd_even. simpl. apply H0. reflexivity.
  + unfold combine_odd_even. destruct (oddb (S n')).
    - apply H. reflexivity.
    - apply H0. reflexivity. Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n -> oddb n = true -> Podd n.
Proof.
  intros. unfold combine_odd_even in H. rewrite H0 in H. apply H. Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n -> oddb n = false -> Peven n.
Proof.
  intros. unfold combine_odd_even in H. rewrite H0 in H. apply H. Qed.

Check plus_comm.

Lemma plus_comm3 : forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm. Abort.

Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  assert (H : m + p = p + m). {
    rewrite plus_comm. reflexivity.
  } rewrite H.
  reflexivity. Qed.

Lemma plus_comm3_take3 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity. Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity. Qed.

Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

Example function_equality_ex2 : (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
Abort.

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

Example function_equality_ex2 : (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm. Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_lemma1 :
  forall (X : Type) (l1 l2 : list X),
    rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  induction l1 as [|a l1].
  + simpl. reflexivity.
  + intros l2. simpl. rewrite (IHl1 [a]).
    rewrite <- app_assoc. simpl. rewrite <- (IHl1 (a::l2)).
    reflexivity. Qed.

(* I got most of this solution, but stuck up to rewrite (IHl1 [a])
   in the lemma above (used https://insight.io/github.com/sighingnow/amazing-coq/blob/HEAD/software-foundations/Logic.v
   for help. After adding that in, I was able to get the rest.
   I need more practice with applying theorems to arguments, i.e.,
   rewrite (IHl1 [a]), rewrite (IHl1 (a::12)), etc. *)
Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros. apply functional_extensionality. induction x as [| x l IHl].
  - unfold tr_rev. simpl. reflexivity.
  - simpl. rewrite <- IHl. unfold tr_rev. simpl.
    apply tr_rev_lemma1. Qed.