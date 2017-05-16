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

(* I got most of this solution, but was stuck up to rewrite (IHl1 [a])
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

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [| k' IHk'].
  - reflexivity.
  - simpl. apply IHk'. Qed.

Theorem evenb_double_conv : forall n, exists k,
  n = if evenb n then double k else S (double k).
Proof.
  intros n. induction n as [| n' IHn'].
  - exists 0. reflexivity.
  - rewrite evenb_S. destruct (evenb n').
    + simpl. inversion IHn'. inversion H. exists x. reflexivity.
    + simpl. inversion IHn'. rewrite H. exists (S x).
      simpl. reflexivity. Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double. Qed.

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true else false.

Example even_1000 : exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

Lemma andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros. split.
  - intros H. split.
      + destruct b1. reflexivity. inversion H.
      + destruct b2. reflexivity. destruct H. destruct b1.
        reflexivity. reflexivity.
  - intros [H1 H2]. rewrite H1. rewrite H2. reflexivity. Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros. split.
  - intros H. destruct b1.
    + left. reflexivity.
    + destruct b2. right. reflexivity. destruct H. left. reflexivity.
  - intros [H1 | H2].
    + rewrite H1. reflexivity.
    + rewrite H2. apply or_true_is_true. Qed.

Lemma beq_ident_contra: forall a : nat, ~beq_nat a a = false.
Proof.
  intros a. induction a.
  - simpl. intros H. inversion H.
  - simpl. apply IHa. Qed.

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  intros. unfold not. split.
  - intros H1 H2. rewrite H2 in H1. apply beq_ident_contra in H1.
    destruct H1.
    (* I got stuck up to the destruct below, had to search for help. *)
  - intros H1. destruct (beq_nat x y) eqn:XEQY.
    + apply beq_nat_true in XEQY. exfalso. apply H1. apply XEQY.
    + reflexivity. Qed.

Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
                             (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | _, [] | [], _ => false
  | h1::t1, h2::t2 => beq h1 h2 && beq_list beq t1 t2
  end.

(* My original attempt. *)
Lemma beq_list_true_iff : forall A (beq : A -> A -> bool),
  (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq H1. split.
  - induction l1 as [| a1 l1].
    + { destruct l2 as [| a2 l2].
      - reflexivity.
      - simpl. intros H. inversion H. }
    + { induction l2 as [| a2 l2].
      - simpl. intros H. inversion H.
      - simpl. rewrite andb_true_iff. intros [H2 H3].
        apply H1 in H2. rewrite H2.
        (* How to get l1 equal to l2? *)
Abort.

(* I was able to start this one off well, but had to get help
   with the last part. I need to remember to possibly delay splitting
   an iff, and to use double induction if it makes sense. *)
Lemma beq_list_true_iff : forall A (beq : A -> A -> bool),
  (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq H1. (* MISTAKE1: Splitting now, instead of in each subcase. *)
  induction l1 as [| a l1 IHl1].
    - destruct l2 as [| b l2].
      + split.
        * reflexivity.
        * reflexivity.
      + simpl. split. 
        * intros H. inversion H.
        * intros H. inversion H.
    - induction l2 as [| b l2].
      + simpl. split.
        * intros H. inversion H.
        * intros H. inversion H.
      + simpl. split.
        * rewrite andb_true_iff. intros [H2 H3].
          apply H1 in H2.
          (* MISTAKE2: Not being able to apply the first induction
             hypothesis to H3 as done in the next step: *)
          apply IHl1 in H3. rewrite H2. rewrite H3.
          reflexivity.
        * intros H. rewrite andb_true_iff. { split.
          - apply H1. inversion H. reflexivity.
          - apply IHl1. inversion H. reflexivity. }
Qed.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l. induction l as [| x l].
  - simpl. split.
    + intros H. apply I.
    + intros H. reflexivity.
  - simpl. split.
    + rewrite andb_true_iff. rewrite IHl. intros H. apply H.
    + rewrite andb_true_iff. rewrite IHl. intros H. apply H.
Qed.

Definition excluded_middle := forall P : Prop, P \/ ~P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. apply H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

Theorem excluded_middle_irrefutable : forall (P : Prop),
  ~~(P \/ ~P).
Proof.
  intros P. unfold not. intros H. apply H.
  right. intros H1. apply H. left. apply H1. Qed.

Theorem not_exists_dist :
  excluded_middle -> forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* Forgot to unfold first. *)
  unfold excluded_middle. intros EM X P H1 x.
  (* Was trying to use apply (EM (P x)), should have been using
     destruct with appropriate destructive branches. *)
  destruct (EM (P x)) as [LHS | RHS].
  - apply LHS.
  - unfold not in H1. exfalso. apply H1.
    exists x. apply RHS. Qed.

Definition peirce := forall P Q : Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P : Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q : Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).

Theorem classical_axioms1 : excluded_middle <-> peirce.
Proof.
  unfold excluded_middle. unfold peirce. split.
  (* Don't have the motivation/brainpower to do these right now,
     aborting for now. *)
  Abort.