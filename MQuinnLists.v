Require Export MQuinnInduction.
Module NatList.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p:natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p:natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p:natprod) : nat :=
  match p with
  | (x, y) => x
  end.

Definition snd' (p:natprod) : nat :=
  match p with
  | (x, y) => y
  end.

Definition swap_pair (p:natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem surjective_pairing' : forall(n m : nat),
  (n, m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall(p : natprod),
  p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem surjective_pairing : forall(p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap: forall(p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem fst_swap_is_snd : forall(p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. ( cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match h with
              | O => (nonzeros t)
              | S _ => h :: (nonzeros t)
              end
  end.
Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match (oddb h) with
              | true => h :: (oddmembers t)
              | false => (oddmembers t)
              end
  end.
Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).
Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 => match l2 with
                | nil => l1
                | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
                end
  end.
Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: t => match (beq_nat h v) with
              | true => 1 + (count v t)
              | false => (count v t)
              end
  end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := [v] ++ s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  (negb (beq_nat 0 (count v s))).
Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match (beq_nat h v) with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.
Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h ::t => match (beq_nat h v) with
             | true => (remove_all v t)
             | false => h :: (remove_all v t)
             end
  end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h1 :: t1 =>  match (member h1 s2) with
                 | true => (subset t1 (remove_one h1 s2))
                 | false => false
                 end
  end.
Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem bag_theorem : forall n : nat, forall b : bag,
  (count n (add n b)) = (count n b) + 1.
Proof.
  intros n b. induction n.
  - simpl. rewrite plus_comm. reflexivity.
  - simpl. rewrite <- beq_nat_refl. rewrite plus_comm. reflexivity.
Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. simpl. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h ::t => rev t ++ [h]
  end.
Example test_rev1 : rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2 : rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl'.
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity. Qed.

Search rev.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity. Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite app_assoc. rewrite app_assoc. reflexivity. Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1.
  - simpl. reflexivity.
  - simpl. destruct n.
    + rewrite IHl1. reflexivity.
    + simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => match l2 with
           | nil => true
           | _ => false
           end
  | h1 :: t1 => match l2 with
           | nil => false
           | h2 :: t2 => match (beq_nat h1 h2) with
                         | true => (beq_natlist t1 t2)
                         | false => false
                         end
           end
  end.
Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite <- beq_nat_refl. rewrite IHl. reflexivity.
Qed.

Theorem count_member_nonzero : forall s : bag,
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros s. induction s.
  - simpl. reflexivity.
  - simpl. 
  (* I wanted to understand how simpl reduced so many steps
     to true; here is what I came up with:
     -> leb 1 (1 + (count 1 (n :: s))) = true (pull off list head)
     -> leb 0 (count 1 (n :: s)) = true (one iteration of leb)
     -> By match case analysis, leb 0 _ = true. Qed. *)
    reflexivity. Qed.

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: forall(s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s.
  - simpl. reflexivity.
  - simpl. destruct n.
    + simpl. rewrite ble_n_Sn. reflexivity.
    + simpl. rewrite IHs. reflexivity.
Qed.

Theorem rev_injective : forall l1 l2 : natlist,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. induction l1.
  - intros H. rewrite <- rev_involutive. rewrite <- H. reflexivity.
  - intros H.  rewrite <- rev_involutive. rewrite <- H.
    rewrite rev_involutive. reflexivity. Qed.

