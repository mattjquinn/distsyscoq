Require Export MQuinnProofObjects.

Check nat_ind.

Theorem mult_0_r' : forall n : nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. rewrite -> IHn'. reflexivity. Qed.

Lemma n_eq_m__S_n_eq_S_m : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros n. apply nat_ind.
  - intros. rewrite H. reflexivity.
  - intros. rewrite H0. reflexivity.
  - apply n.
Qed.

Theorem plus_one_r' : forall n : nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. apply n_eq_m__S_n_eq_S_m.
    apply IHn'.
Qed.

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.

(* rgb_ind : forall P : rgb -> Prop,
    P red ->
    P green ->
    P blue ->
    forall r : rgb, P r *)
Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.
Check natlist_ind.

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(* natlist1_ind : forall P : natlist1 -> Prop,
    P nnil1 ->
    (forall (l : natlist1), P l ->
      forall (n : nat), P (nsnoc1 l n) ->
    forall n : natlist1, P n.
*)
(* Got the above almost right, except that forall (n : nat)
   needed to be moved down instead of grouped with
   forall (l : natlist1).
*)
Check natlist1_ind.

Inductive byntree : Type :=
  | bempty : byntree
  | bleaf : yesno -> byntree
  | nbranch : yesno -> byntree -> byntree -> byntree.

(*
  byntree_ind : forall P : byntree -> Prop,
    P bempty ->
    (forall y : yesno, P (bleaf y)) ->
    (forall b1 : byntree, P b1 ->
      (forall b2 : byntree, P b2 ->
        forall y : yesno, P (nbranch y b1 b2))) ->
    forall b : byntree, P b.
*)
Check byntree_ind.

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.
Check ExSet_ind.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
Check list_ind.

Inductive tree (X : Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.

(*
  tree_ind : forall (X : Type) (P : tree X -> Prop),
    (forall x : X, P (leaf X x)) ->
    (forall (t1 : tree X), P t1 ->
      forall (t2 : tree X), P t2 ->
        P (node X t1 t2)) ->
    forall t : tree X, P t.
*)
Check tree_ind.

Inductive mytype (X : Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.
Check mytype_ind.

Inductive foo (X Y : Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.
Check foo_ind.

Inductive foo' (X : Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

(*
  foo'_ind : forall (X : Type) (P : foo' X -> Prop),
    (forall (l : list X) (f : foo' X),
      P f ->
      P (C1 X l f) ) ->
    P (C2 X) ->
    forall f : foo' X, P f.
*)

Check foo'_ind.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n : nat, P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IHn. unfold P_m0r in IHn. unfold P_m0r.
    simpl. apply IHn. Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - intros m. rewrite <- plus_n_0. reflexivity.
  - intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

