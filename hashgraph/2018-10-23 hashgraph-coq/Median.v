(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Nat.
Require Import Bool.
Require Import Omega.
Require Import List.
Require Import Sorting.
Require Import Permutation.

Require Import Tact.
Require Import Decide.
Require Import Relation.
Require Import Weight.
Require Import Calculate.
Require Import Majority.


Lemma Forall_app :
  forall (A : Type) (P : A -> Prop) (l m : list A),
    Forall P l
    -> Forall P m
    -> Forall P (l ++ m).
Proof.
intros A P l m Hl Hm.
apply Forall_forall.
intros x Hx.
so (in_app_or _#4 Hx) as [H | H].
  {
  apply (Forall_forall _#3 andel Hl); auto.
  }

  {
  apply (Forall_forall _#3 andel Hm); auto.
  }
Qed.


Lemma NoDup_app_invert :
  forall T (l1 l2 : list T),
    NoDup (l1 ++ l2)
    -> NoDup l1 /\ NoDup l2.
Proof.
intros T l1 l2 Hdist.
revert Hdist.
induct l1.

(* nil *)
{
intros Hdist.
cbn in Hdist.
split; auto.
apply NoDup_nil.
}

(* cons *)
{
intros x l1 IH Hdist.
rewrite <- app_comm_cons in Hdist.
invertc Hdist.
intros Hnin Hdist.
so (IH Hdist) as (Hdist1 & Hdist2).
split; auto.
apply NoDup_cons; auto.
contradict Hnin.
apply in_or_app; left; auto.
}
Qed.


(* Never actually use this. *)
Lemma sorted_unique :
  forall (U : Type) (R : U -> U -> Prop),
    order U R
    -> (forall x y, R x y \/ R y x)
    -> (forall x y, decidable (R x y))
    -> forall (l m : list U),
         Sorted R l
         -> Sorted R m
         -> Permutation l m
         -> l = m.
Proof.
intros U R Hord Htotal Hdec l m Hl Hm Hlm.
revert m Hl Hm Hlm.
induct l.

(** nil *)
{
intros m _ _ Hperm.
symmetry.
apply Permutation_nil; auto.
}

(** cons *)
{
intros x l' IH m Hl Hm Hlm.
destruct m as [| y m'].
  {
  exfalso.
  symmetry in Hlm.
  eapply Permutation_nil_cons; eauto.
  }
so (Sorted_inv _#4 Hl) as (Hl' & _).
so (Sorted_inv _#4 Hm) as (Hm' & _).
assert (x = y).
  {
  destruct (Permutation_in _ Hlm (or_introl (eq_refl _))) as [| Hinx].
    {
    subst y.
    reflexivity.
    }
  destruct (Permutation_in _ (Permutation_sym Hlm) (or_introl (eq_refl _))) as [| Hiny].
    {
    subst y.
    reflexivity.
    }
  apply (ord_antisym U R); auto.
    {
    exact (Forall_forall _#3 andel (@Sorted_extends _ _ (ord_trans _ _ Hord) _ _ Hl) _ Hiny).
    }

    {
    exact (Forall_forall _#3 andel (@Sorted_extends _ _ (ord_trans _ _ Hord) _ _ Hm) _ Hinx).
    }
  }
subst y.
f_equal.
apply IH; auto.
eapply Permutation_cons_inv; eauto.
}
Qed.


Lemma map_sorted :
  forall (T U : Type) (R : U -> U -> Prop) (f : T -> U) (l : list T),
    Sorted (fun x y => R (f x) (f y)) l
    -> Sorted R (map f l).
Proof.
intros S U R f l Hsorted.
apply Sorted_LocallySorted_iff.
so (Sorted_LocallySorted_iff _ _ andel Hsorted) as H.
clear Hsorted.
induct H.

(* nil *)
{
apply LSorted_nil.
}

(* cons1 *)
{
intros x.
cbn.
apply LSorted_cons1.
}

(* consn *)
{
intros x y l _ IH Hxy.
cbn in IH.
cbn.
apply LSorted_consn; auto.
}
Qed.


Lemma sorted_impl :
  forall T R R' l,
    inclusion T R R'
    -> Sorted R l
    -> Sorted R' l.
Proof.
intros T R R' l Hincl Hl.
apply Sorted_LocallySorted_iff.
so (Sorted_LocallySorted_iff _#3 andel Hl) as H.
clear Hl.
induct H; eauto using LocallySorted.
Qed.


Lemma strongly_sorted_app_inv :
  forall T (R : T -> T -> Prop) (l m : list T),
    StronglySorted R (l ++ m)
    -> forall x y,
         In x l
         -> In y m
         -> R x y.
Proof.
intros T R l m Hsorted x y Hx Hy.
revert Hsorted x Hx.
induct l.

(* nil *)
{
intros _ x Hx.
destruct Hx.
}

(* cons *)
{
intros z l IH Hsorted x Hx.
rewrite <- app_comm_cons in Hsorted.
invertc Hsorted.
intros Hsorted Hfirst.
destruct Hx as [Heq | Hx].
  {
  subst z.
  refine (Forall_forall _#3 andel Hfirst _ _).
  apply in_or_app.
  right; auto.
  }

  {
  apply IH; auto.
  }
}
Qed.


Lemma strongly_sorted_remove_middle :
  forall T (R : T -> T -> Prop) (l : list T) (x : T) (m : list T),
    StronglySorted R (l ++ x :: m)
    -> StronglySorted R (l ++ m).
Proof.
intros T R l x m.
induct l.

(* nil *)
{
intros Hsorted.
cbn.
cbn in Hsorted.
invert Hsorted; auto.
}

(* cons *)
{
intros y l IH Hsorted.
rewrite <- app_comm_cons in Hsorted.
rewrite <- app_comm_cons.
invertc Hsorted.
intros Hsorted Hfirst.
apply SSorted_cons; auto.
apply Forall_forall.
intros z Hz.
exploit (Forall_forall _#3 andel Hfirst z); auto.
apply in_or_app.
so (in_app_or _#4 Hz) as [H | H].
  {
  left; auto.
  }

  {
  right; right; auto.
  }
}
Qed.


Module Type WEIGHT_AND_VALUE.

Parameter T : Type.
Parameter U : Type.

Axiom eqT_decide : forall (x y : T), decidable (x = y).

Parameter wt : T -> nat.
Parameter vl : T -> U.

Axiom wt_pos : forall x, wt x > 0.

Parameter lebU : U -> U -> bool.

Axiom lebU_order : order U (fun x y => lebU x y = true).
Axiom lebU_total : forall x y, lebU x y = true \/ lebU y x = true.

Parameter inh : U.

End WEIGHT_AND_VALUE.


Module MedianFun (Import X:WEIGHT_AND_VALUE).


Module TOrder.

Definition t := T.

Definition leb (x y : T) := X.lebU (vl x) (vl y).

Lemma leb_total : forall (x y : T), leb x y = true \/ leb y x = true.
Proof.
intros x y.
unfold leb.
apply lebU_total.
Qed.

End TOrder.


Module TSort := Sort TOrder.


Definition leU (x y : U) : Prop := lebU x y = true.
Definition leT (x y : T) : Prop := leU (vl x) (vl y).


(* Strict select is easier to work with for some purposes:
   we don't need to deal with or rule out zero weights.
*)
Fixpoint sselect (l : list T) (n : nat) {struct l} : U :=
  match l with
  | nil => X.inh
  | cons x l' =>
      if ltb n (wt x) then
        vl x
      else
        sselect l' (n - wt x)
  end.


Fixpoint select (l : list T) (n : nat) {struct l} : U :=
  match l with
  | nil => X.inh
  | cons x l' =>
      if leb n (wt x) then
        vl x
      else
        select l' (n - wt x)
  end.


Definition median (l : list T) : U :=
  select (TSort.sort l) (S (sumweight wt l) / 2).


Lemma tsort_sorted :
  forall l,
    Sorted leT (TSort.sort l).
Proof.
intro l.
(** The lemmas Sorted_sort and LocallySorted_sort are reversed in the library. *)
refine (sorted_impl _#4 _ (TSort.LocallySorted_sort _)).
intros x y Hxy.
exact Hxy.
Qed.


Lemma leU_order : order U leU.
Proof.
exact lebU_order.
Qed.


Lemma leU_total : forall x y, leU x y \/ leU y x.
Proof.
exact lebU_total.
Qed.


Lemma leU_decide : forall x y, decidable (leU x y).
Proof.
intros x y.
unfold leU.
destruct (bool_dec (lebU x y) true); [left | right]; auto.
Qed.


Lemma eqU_decide : forall (x y : U), decidable (x = y).
Proof.
intros x y.
so (leU_decide x y) as [Hxy | Hnxy].
  {
  so (leU_decide y x) as [Hyx | Hyx].
    {
    left.
    apply (ord_antisym _ _ lebU_order); auto.
    }

    {
    right.
    intro.
    subst y.
    contradiction.
    }
  }
right.
intro.
subst y.
destruct Hnxy.
apply (ord_refl _ _ lebU_order).
Qed.


Lemma sselect_prefix :
  forall l m n x,
    Forall (fun y => x = vl y) l
    -> n < sumweight wt l
    -> sselect (l ++ m) n = x.
Proof.
intros l m n x Hl Hle.
revert n Hle.
induct Hl.

(* nil *)
{
intros n Hlt.
cbn in Hlt.
omega.
}

(* cons *)
{
intros y l -> _ IH n Hlt.
rewrite <- app_comm_cons.
cbn [sselect].
remember (ltb n (wt y)) as b eqn:Heqb.
destruct b; auto.
apply IH.
symmetry in Heqb.
so (Nat.ltb_ge _ _ andel Heqb).
rewrite -> sumweight_cons in Hlt.
omega.
}
Qed.


Lemma sselect_cons_r :
  forall (x : T) (l : list T) n,
    sselect (x :: l) (wt x + n) = sselect l n.
Proof.
intros x l n.
cbn [sselect].
remember (ltb (wt x + n) (wt x)) as b eqn:Heqb.
destruct b.
  {
  symmetry in Heqb.
  so (Nat.ltb_lt _ _ andel Heqb).
  omega.
  }
  
  {
  f_equal.
  omega.
  }
Qed.


Lemma sselect_app_r :
  forall (l m : list T) n,
    sselect (l ++ m) (sumweight wt l + n) = sselect m n.
Proof.
intros l m.
induct l.

(* nil *)
{
intro n.
cbn.
reflexivity.
}

(* cons *)
{
intros x l IH n.
rewrite <- app_comm_cons.
rewrite -> sumweight_cons.
rewrite <- Nat.add_assoc.
rewrite <- IH.
apply sselect_cons_r.
}
Qed.


Lemma sselect_lift :
  forall (l : list T) (x : T) (m : list T),
    Forall (fun y => vl x = vl y) l
    -> forall n, sselect (l ++ x :: m) n = sselect (x :: l ++ m) n.
Proof.
intros l x m Hl n.
so (lt_dec n (sumweight wt l + wt x)) as [Hlt | Hnlt].
  {
  transitivity (vl x).
    {
    replace (l ++ x :: m) with ((l ++ x :: nil) ++ m).
    2:{
      rewrite <- app_assoc.
      cbn.
      reflexivity.
      }
    apply sselect_prefix.
      {
      apply Forall_app; auto.
      }
  
      {
      rewrite -> sumweight_app.
      rewrite -> sumweight_cons.
      omega.
      }
    }

    {
    symmetry.
    rewrite -> app_comm_cons.
    apply sselect_prefix.
      {
      apply Forall_cons; auto.
      }

      {
      rewrite -> sumweight_cons.
      omega.
      }
    }
  }

  {
  transitivity (sselect m (n - sumweight wt l - wt x)).
    {
    replace n with (sumweight wt l + (wt x + (n - sumweight wt l - wt x))) at 1 by omega.
    rewrite -> sselect_app_r.
    rewrite -> sselect_cons_r.
    reflexivity.
    }

    {
    symmetry.
    replace n with (wt x + (sumweight wt l + (n - sumweight wt l - wt x))) at 1 by omega.
    rewrite -> sselect_cons_r.
    rewrite -> sselect_app_r.
    reflexivity.
    }
  }
Qed.


Lemma Transitive_leT : Relations_1.Transitive leT.
Proof.
intros x y z Hxy Hyz.
unfold leT in *.
eapply (ord_trans _ _ leU_order); eauto.
Qed.


Lemma sselect_unique :
  forall (l m : list T) (n : nat),
    Sorted leT l
    -> Sorted leT m
    -> Permutation l m
    -> sselect l n = sselect m n.
Proof.
intros l m n Hl Hm Hperm.
so (Sorted_StronglySorted Transitive_leT Hl) as Hl'.
so (Sorted_StronglySorted Transitive_leT Hm) as Hm'.
clear Hl Hm.
revert m n Hl' Hm' Hperm.
induct l.

(* nil *)
{
intros m n Hl Hm Hperm.
rewrite -> (Permutation_nil Hperm).
reflexivity.
}

(* cons *)
{
intros x l IH m n Hxl Hm Hperm.
so (Permutation_in _#4 Hperm (or_introl (eq_refl _))) as Hin.
so (in_split _#3 Hin) as (m1 & m2 & ->).
clear Hin.
so (Permutation_cons_app_inv _#5 Hperm) as Hperm'.
rewrite -> sselect_lift.
2:{
  apply Forall_forall.
  intros y Hy.
  apply (ord_antisym _ _ leU_order).
    {
    change (leT x y).
    so (StronglySorted_inv Hxl) as (_ & Hall).
    refine (Forall_forall _#3 andel Hall _ _).
    apply (@Permutation_in _ (m1 ++ m2)).
      {
      apply Permutation_sym; auto.
      }

      {
      apply in_or_app.
      left; auto.
      }
    }

    {
    change (leT y x).
    apply (strongly_sorted_app_inv _#4 Hm); auto.
    left; auto.
    }
  }
cbn [sselect].
set (b := ltb n (wt x)).
destruct b; auto.
so (StronglySorted_inv _#4 Hxl) as (Hl & _).
apply IH; auto.
eapply strongly_sorted_remove_middle; eauto.
}
Qed.


Lemma sselect_eq_select :
  forall l n,
    sselect l n = select l (S n).
Proof.
intros l.
induct l.

(* nil *)
{
intro n.
cbn.
reflexivity.
}

(* cons *)
{
intros x l IH n.
cbn [select sselect].
remember (ltb n (wt x)) as b eqn:Heq.
destruct b.
  {
  replace (leb (S n) (wt x)) with true; auto.
  }

  {
  replace (leb (S n) (wt x)) with false; auto.
  replace (S n - wt x) with (S (n - wt x)); auto.
  symmetry in Heq.
  so (Nat.ltb_ge _ _ andel Heq).
  omega.
  }
}
Qed.


Lemma select_unique :
  forall (l m : list T) (n : nat),
    Sorted leT l
    -> Sorted leT m
    -> Permutation l m
    -> select l n = select m n.
Proof.
intros l m n Hl Hm Hperm.
destruct n as [| n].
2:{
  rewrite <- !sselect_eq_select.
  apply sselect_unique; auto.
  }
destruct l as [| x l].
  {
  destruct m as [| y m].
    {
    cbn.
    reflexivity.
    }

    {
    destruct (Permutation_nil_cons _#3 Hperm).
    }
  }

  {
  destruct m as [| y m].
    {
    destruct (Permutation_nil_cons _#3 (Permutation_sym _#3 Hperm)).
    }
  
    {
    cbn.
    apply (ord_antisym _ _ leU_order).
      {
      assert (In y (cons x l)) as Hin.
        {
        apply (@Permutation_in _ (cons y m)); auto using Permutation_sym.
        left; auto.
        }
      destruct Hin as [| Hin].
        {
        subst y.
        apply (ord_refl _ _ leU_order).
        }

        {
        so (@Sorted_extends _ _ Transitive_leT _ _ Hl) as H.
        exact (Forall_forall _#3 andel H _ Hin).
        }
      }

      {
      assert (In x (cons y m)) as Hin.
        {
        apply (@Permutation_in _ (cons x l)); auto.
        left; auto.
        }
      destruct Hin as [| Hin].
        {
        subst y.
        apply (ord_refl _ _ leU_order).
        }

        {
        so (@Sorted_extends _ _ Transitive_leT _ _ Hm) as H.
        exact (Forall_forall _#3 andel H _ Hin).
        }
      }
    }
  }
Qed.


Lemma median_unique :
  forall (l m : list T),
    Permutation l m
    -> median l = median m.
Proof.
intros l m Hlm.
unfold median.
replace (sumweight wt m) with (sumweight wt l).
2:{
  apply permutation_weight; auto.
  }
apply select_unique; auto using tsort_sorted.
apply (@Permutation_trans _ _ l).
  {
  apply Permutation_sym.
  apply TSort.Permuted_sort.
  }
apply (@Permutation_trans _ _ m); auto.
apply TSort.Permuted_sort.
Qed.


Lemma select_spec :
  forall (l : list T) (n : nat),
    0 < n
    -> n <= sumweight wt l
    -> exists l1 x l2,
         l = l1 ++ x :: l2
         /\ select l n = vl x
         /\ sumweight wt l1 < n
         /\ n <= sumweight wt (l1 ++ x :: nil).
Proof.
intros l.
induct l.

(* nil *)
{
intros n Hlo Hhi.
exfalso.
cbn in Hhi.
omega.
}

(* cons *)
{
intros x l IH n Hlo Hhi.
cbn [select].
remember (leb n (wt x)) as b eqn:Heqb.
symmetry in Heqb.
destruct b.
  {
  exists nil, x, l.
  do2 3 split; auto.
  cbn.
  so (leb_complete _ _ Heqb).
  omega.
  }

  {
  exploit (IH (n - wt x)) as H.
    {
    so (leb_complete_conv _ _ Heqb).
    omega.
    }

    {
    rewrite -> sumweight_cons in Hhi.
    omega.
    }
  destruct H as (l1 & y & l2 & Heq & Hselect & Hlo' & Hi').
  exists (cons x l1), y, l2.
  do2 3 split; auto.
    {
    rewrite <- app_comm_cons.
    f_equal.
    auto.
    }

    {
    rewrite -> sumweight_cons.
    omega.
    }

    {
    rewrite <- app_comm_cons.
    rewrite -> sumweight_cons.
    omega.
    }
  }
}
Qed.


Lemma median_spec :
  forall (l : list T),
    length l > 0
    -> NoDup l
    -> exists x m n,
         median l = vl x
         /\ In x l
         /\ weight wt (fun y => In y l /\ leT y x) m
         /\ S (sumweight wt l) / 2 <= m
         /\ weight wt (fun y => In y l /\ leT x y) n
         /\ S (sumweight wt l) / 2 <= n.
Proof.
intros l Hnonempty Hdist.
set (n := S (sumweight wt l) / 2).
so (permutation_weight _ wt _ _ (TSort.Permuted_sort l)) as Heql.
exploit (select_spec (TSort.sort l) n) as H.
  {
  (* The result is also true if n=0, but we skip the special case since it's easy enough
     to show that n > 0.
  *)
  destruct l as [| x l].
    {
    exfalso.
    cbn in Hnonempty.
    omega.
    }
  subst n.
  apply Nat.div_str_pos.
  split; auto.
  rewrite -> sumweight_cons.
  so (wt_pos x).
  omega.
  }

  {
  rewrite <- Heql.
  remember (sumweight wt l) as m eqn:H.
  clear H.
  subst n.
  apply atleasthalf_le_all.
  }
destruct H as (l1 & x & l2 & Heq & Hselect & Hlower & Hupper).
rewrite -> Heq in Heql.
exploit (weight_subset _ wt (fun y => In y l /\ leT y x) (fun y => In y l) (sumweight wt l)) as H.
  {
  intros y Hiny.
  apply dec_and.
    {
    left; auto.
    }
  unfold leT.
  apply leU_decide.
  }

  {
  intros y (Hy & _).
  auto.
  }

  {
  apply weight_In; auto.
  }
destruct H as (n1 & Hweightn1 & _).
exploit (weight_subset _ wt (fun y => In y l /\ leT x y) (fun y => In y l) (sumweight wt l)) as H.
  {
  intros y Hiny.
  apply dec_and.
    {
    left; auto.
    }
  unfold leT.
  apply leU_decide.
  }

  {
  intros y (Hy & _).
  auto.
  }

  {
  apply weight_In; auto.
  }
destruct H as (n2 & Hweightn2 & _).
exists x, n1, n2.
do2 5 split; auto.
  {
  apply (@Permutation_in _ (TSort.sort l)).
    {
    apply Permutation_sym.
    apply TSort.Permuted_sort.
    }
  rewrite -> Heq.
  apply in_or_app; right.
  left; auto.
  }

  {
  refine (le_trans _#3 Hupper _).
  refine (weight_subset' _#6 _ _ (weight_In _#3 _) Hweightn1).
    {
    intros y _.
    apply dec_In.
    exact eqT_decide.
    }

    {
    intros y Hy.
    split.
      {
      apply (Permutation_in _#4 (Permutation_sym _#3 (TSort.Permuted_sort l))).
      rewrite -> Heq.
      apply in_or_app.
      so (in_app_or _#4 Hy) as [Hy' | Hy'].
        {
        left; auto.
        }

        {
        destruct Hy' as [H | H].
          {
          subst y.
          right; left; auto.
          }

          {
          destruct H.
          }
        }
      }

      {
      so (in_app_or _#4 Hy) as [Hy' | Hy'].
        {
        apply (strongly_sorted_app_inv _ _ l1 (x :: l2)); auto.
          {
          apply Sorted_StronglySorted; auto using Transitive_leT.
          rewrite <- Heq.
          apply tsort_sorted.
          }

          {
          left; auto.
          }
        }

        {
        destruct Hy' as [H | H].
          {
          subst y.
          unfold leT.
          apply ord_refl.
          exact leU_order.
          }

          {
          destruct H.
          }
        }
      }
    }

    {
    refine (NoDup_app_invert _ _ l2 _ andel).
    rewrite <- app_assoc.
    cbn.
    rewrite <- Heq.
    apply (Permutation_NoDup _#3 (TSort.Permuted_sort l)); auto.
    }
  }

  {
  assert (n <= sumweight wt (x :: l2)) as Hupper'.
    {
    rewrite -> sumweight_cons.
    replace (wt x + sumweight wt l2) with (sumweight wt l - sumweight wt l1).
    2:{
      rewrite -> Heql.
      rewrite -> sumweight_app.
      rewrite -> sumweight_cons.
      omega.
      }
    apply under_half_complement.
    exact Hlower.
    }
  refine (le_trans _#3 Hupper' _).
  refine (weight_subset' _#6 _ _ (weight_In _#3 _) Hweightn2).
    {
    intros y _.
    apply dec_In.
    exact eqT_decide.
    }

    {
    intros y Hy.
    split.
      {
      apply (Permutation_in _#4 (Permutation_sym _#3 (TSort.Permuted_sort l))).
      rewrite -> Heq.
      apply in_or_app.
      right; auto.
      }

      {
      destruct Hy as [Hy | Hy].
        {
        subst y.
        unfold leT.
        apply ord_refl.
        exact leU_order.
        }

        {
        apply (strongly_sorted_app_inv _ _ (l1 ++ x :: nil) l2); auto.
          {
          apply Sorted_StronglySorted; auto using Transitive_leT.
          rewrite <- app_assoc.
          cbn.
          rewrite <- Heq.
          apply tsort_sorted.
          }
          
          {
          apply in_or_app.
          right; left; auto.
          }
        }
      }
    }

    {
    refine (NoDup_app_invert _ l1 _ _ ander).
    rewrite <- Heq.
    apply (Permutation_NoDup _#3 (TSort.Permuted_sort l)); auto.
    }
  }
Qed.


Lemma majority_median :
  forall (P : T -> Prop) (l : list T),
    NoDup l
    -> majority wt P (fun x => In x l)
    -> exists x y,
         P x
         /\ P y
         /\ leU (vl x) (median l)
         /\ leU (median l) (vl y).
Proof.
intros P l Hdist Hmaj.
assert (length l > 0) as Hnonempty.
  {
  so (majority_inhabitant _#4 Hmaj) as (x & Hx).
  so (majority_incl _#4 Hmaj _ Hx) as Hin.
  destruct l.
    {
    destruct Hin.
    }

    {
    cbn.
    omega.
    }
  }
so (median_spec l Hnonempty Hdist) as (x & m & n & Hmedian & Hinx & Hweight_le & Hm & Hweight_ge & Hn).
assert (atleasthalf wt (fun y => In y l /\ leT y x) (fun y => In y l)) as Hmajle.
  {
  exists m, (sumweight wt l).
  do2 3 split; auto.
    {
    intros z Hz.
    destruct Hz; auto.
    }

    {
    apply weight_In; auto.
    }
  }
assert (atleasthalf wt (fun y => In y l /\ leT x y) (fun y => In y l)) as Hmajge.
  {
  exists n, (sumweight wt l).
  do2 3 split; auto.
    {
    intros z Hz.
    destruct Hz; auto.
    }

    {
    apply weight_In; auto.
    }
  }
so (majority_atleasthalf_intersect _#5 eqT_decide Hmaj Hmajle) as (y & HPy & Hiny & Hyx).
so (majority_atleasthalf_intersect _#5 eqT_decide Hmaj Hmajge) as (z & HPz & Hinz & Hxz).
exists y, z.
do2 3 split; auto.
  {
  rewrite -> Hmedian.
  exact Hyx.
  }

  {
  rewrite -> Hmedian.
  exact Hxz.
  }
Qed.



End MedianFun.


Require Import Hashgraph.
Require Import HashgraphFacts.
Require Import Vote.

Module EventWeightAndValue.

Definition T := event.
Definition U := nat.

Definition eqT_decide := eq_event_decide.

Definition wt := creatorstake.
Definition vl := timestamp.

Lemma wt_pos : forall x, wt x > 0.
Proof.
intro x.
unfold wt.
apply stake_positive.
Qed.

Definition lebU := Nat.leb.

Lemma lebU_order : order nat (fun x y => lebU x y = true).
Proof.
unfold lebU.
apply Build_order.
  {
  intros x.
  rewrite -> leb_iff.
  auto.
  }

  {
  intros x y z.
  rewrite -> !leb_iff.
  omega.
  }

  {
  intros x y.
  rewrite -> !leb_iff.
  omega.
  }
Qed.

Definition lebU_total := NatOrder.leb_total.

Definition inh := 0.

End EventWeightAndValue.


Module EventMedian := MedianFun EventWeightAndValue.

Export EventMedian.
