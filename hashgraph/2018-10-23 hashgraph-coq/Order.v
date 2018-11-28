(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Nat.
Require Import Bool.
Require Import Omega.
Require Import List.
Require Import Permutation.

Require Import Tact.
Require Import Decide.
Require Import Relation.
Require Import HashgraphFacts.
Require Import Sees.
Require Import Round.
Require Import Progress.
Require Import Decision.
Require Import Consensus.
Require Import Famous.
Require Import Received.
Require Import Median.


Definition earliest_observer (x y z : event) : Prop :=
  x @= y
  /\ (forall y', self_parent y' y -> x @= y' -> False)
  /\ y $= z.


Definition time_received (s : sample) (W : world) (x : event) (t : nat) : Prop :=
  exists i l,
    received s W i x
    /\ NoDup l
    /\ (forall y,
          (exists w,
             ufwitness s W i w
             /\ earliest_observer x y w)
          <-> In y l)
    /\ t = median l.


(** The consensus order. *)
Definition corder (s : sample) (W : world) (x y : event) : Prop :=
  exists i j t u,
    received s W i x
    /\ received s W j y
    /\ time_received s W x t
    /\ time_received s W y u
    /\ (i < j
        \/ (i = j /\ t < u)
        \/ (i = j /\ t = u /\ Is_true (textorder x y))).


Lemma earliest_observer_impl_self_ancestor :
  forall x y z,
    earliest_observer x y z
    -> y $= z.
Proof.
intros x y z H.
destruct H as (_ & _ & H).
exact H.
Qed.


Lemma time_received_fun :
  forall s W x t u,
    time_received s W x t
    -> time_received s W x u
    -> t = u.
Proof.
intros s W x t u Ht Hu.
destruct Ht as (i & l & Hi & Hdistl & Hl & ->).
destruct Hu as (i' & m & Hi' & Hdistm & Hm & ->).
so (received_fun _#5 Hi Hi'); subst i'.
clear Hi'.
apply median_unique.
apply NoDup_Permutation; auto.
intro y.
rewrite <- Hl.
rewrite <- Hm.
reflexivity.
Qed.


Lemma received_impl_time_received :
  forall s W x i,
    received s W i x
    -> finite (ufwitness s W i)
    -> exists t,
         time_received s W x t.
Proof.
intros s W x i Hrec Hfinf.
cut (finite (fun y =>
               exists w,
                 ufwitness s W i w
                 /\ earliest_observer x y w)).
  {
  intro Hfin.
  destruct Hfin as (l & Hl).
  so (Cardinality.deduplicate _ l eq_event_decide) as (l' & Hdist & Hl').
  exists (median l').
  exists i, l'.
  do2 3 split; auto.
  intro y.
  transitivity (In y l); auto.
  }
apply finite_exists; auto.
intros w Hfwit.
apply (finite_subset _ _ (fun y => y @= w)).
  {
  intros y Hy.
  destruct Hy as (_ & _ & Hyw).
  apply self_ancestor_impl_ancestor; auto.
  }

  {
  intros y.
  apply dec_and; [| apply dec_and].
    {
    apply ancestor_decide.
    }

    {
    apply dec_forall_imp_finite.
      {
      apply (finite_subset _ _ (fun y' => parent y' y)).
        {
        intros y' Hy'.
        apply self_parent_impl_parent; auto.
        }

        {
        intro.
        apply self_parent_decide.
        }

        {
        apply parent_finite.
        }
      }

      {
      intros y' Hyy.
      apply dec_not.
      apply ancestor_decide.
      }
    }

    {
    apply self_ancestor_decide.
    }
  }

  {
  apply ancestor_finite.
  }
Qed.


Lemma time_received_defined :
  forall s x,
    member (global s) x
    -> honest (creator x)
    -> exists t,
         time_received s (global s) x t.
Proof.
intros s x Hsx Hhonest.
so (received_defined s x Hsx Hhonest) as (i & Hrec).
eapply received_impl_time_received; eauto.
apply ufwitness_finite_global.
Qed.


Theorem corder_antisym :
  forall s,
    antisymmetric event (corder s (global s)).
Proof.
intros s x y Hxy Hyx.
destruct Hxy as (i & j & t & u & Hi & Hj & Ht & Hu & Hxy).
destruct Hyx as (j' & i' & u' & t' & Hj' & Hi' & Hu' & Ht' & Hyx).
so (received_fun _#5 Hi Hi'); subst i'.
so (received_fun _#5 Hj Hj'); subst j'.
so (time_received_fun _#5 Ht Ht'); subst t'.
so (time_received_fun _#5 Hu Hu'); subst u'.
destruct Hxy as [Hij | [Htu | Hxy]]; destruct Hyx as [Hji | [Hut | Hyx]]; try (exfalso; omega).
destruct Hxy as (_ & _ & Hxy).
destruct Hyx as (_ & _ & Hyx).  
apply (ord_antisym _ _ textorder_order); auto.
Qed.    


Theorem corder_trans :
  forall s,
    transitive event (corder s (global s)).
Proof.
intros s.
intros x y z Hxy Hyz.
destruct Hxy as (i & j & t & u & Hi & Hj & Ht & Hu & Hxy).
destruct Hyz as (j' & k & u' & v & Hj' & Hk & Hu' & Hv & Hyz).
so (received_fun _#5 Hj Hj'); subst j'.
so (time_received_fun _#5 Hu Hu'); subst u'.
destruct Hxy as [Hij | [(Hij & Htu) | (Hij & Htu & Hxy)]]; destruct Hyz as [Hjk | [(Hjk & Huv) | (Hjk & Huv & Hyz)]];
exists i, k, t, v;
do2 4 split; auto;
try (left; omega);
try (right; left; omega).
right; right.
subst j k u v.
do2 2 split; auto.
eapply (ord_trans _ _ textorder_order); eauto.
Qed.


Theorem corder_total :
  forall s x y,
    member (global s) x
    -> member (global s) y
    -> honest (creator x)
    -> honest (creator y)
    -> corder s (global s) x y \/ corder s (global s) y x.
Proof.
intros s x y Hsx Hsy Hhonestx Hhonesty.
so (received_defined _ _ Hsx Hhonestx) as (i & Hrecx).
so (received_defined _ _ Hsy Hhonesty) as (j & Hrecy).
so (time_received_defined _ _ Hsx Hhonestx) as (t & Htimex).
so (time_received_defined _ _ Hsy Hhonesty) as (u & Htimey).
so (lt_eq_lt_dec i j) as [[Hij | Heq] | Hji].
  {
  left.
  exists i, j, t, u.
  do2 4 split; auto.
  }

2:{
  right.
  exists j, i, u, t.
  do2 4 split; auto.
  }
subst j.
so (lt_eq_lt_dec t u) as [[Htu | Heq] | Hut].
  {
  left.
  exists i, i, t, u.
  do2 4 split; auto.
  }

2:{
  right.
  exists i, i, u, t.
  do2 4 split; auto.
  }
subst u.
so (textorder_total x y) as [Hxy | Hyx].
  {
  left.
  exists i, i, t, t.
  do2 4 split; auto.
  }

  {
  right.
  exists i, i, t, t.
  do2 4 split; auto.
  }
Qed.


(** Theorem 5.19 *)
Corollary corder_refl :
  forall s x,
    member (global s) x
    -> honest (creator x)
    -> corder s (global s) x x.
Proof.
intros s x Hsx Hhonest.
so (corder_total _#3 Hsx Hsx Hhonest Hhonest) as H.
destruct H; auto.
Qed.


Lemma fwitness_stable :
  forall s W W' i y,
    extends W W'
    -> (forall x, decidable (member W x))
    -> nonempty W
    -> received_by s W i y
    -> forall x, fwitness s W i x <-> fwitness s W' i x.
Proof.
intros s V W i q Hextends Hdec Hne Hrb w.
so (received_by_inhabited _#4 Hne Hrb) as Hinh.
destruct Hrb as (Hsettled & _).
clear q.
split.
  {
  intros (Hwit & Hfamous).
  split; eauto using extends_famous.
  }

  {
  intros (Hwit & Hfamous).
  assert (member V w) as Vw.
    {
    so (Hdec w) as [| Vnw]; auto.
    exfalso.
    so Hinh as (y & Vy & Hroundy).
    so (ancestor_witness _#3 (le_refl _) Hroundy) as (z & Hzy & Hwitz).
    so (Hsettled i z (le_refl _) (world_closed _#3 Hzy Vy) Hwitz) as (v & b & Vv & Hdecisionz).
    so (no_late_fame_world _#7 Vv Vnw Hwitz Hwit Hdecisionz) as Hdecision.
    destruct Hfamous as (u & Wu & Hdecision').
    so (decision_consistent _#7 (Hextends _ Vv) Wu Hdecision Hdecision') as H.
    discriminate H.
    }
  split; auto.
  so (Hsettled i w (le_refl _) Vw Hwit) as (y & b & Vy & Hdecision).
  destruct Hfamous as (z & Wz & Hdecision').
  so (decision_consistent _#7 (Hextends _ Vy) Wz Hdecision Hdecision'); subst b.
  exists y.
  split; auto.
  }
Qed.


Lemma ufwitness_stable :
  forall s W W' i y,
    extends W W'
    -> (forall x, decidable (member W x))
    -> nonempty W
    -> received_by s W i y
    -> forall x, ufwitness s W i x <-> ufwitness s W' i x.
Proof.
intros s V W i q Hextends Hdec Hne Hrb w.
split.
  {
  intro Hw.
  destruct Hw as (Hw & Hmin).
  split.
    {
    exact (fwitness_stable _#5 Hextends Hdec Hne Hrb _ andel Hw).
    }
  intros y Hy Heqcr.
  apply Hmin; auto.
  exact (fwitness_stable _#5 Hextends Hdec Hne Hrb _ ander Hy).
  }

  {
  intro Hw.
  destruct Hw as (Hw & Hmin).
  split.
    {
    exact (fwitness_stable _#5 Hextends Hdec Hne Hrb _ ander Hw).
    }
  intros y Hy Heqcr.
  apply Hmin; auto.
  exact (fwitness_stable _#5 Hextends Hdec Hne Hrb _ andel Hy).
  }
Qed.


Lemma time_received_consistent :
  forall s W W' x t,
    extends W W'
    -> (forall x, decidable (member W x))
    -> nonempty W
    -> time_received s W x t
    -> time_received s W' x t.
Proof.
intros s V W x t Hextends Hdec Hne Htr.
destruct Htr as (i & l & Hrec & Hdist & Hl & ->).
exists i, l.
do2 3 split; auto.
  {
  eapply received_consistent; eauto.
  }
so (ufwitness_stable _#5 Hextends Hdec Hne (Hrec andel)) as Hfiff.
intros y.
rewrite <- Hl.
split.
  {
  intros (w & H).
  exists w.
  rewrite -> Hfiff.
  exact H.
  }

  {
  intros (w & H).
  exists w.
  rewrite <- Hfiff.
  exact H.
  }
Qed.


(** A hashgraph cannot later discover new predecessors in the consensus order. *)
Theorem corder_stable :
  forall s W W' x y,
    extends W W'
    -> (forall x, decidable (member W x))
    -> nonempty W
    -> corder s W y y
    -> corder s W' x y
    -> corder s W x y.
Proof.
intros s V W x y Hextends Hdec Hne HVy HWxy.
destruct HVy as (i & _ & t & _ & Hi & _ & Ht & _).
destruct HWxy as (j & i' & u & t' & Hj & Hi' & Hu & Ht' & Hxy).
so (received_consistent _#5 Hextends Hdec Hne Hi) as Hi''.
so (received_fun _#5 Hi' Hi''); subst i'.
clear Hi''.
so (time_received_consistent _#5 Hextends Hdec Hne Ht) as Ht''.
so (time_received_fun _#5 Ht' Ht''); subst t'.
clear Ht''.
exists j, i, u, t.
assert (received s V j x) as Hrec.
  {
  eapply received_cumulative; eauto.
  omega.
  }
do2 4 split; auto.
destruct Hu as (j' & l & Hrec' & Hdist & Hl & Hu).
so (received_fun _#5 (received_consistent _#5 Hextends Hdec Hne Hrec) Hrec'); subst j'.
exists j, l.
do2 3 split; auto.
intro z.
rewrite <- Hl.
so (ufwitness_stable _#5 Hextends Hdec Hne (Hrec andel)) as Hfiff.
split.
  {
  intros (w & H).
  exists w.
  rewrite <- Hfiff.
  exact H.
  }

  {
  intros (w & H).
  exists w.
  rewrite -> Hfiff.
  exact H.
  }
Qed.


(** A hashgraph eventually places every (honest) event into the consensus order. *)
Theorem corder_support :
  forall s W x,
    extends W (global s)
    -> (forall x, decidable (member W x))
    -> nonempty W
    -> (forall i, finite (ufwitness s W i))
    -> member (global s) x
    -> honest (creator x)
    -> exists j,
         (exists y, member W y /\ round j y)
         -> corder s W x x.
Proof.
intros s W x Hextends Hdec Hne Hfinf Hsx Hhonest.
so (received_defined _ _ Hsx Hhonest) as (i & Hrec).
so (received_support _#4 Hextends Hdec Hne Hrec) as (j & Hj).
exists j.
intro Hinh.
so (Hj Hinh) as Hrec'.
so (received_impl_time_received _#4 Hrec' (Hfinf i)) as (t & Htr).
exists i, i, t, t.
do2 4 split; auto.
right; right.
do2 2 split; auto.
apply (ord_refl _ _ textorder_order).
Qed.


Corollary corder_support_finite :
  forall s W x,
    extends W (global s)
    -> finite (member W)
    -> nonempty W
    -> member (global s) x
    -> honest (creator x)
    -> exists j,
         (exists y, member W y /\ round j y)
         -> corder s W x x.
Proof.
intros s W x Hextends Hfin Hne Hsx Hhonest.
apply corder_support; auto.
  {
  intro y.
  apply finite_decide; auto.
  exact eq_event_decide.
  }

  {
  apply ufwitness_finite_finite; auto.
  }
Qed.
