(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Bool.
Require Import Nat.
Require Import List.
Require Import Omega.
Require Import Decide.

Require Import Tact.
Require Import Relation.
Require Import Weight.
Require Import Calculate.
Require Import Majority.
Require Export Hashgraph.


(** Peers *)

Lemma eq_peer_decide : forall (a b : peer), decidable (a = b).
Proof.
intros a b.
so (peer_eq_dec a b) as [Heq | Hneq]; [left | right]; auto.
Qed.  


Lemma arbitrary_peer : inhabited peer.
Proof.
destruct number_of_peers as (p & _ & _ & Hlen).
destruct p as [| x p].
  {
  cbn in Hlen.
  so number_peers_minimum.
  omega.
  }
exact (inhabits x).
Qed.


Lemma distinct_peer :
  forall (P : peer -> Prop) a,
    majority stake P every
    -> exists b, P b /\ a <> b.
Proof.
intros P a Hmaj.
destruct Hmaj as (m & n & _ & HcardP & Hcardn & Hgt).
destruct HcardP as (p & Hdistp & Hp & Hweightp).
destruct p as [| b p].
  {
  cbn in Hweightp.
  subst m.
  omega.
  }
so (eq_peer_decide a b) as [Heq | Hneq].
2:{
  exists b.
  split; auto.
  apply Hp.
  left; auto.
  }
subst b.
destruct p as [| c p].
  {
  exfalso.
  apply (no_majority_stake a).
  exists m, n.
  do2 3 split; auto.
  exists (cons a nil).
  do2 2 split; auto.
  intros d.
  split.
    {
    intros <-.
    left; auto.
    }

    {
    intro H.
    destruct H; auto.
    destruct H.
    }
  }
exists c.
split.
  {
  apply Hp.
  right; left; auto.
  }

  {
  intros <-.
  invert Hdistp.
  intros H _.
  destruct H.
  left; auto.
  }
Qed.


Lemma honest_decide :
  forall a, decidable (honest a).
Proof.
intro a.
apply finite_decide.
  {
  exact eq_peer_decide.
  }
destruct supermajority_honest as (m & _ & _ & Hcard & _).
eapply weight_finite; eauto.
Qed.


(** Events *)

Lemma eq_event_decide : forall (x y : event), decidable (x = y).
Proof.
intros x y.
so (event_eq_dec x y) as [Heq | Hneq]; [left | right]; auto.
Qed.  


(** Parents *)

Lemma initial_no_parent :
  forall x y, initial y -> parent x y -> False.
Proof.
intros x y Hinit Hparent.
invert Hparent.
  {
  intros z Hparents.
  destruct Hinit.
  exists x, z.
  auto.
  }

  {
  intros z Hparents.
  destruct Hinit.
  exists z, x.
  auto.
  }
Qed.


Lemma initial_no_self_parent :
  forall x y, initial y -> self_parent x y -> False.
Proof.
intros x y Hinit Hparent.
destruct Hparent as (z & Hparents).
destruct Hinit.
exists x, z.
auto.
Qed.


Lemma parents_self_parent :
  forall x y z,
    parents x y z -> self_parent x z.
Proof.
intros x y z H.
exists y; auto.
Qed.


Lemma parent_decide :
  forall x y, decidable (parent x y).
Proof.
intros x y.
so (initial_decide y) as [Hinit | (v & w & Hparents)].
  {
  right.
  intros H.
  eapply initial_no_parent; eauto.
  }
so (event_eq_dec x v) as [Heq | Hneqv].
  {
  subst x.
  left.
  eapply parent1; eauto.
  }
so (event_eq_dec x w) as [Heq | Hneqw].
  {
  subst x.
  left.
  eapply parent2; eauto.
  }
right.
intros Hparent.
invert Hparent.
  {
  intros z Hparents'.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).
  destruct Hneqv; auto.
  }

  {
  intros z Hparents'.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).
  destruct Hneqw; auto.
  }
Qed.


Lemma parent_finite :
  forall x, finite (fun y => parent y x).
Proof.
intros x.
so (initial_decide x) as [Hinit | (y & z & Hparents)].
  {
  exists nil.
  intros y.
  split.
    {
    intro H.
    eapply initial_no_parent; eauto.
    }
    
    {
    intro H.
    destruct H.
    }
  }
exists (cons y (cons z nil)).
intros w.
split.
  {
  intros Hwx.
  invert Hwx.
    {
    intros v Hparents'.
    so (parents_fun _#5 Hparents Hparents') as (<- & <-).
    left; auto.
    }
  
    {
    intros v Hparents'.
    so (parents_fun _#5 Hparents Hparents') as (<- & <-).
    right; left; auto.
    }
  }

  {
  intro H.
  destruct H as [Heq | [Heq | H]].
    {
    subst.
    eapply parent1; eauto.
    }

    {
    subst.
    eapply parent2; eauto.
    }

    {
    destruct H.
    }
  }
Qed.


Lemma self_parent_impl_parent :
  forall x y, self_parent x y -> parent x y.
Proof.
intros x y Hxy.
destruct Hxy as (z & H).
eapply parent1; eauto.
Qed.


Lemma self_parent_fun :
  forall x x' y,
    self_parent x y
    -> self_parent x' y
    -> x = x'.
Proof.
intros x x' y H H'.
destruct H as (z & H).
destruct H' as (z' & H').
so (parents_fun _#5 H H') as (<- & _).
reflexivity.
Qed.


Lemma self_parent_creator :
  forall x y, self_parent x y -> creator x = creator y.
Proof.
intros x y H.
destruct H as (z & H).
eapply parents_creator; eauto.
Qed.


Lemma self_parent_decide :
  forall x y, decidable (self_parent x y).
Proof.
intros x y.
so (initial_decide y) as [Hinit | (u & v & Hparents)].
  {
  right.
  intros (u & Hparents).
  apply Hinit; eauto.
  }

  {
  so (eq_event_decide x u) as [| Hneq].
    {
    subst u.
    left.
    exists v; auto.
    }

    {
    right.
    intros (w & Hparents').
    so (parents_fun _#5 Hparents Hparents') as (<- & _).
    destruct Hneq; auto.
    }
  }
Qed.


(** Paths *)

Lemma self_ancestor_impl_ancestor :
  forall x y, x $= y -> x @= y.
Proof.
intros x y H.
apply (star_mono _ self_parent); auto.
exact self_parent_impl_parent.
Qed.


Lemma strict_self_ancestor_impl_strict_ancestor :
  forall x y, x $ y -> x @ y.
Proof.
intros x y H.
apply (plus_mono _ self_parent); auto.
exact self_parent_impl_parent.
Qed.


Lemma self_parent_well_founded : well_founded self_parent.
Proof.
intros x.
wfinduct x using parent_well_founded.
intros x IH.
apply Acc_intro.
intros y Hyx.
apply IH.
apply self_parent_impl_parent; auto.
Qed.


Lemma strict_ancestor_well_founded : well_founded strict_ancestor.
Proof.
apply plus_well_founded.
apply parent_well_founded.
Qed.


Lemma strict_ancestor_parents :
  forall w x y z,
    parents x y z
    -> w @ z
    -> w @= x \/ w @= y.
Proof.
intros w x y z Hparents Hwz.
so (plus_plusr _#4 Hwz) as (v & Hwv & Hvz).
invert Hvz.
  {
  intros v' Hparents'.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).
  left; auto.
  }

  {
  intros v' Hparents'.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).
  right; auto.
  }
Qed.


Lemma strict_self_ancestor_parent :
  forall x y z,
    self_parent y z
    -> x $ z
    -> x $= y.
Proof.
intros x y z Hparent Hxz.
so (plus_plusr _#4 Hxz) as (v & Hxv & Hvz).
so (self_parent_fun _#3 Hparent Hvz); subst v.
exact Hxv.
Qed.


Lemma strict_ancestor_initial :
  forall x y, x @ y -> initial y -> False.
Proof.
intros x y Hxy Hinit.
destruct (plus_plusr _#4 Hxy) as (z & _ & Hzy).
eapply initial_no_parent; eauto.
Qed.


Lemma ancestor_initial :
  forall x y, x @= y -> initial y -> x = y.
Proof.
intros x y Hxy Hinit.
so (star_plus _#4 Hxy) as [Heq | Hxy']; auto.
exfalso.
eapply strict_ancestor_initial; eauto.
Qed.


Lemma self_ancestor_creator :
  forall x y, x $= y -> creator x = creator y.
Proof.
intros x y H.
induct H; auto.
(** step *)
{
intros x y z Hxy _ Heq.
transitivity (creator y); auto.
eapply self_parent_creator; eauto.
}
Qed.


Lemma strict_ancestor_irreflex :
  forall x, x @ x -> False.
Proof.
intros x Hxx.
eapply well_founded_impl_irrefl; eauto.
exact strict_ancestor_well_founded.
Qed.    


(** Path decisions *)

Lemma strict_ancestor_finite : forall x, finite (fun y => y @ x).
Proof.
intro x.
apply finite_plus.
  { exact parent_well_founded. }

  { exact parent_decide. }

  { exact parent_finite. }
Qed.


Lemma ancestor_finite : forall x, finite (fun y => y @= x).
Proof.
intro x.
apply finite_star.
  { exact parent_well_founded. }

  { exact parent_decide. }

  { exact parent_finite. }
Qed.


Lemma ancestor_decide :
  forall x y,
    decidable (x @= y).
Proof.
intros x y.
wfinduct y using parent_well_founded.
intros y IH.
so (event_eq_dec x y) as [Heq | Hneq].
  {
  subst y.
  left.
  apply star_refl.
  }
so (initial_decide y) as [Hinit | Hparents].
  {
  right.
  intros Hxy.
  so (star_plus _#4 Hxy) as [Heq | Hxy'].
    {
    subst y.
    destruct Hneq; auto.
    }
  so (plus_plusr _#4 Hxy') as (z & _ & Hzy).
  destruct Hinit.
  invert Hzy; eauto.
  }
destruct Hparents as (v & w & Hparents).
so (IH _ (parent1 Hparents)) as [Hvy | Hnvy].
  {
  left.
  eapply star_trans; eauto.
  apply star_one.
  eapply parent1; eauto.
  }
so (IH _ (parent2 Hparents)) as [Hwy | Hnwy].
  {
  left.
  eapply star_trans; eauto.
  apply star_one.
  eapply parent2; eauto.
  }
right.
intro Hxy.
so (star_plus _#4 Hxy) as [? | Hxy'].
  {
  subst y.
  destruct Hneq; auto.
  }
so (plus_plusr _#4 Hxy') as (u & Hxu & Huy).
invert Huy.
  {
  intros u' Hparents'.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).  
  destruct Hnvy; auto.
  }

  {
  intros u' Hparents'.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).  
  destruct Hnwy; auto.
  }
Qed.


Lemma strict_ancestor_decide :
  forall x y,
    decidable (x @ y).
Proof.
intros x y.
so (ancestor_decide x y) as [Hxy | Hnxy].
  {
  so (star_plus _#4 Hxy) as [Heq | Hxy'].
    {
    subst y.
    right.
    unfold not.
    apply well_founded_impl_irrefl.
    exact strict_ancestor_well_founded.
    }
  left; auto.
  }

  {
  right.
  contradict Hnxy.
  apply plus_star; auto.
  }
Qed.


Lemma self_ancestor_decide :
  forall x y,
    decidable (x $= y).
Proof.
intros x y.
wfinduct y using self_parent_well_founded.
intros y IH.
so (event_eq_dec x y) as [Heq | Hneq].
  {
  subst y.
  left.
  apply star_refl.
  }
so (initial_decide y) as [Hinit | Hparents].
  {
  right.
  intros Hxy.
  so (star_plus _#4 Hxy) as [Heq | Hxy'].
    {
    subst y.
    destruct Hneq; auto.
    }
  so (plus_plusr _#4 Hxy') as (z & _ & Hzy).
  destruct Hinit.
  invert Hzy; eauto.
  }
destruct Hparents as (v & w & Hparents).
so (IH v (ex_intro _ _ Hparents)) as [Hvy | Hnvy].
  {
  left.
  eapply star_trans; eauto.
  apply star_one.
  exists w; auto.
  }
right.
intro Hxy.
so (star_plus _#4 Hxy) as [? | Hxy'].
  {
  subst y.
  destruct Hneq; auto.
  }
so (plus_plusr _#4 Hxy') as (u & Hxu & Huy).
destruct Huy as (u' & Hparents').
so (parents_fun _#5 Hparents Hparents') as (<- & <-).  
destruct Hnvy; auto.
Qed.


Lemma self_ancestor_total :
  forall W x y, 
    member W x
    -> member W y
    -> honest (creator x)
    -> creator x = creator y
    -> x $= y \/ y $= x.
Proof.
intros W x y Wx Wy Hhonest Heqcr.
so (self_ancestor_decide x y) as [| Hnxy]; auto.
so (self_ancestor_decide y x) as [| Hnyx]; auto.
exfalso.
destruct (world_forks W _ Hhonest).
exists x, y.
do2 3 split; auto.
do2 2 split; auto.
Qed.


Lemma self_ancestor_total' :
  forall W x y, 
    member W x
    -> member W y
    -> honest (creator x)
    -> creator x = creator y
    -> x $= y \/ y $ x.
Proof.
intros W x y Wx Wy Hhonest Heqcr.
so (eq_event_decide x y) as [Heq | Hneq].
  {
  subst y.
  left.
  apply star_refl.
  }
so (self_ancestor_total _ _ _ Wx Wy Hhonest Heqcr) as [Hxy | Hyx]; auto.
right.
apply star_neq_plus; auto.
Qed.


(** Forks *)

Lemma fork_symm :
  forall x y, fork x y -> fork y x.
Proof.
intros x y H.
destruct H as (Heq & Hnxy & Hnyx).
do2 2 split; auto.
Qed.


Lemma fork_creator :
  forall x y, fork x y -> creator x = creator y.
Proof.
intros x y H.
destruct H; auto.
Qed.


Lemma fork_decide :
  forall x y, decidable (fork x y).
Proof.
intros x y.
apply dec_and.
  { apply eq_peer_decide. }
apply dec_and.
  {
  apply dec_not.
  apply self_ancestor_decide.
  }
apply dec_not.
apply self_ancestor_decide.
Qed.


(** Worlds *)

Definition realtime_before (s : sample) (x : event) : world.
Proof.
apply (mk_world (fun y => realtime s y x)).
  {
  intros z y Hzy Hyx.
  apply (realtime_trans _ _ y); auto.
  apply ancestor_realtime; auto.
  apply (realtime_member _ _ x); eauto.
  }

  {
  intros a Ha.
  intros (y & z & Hyx & Hzx & Hfork & Heqcr).
  subst a.
  destruct Hyx as (j & _ & -> & _).
  destruct Hzx as (k & _ & -> & _).
  apply (spawn_forks s j k); auto.
  }
Defined.
  

Lemma event_world : forall x, exists W, member W x.
Proof.
intros x.
so (no_orphans x) as (s & i & Hspawn).
exists (realtime_before s x).
subst x.
exists i, i.
auto.
Qed.


(** Textorder *)

Lemma textorder_decide :
  forall x y, decidable (Is_true (textorder x y)).
Proof.
intros x y.
apply Is_true_decide.
Qed.
