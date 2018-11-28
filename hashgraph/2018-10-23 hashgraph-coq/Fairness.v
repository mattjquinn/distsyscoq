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
Require Import Majority.
Require Import Cardinality.
Require Import HashgraphFacts.
Require Import Sees.
Require Import Round.
Require Import Progress.
Require Import Vote.
Require Import Decision.
Require Import Consensus.
Require Import Famous.


Lemma stsees_impl_famous_pre :
  forall s i x y,
    member (global s) y
    -> rwitness i x
    -> (forall j z, parent z y -> round j z -> j <= i)
    -> stsees x y
    -> exists z,
         member (global s) z 
         /\ decision s x z true
         /\ rwitness (S first_regular + i) z.
Proof.
intros s i x y Hsy Hwitx Hparentround Hxy.
so first_regular_min as Hd2.
so (all_rounds_inhabited _ (S first_regular + i) (global_nonterminating s)) as (z & Hwitz & Hsz).
exists z.
do2 2 split; auto.
apply (unanimity_impl_decision s (global s) x z i (first_regular + i) true); auto.
  {
  exact (Hwitx andel).
  }

2:{
  omega.
  }

2:{
  replace (S (first_regular + i) - i) with (S first_regular) by omega.
  so coin_freq_min.
  rewrite -> Nat.mod_small; omega.
  }
clear z Hwitz Hsz.
intros w Hsw Hwitw.
eapply vote_first; eauto; try omega.
split.
2:{
  intros _.
  exact I.
  }
intros _.
(** The heart of the proof starts here. *)
destruct Hxy as (y' & Hyy & Hmaj1).
exploit (stsees_many_witnesses (pred (first_regular + i)) w) as Hmaj2.
  {
  force_exact (Hwitw andel).
  f_equal.
  omega.
  }
so (supermajority_intersect_3 _#6 eq_peer_decide supermajority_honest Hmaj1 Hmaj2) as (a & Hhonest & Ha1 & Ha2).
destruct Ha1 as (u & Heqcru & Hxu & Huy).
destruct Ha2 as (v & Heqcrv & Hvw & Hwitv).
apply (star_plus_trans _#3 u).
  {
  apply sees_impl_ancestor; auto.
  }
apply (star_plus_trans _#3 v).
2:{
  apply stsees_impl_strict_ancestor; auto.
  }
apply self_ancestor_impl_ancestor.
destruct (eq_event_decide v u) as [Heq | Hneqvu].
  {
  subst v.
  apply star_refl.
  }
rewrite <- Heqcru in Hhonest.
rewrite <- Heqcrv in Heqcru.
exploit (self_ancestor_total (global s) u v) as H; auto.
  {
  apply (world_closed _ _ y); auto.
  eapply star_trans; eauto.
  apply sees_impl_ancestor; auto.
  }

  {
  apply (world_closed _ _ w); auto.
  apply stsees_impl_ancestor; auto.
  }
destruct H as [| Hvu]; auto.
exfalso.
so (eq_event_decide u y) as [Heq | Hnequy].
  {
  subst u.
  so (plus_plusr _#4 (star_neq_plus _#4 Hvu Hneqvu)) as (z & Hvz & Hzy).
  so (round_defined z) as (j & Hroundz).
  so (Hparentround _ _ (self_parent_impl_parent _ _ Hzy) Hroundz) as Hji.
  so (round_mono _#4 (self_ancestor_impl_ancestor _ _ Hvz) (Hwitv andel) Hroundz).
  omega.
  }

  {
  so (plus_plusr _#4 (star_neq_plus _#4 (star_trans _#5 (sees_impl_ancestor _ _ Huy) Hyy) Hnequy)) as (z & Huz & Hzy).
  so (round_defined z) as (j & Hroundz).
  so (Hparentround _ _ Hzy Hroundz) as Hji.
  so (round_mono _#4 (star_trans _#5 (self_ancestor_impl_ancestor _ _ Hvu) Huz) (Hwitv andel) Hroundz).
  omega.
  }
Qed.


Lemma stsees_impl_famous :
  forall s i x y,
    member (global s) y
    -> rwitness i x
    -> (forall j z, parent z y -> round j z -> j <= i)
    -> stsees x y
    -> famous s (global s) x.
Proof.
intros s i x y Hsy Hwitx Hparentround Hxy.
so (stsees_impl_famous_pre _#4 Hsy Hwitx Hparentround Hxy) as (z & Hz & Hdecision & _).
exists z.
split; auto.
Qed.


Lemma fwitness_finite_nonterm_if :
  forall s W,
    extends W (global s)
    -> nonterminating W
    -> (forall x, member (global s) x -> decidable (member W x))
    -> forall i x, fwitness s W i x -> finite (fwitness s W i).
Proof.
intros s W HsW Hnonterm HdecW i x Hx.
destruct Hx as (Hwitx & Hfamousx).
destruct Hfamousx as (y & Wy & Hdecisionxy).
apply (finite_subset' _ _ (fun z => realtime s z y)).
  { exact eq_event_decide. }

  {
  intros w Hw.
  destruct Hw as (Hwitw & Hfamous).
  destruct Hfamous as (z & Wz & Hdecisionwz).
  apply ancestor_realtime.
    { exact (HsW _ Wy). }
  so (ancestor_decide w y) as [| Hnwy]; auto.
  exfalso.
  so (no_late_fame _#6 Hwitx Hwitw Hdecisionxy Hnwy) as Hdecisionwy.
  so (decision_consistent _#7 Wy Wz Hdecisionwy Hdecisionwz) as H.
  discriminate H.
  }

  {
  intros z Hzy.
  so (HdecW _ (realtime_member _#3 Hzy andel)) as [Wz | Wnz].
  2:{
    right.
    contradict Wnz.
    destruct Wnz as (_ & Hfamous).
    eapply famous_member; eauto.
    }
  apply dec_and_dep.
    {
    apply rwitness_decide.
    }

    {
    intros (_ & Hwitz).
    apply famous_decide_nonterm; auto.
    }
  }

  {
  so (HsW _ Wy) as (m & _ & -> & _).
  assert (exists l, forall n, In n l <-> n < S m) as (l & Hl).
    {
    clear Wy x Hwitx Hdecisionxy.
    generalize (S m).
    intro m'.
    clear m.
    induct m'.
      (* 0 *)
      {
      exists nil.
      intros n.
      split.
        {
        intro H; destruct H.
        }

        {
        intro H; omega.
        }
      }

      (* S *)
      {
      intros m (l & Hl).
      exists (cons m l).
      intros n.
      split.
        {
        intros H.
        destruct H as [H | H].
          {
          omega.
          }

          {
          so (Hl _ andel H).
          omega.
          }
        }
        
        {
        intro Hnm.
        so (eq_nat_dec m n) as [Heq | Hneq].
          {
          subst.
          left; auto.
          }

          {
          right.
          apply Hl.
          omega.
          }
        }
      }
    }
  exists (map (spawn s) l).
  intros z.
  split.
    {
    intro H.
    destruct H as (n & m' & -> & Heq & Hle).
    so (spawn_inj _#3 Heq); subst m'.
    apply in_map.
    apply Hl.
    omega.
    }

    {
    intro Hz.
    so (in_map_iff _#5 andel Hz) as (n & <- & Hin).
    exists n, m.
    do2 2 split; auto.
    so (Hl _ andel Hin).
    omega.
    }
  }
Qed.


Lemma fwitness_finite_global_if :
  forall s i x, fwitness s (global s) i x -> finite (fwitness s (global s) i).
Proof.
intros s i x Hx.
eapply fwitness_finite_nonterm_if; eauto.
  { unfold extends, incl; auto. }

  { apply global_nonterminating. }

  {
  intros y Hy.
  left; auto.
  }
Qed.    


Lemma minimal_witness :
  forall s i,
    exists x,
      member (global s) x
      /\ rwitness i x
      /\ forall j y, parent y x -> round j y -> j < i.
Proof.
intros s i.
so (all_rounds_inhabited _ i (global_nonterminating s)) as (y & Hwity & Hsy).
revert Hwity Hsy.
wfinduct y using strict_ancestor_well_founded.
intros y IH Hwity Hsy.
so (initial_decide y) as [Hinit | (u & v & Hparents)].
  {
  so (round_fun _#3 (Hwity andel) (round_initial Hinit)) as H.
  exists y.
  do2 2 split; auto.
  intros j z Hparent _.
  exfalso.
  eapply initial_no_parent; eauto.
  }
so (round_defined v) as (j & Hroundv).
so (lt_dec j i) as [Hle | Hnle].
  {
  exists y.
  do2 2 split; auto.
  intros k z Hzy Hroundz.
  invert Hzy.
    {
    intros ? Hparents'.
    so (parents_fun _#5 Hparents Hparents') as (<- & <-).
    so (strict_self_ancestor_witness _#4 (Hwity ander) (plus_one _#4 (ex_intro _ _ Hparents)) Hroundz (Hwity andel)).
    omega.
    }

    {
    intros ? Hparents'.
    so (parents_fun _#5 Hparents Hparents') as (<- & <-).
    so (round_fun _#3 Hroundv Hroundz); subst k.
    omega.
    }
  }

  {
  so (ancestor_witness _#3 (le_refl _) Hroundv) as (w & Hwv & Hwitw).
  assert (w @ y) as Hwy.
    {
    eapply star_plus_trans; eauto.
    apply plus_one.
    eapply parent2; eauto.
    }
  apply (IH w); auto.
    {
    force_exact Hwitw.
    f_equal.
    so (round_mono _#4 (plus_star _#4 Hwy) (Hwitw andel) (Hwity andel)).
    omega.
    }

    {
    apply (world_closed _ _ y); auto.
    apply plus_star; auto.
    }
  }
Qed.


Lemma minimal_witness' :
  forall s i,
    exists x,
      member (global s) x
      /\ rwitness (S i) x
      /\ forall j y, parent y x -> round j y -> j <= i.
Proof.
intros s i.
so (minimal_witness s (S i)) as (x & Hx & Hwitx & Hminimal).
exists x.
do2 2 split; auto.
intros j y Hyx Hroundy.
so (Hminimal _ _ Hyx Hroundy).
omega.
Qed.


Theorem fairness :
  forall s i,
    supermajority
      stake
      (fun a => exists w, creator w = a /\ fwitness s (global s) i w)
      every.
Proof.
intros s i.
so (minimal_witness' s i) as (y & Hsy & Hwity & Hparentround).
so (stsees_many_witnesses _ _ (Hwity andel)) as Hmaj.
assert (exists z, fwitness s (global s) i z) as (z & Hz).
  {
  so (supermajority_inhabitant _#4 Hmaj) as (a & Ha).
  destruct Ha as (x & <- & Hxy & Hwitx).
  exists x.
  split; auto.
  eapply stsees_impl_famous; eauto.
  }
eapply supermajority_enlarge; eauto.
  {
  intros a Ha.
  destruct Ha as (x & Heqcr & Hxy & Hwitx).
  exists x.
  split; auto.
  split; auto.
  eapply stsees_impl_famous; eauto.
  }

  {
  intros a _.
  apply (dec_exists_finite _ _ (fwitness s (global s) i)).
    {
    intros x (H1 & H2).
    auto.
    }

    {
    eapply fwitness_finite_global_if; eauto.
    }

    {
    intros x.
    apply dec_and.
      {
      apply eq_peer_decide.
      }

      {
      apply finite_decide.
        {
        exact eq_event_decide.
        }

        {
        eapply fwitness_finite_global_if; eauto.
        }
      }
    }
  }
Qed.


Lemma famous_witness_exists :
  forall s i,
    exists x,
      fwitness s (global s) i x.
Proof.
intros s i.
so (supermajority_inhabitant _#4 (fairness s i)) as (a & Ha).
destruct Ha as (x & _ & Hx).
exists x; auto.
Qed.
