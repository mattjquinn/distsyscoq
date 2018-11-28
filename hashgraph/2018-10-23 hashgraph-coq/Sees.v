(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Decide.

Require Import Tact.
Require Import Relation.
Require Import Majority.
Require Import HashgraphFacts.


(** y sees x *)
Definition sees (x y : event) : Prop :=
  x @= y
  /\ ~ exists z z', z @= y /\ z' @= y /\ fork z z' /\ creator z = creator x.


(** y strongly sees x *)
Definition stsees (x y : event) : Prop :=
  exists w,
    w @= y
    /\ supermajority
         stake
         (fun a => exists z, creator z = a /\ sees x z /\ sees z w)
         every.


Lemma sees_impl_ancestor :
  forall x y, sees x y -> x @= y.
Proof.
intros x y Hsee.
destruct Hsee; auto.
Qed.


(** Lemma 5.12 *)
Lemma strongly_seeing :
  forall W x y v w,
    member W v
    -> member W w
    -> fork x y
    -> stsees x v
    -> stsees y w
    -> False.
Proof.
intros W x y v w Wv Ww Hfork Hssx Hssy.
destruct Hssx as (v' & Hv & Hmajx).
destruct Hssy as (w' & Hw & Hmajy).
so (supermajority_intersect_3 _#6 eq_peer_decide supermajority_honest Hmajx Hmajy) as (a & Hhonest & Hseesx & Hseesy).
destruct Hseesx as (q & Hcrq & Hxq & Hqv').
destruct Hseesy as (r & Hcrr & Hyr & Hqw').
assert (q @= r \/ r @= q) as Hordered.
  {
  so (ancestor_decide q r) as [? | Hnqr]; auto.
  so (ancestor_decide r q) as [? | Hnrq]; auto.
  exfalso.
  so (world_forks W _ Hhonest) as H.
  destruct H.
  exists q, r.
  do2 3 split; auto.
    {
    apply (world_closed _ _ v); auto.
    eapply star_trans; eauto.
    apply sees_impl_ancestor; auto.
    }
    
    {
    apply (world_closed _ _ w); auto.
    eapply star_trans; eauto.
    apply sees_impl_ancestor; auto.
    }

    {
    do2 2 split.
      {
      subst a; auto.
      }
  
      {
      contradict Hnqr.
      apply self_ancestor_impl_ancestor; auto.
      }
  
      {
      contradict Hnrq.
      apply self_ancestor_impl_ancestor; auto.
      }
    }
  }
cut (forall x y q r,
       fork x y
       -> sees x q
       -> sees y r
       -> q @= r
       -> False).
  {
  intros H.
  destruct Hordered; [eapply (H x) | eapply (H y)]; eauto using fork_symm.
  }
repeat (match goal with H : _ |- _ => clear H end).
intros x y q r Hfork Hxq Hyr Hqr.
destruct Hyr as (Hyr & Hnofork).
destruct Hnofork.
exists x, y.
do2 3 split; auto using fork_creator.
destruct Hxq as (Hxq & _).
eapply star_trans; eauto.
Qed.


Lemma stsees_impl_strict_ancestor :
  forall x y, stsees x y -> x @ y.
Proof.
intros x y Hss.
destruct Hss as (w & Hwy & Hmaj).
so (distinct_peer _ (creator w) (supermajority_impl_majority _ _ _ _ Hmaj)) as (b & Hb & Hneq).
destruct Hb as (z & <- & Hxz & Hzw).
eapply plus_star_trans; eauto.
apply star_neq_plus.
  {
  eapply star_trans; apply sees_impl_ancestor; eauto.
  }
intro.
subst w.
apply (well_founded_impl_irrefl _ _ strict_ancestor_well_founded x).
apply (plus_trans _#3 z).
  {
  apply star_neq_plus.
    { apply sees_impl_ancestor; auto. }

    {
    contradict Hneq.
    f_equal; auto.
    }
  }

  {
  apply star_neq_plus.
    { apply sees_impl_ancestor; auto. }

    {
    contradict Hneq.
    f_equal; auto.
    }
  }
Qed.


Lemma stsees_impl_ancestor :
  forall x y, stsees x y -> x @= y.
Proof.
intros x y H.
apply plus_star.
apply stsees_impl_strict_ancestor; auto.
Qed.


Lemma sees_decide :
  forall x y,
    decidable (sees x y).
Proof.
intros x y.
apply dec_and.
  { apply ancestor_decide. }
apply dec_not.
apply (dec_exists_finite _ _ (fun z => z @= y)).
  2:{ apply ancestor_finite. }

  {
  intros z Hz.
  destruct_all Hz; auto.
  }
intro z.
apply (dec_exists_finite _ _ (fun z' => z' @= y)).
  2:{ apply ancestor_finite. }

  {
  intros z' Hz'.
  destruct_all Hz'; auto.
  }
intro z'.
apply dec_and.
  { apply ancestor_decide. }
apply dec_and.
  { apply ancestor_decide. }
apply dec_and.
  { apply fork_decide. }
apply eq_peer_decide.
Qed.


Lemma stsees_decide :
  forall x y,
    decidable (stsees x y).
Proof.
intros x y.
apply (dec_exists_finite _ _ (fun z => z @= y)).
  {
  intros z (H & _).
  auto.
  }

  { apply ancestor_finite. }
intro w.
apply dec_and.
  {
  apply ancestor_decide.
  }
eapply supermajority_decide.
  {
  intro a.
  apply (dec_exists_finite _ _ (fun z => z @= w)).
    {
    intros z (_ & _ & H).
    apply sees_impl_ancestor; auto.
    }
  
    { apply ancestor_finite. }
  intro z.
  apply dec_and.
    { apply eq_peer_decide. }
  apply dec_and; apply sees_decide.
  }

  { unfold incl, every; auto. }

  { exact the_total_stake. }
Qed.


Lemma self_ancestor_sees_trans :
  forall x y z,
    x $= y
    -> sees y z
    -> sees x z.
Proof.
intros x y z Hxy Hsees.
destruct Hsees as (Hyz & Hnofork).
split.
  {
  eapply star_trans; eauto.
  apply self_ancestor_impl_ancestor; auto.
  }
contradict Hnofork.
destruct Hnofork as (u & w & Huz & Hwz & Hfork & Heqcr).
exists u, w.
do2 3 split; auto.
transitivity (creator x); auto.
apply self_ancestor_creator; auto.
Qed.


Lemma self_ancestor_stsees_trans :
  forall x y z,
    x $= y
    -> stsees y z
    -> stsees x z.
Proof.
intros x y z Hxy Hss.
destruct Hss as (w & Hwz & Hmaj).
exists w.
split; auto.
eapply supermajority_enlarge; eauto.
  {
  intros a (u & Heqcr & Hyu & Huw).
  exists u.
  do2 2 split; auto.
  eapply self_ancestor_sees_trans; eauto.
  }

  {
  intros a _.
  apply (dec_exists_finite _ _ (fun u => u @= w)).
    {
    intros u (_ & _ & Hu).
    apply sees_impl_ancestor; auto.
    }

    {
    apply ancestor_finite.
    }

    {
    intros u.
    apply dec_and.
      { apply eq_peer_decide. }
    apply dec_and; apply sees_decide.
    }
  }
Qed.


Lemma stsees_ancestor_trans :
  forall x y z,
    stsees x y
    -> y @= z
    -> stsees x z.
Proof.
intros x y z Hss Hyz.
destruct Hss as (w & Hss & Hwy).
exists w.
split; auto.
eapply star_trans; eauto.
Qed.


Lemma ancestor_sees :
  forall x y,
    honest (creator x)
    -> x @= y
    -> sees x y.
Proof.
intros x y Hhonest Hxy.
split; auto.
intros (z & z' & Hzy & Hz'y & Hfork & Heqcr).
rewrite <- Heqcr in Hhonest.
so (event_world y) as (W & Wy).
destruct (world_forks W _ Hhonest).
exists z, z'.
do2 3 split; auto.
  {
  eapply world_closed; eauto.
  }

  {
  eapply world_closed; eauto.
  }
Qed.
