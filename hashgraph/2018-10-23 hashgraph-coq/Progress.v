(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Nat.
Require Import Omega.
Require Import List.

Require Import Tact.
Require Import Decide.
Require Import Cardinality.
Require Import Calculate.
Require Import Majority.
Require Import Relation.
Require Import HashgraphFacts.
Require Import Sees.
Require Import Round.


Lemma honest_event_exists :
  forall s, exists x, member (global s) x /\ honest (creator x).
Proof.
intros s.
so distinct_honest_peers as (a & b & Ha & Hb & Hneq).
so (honest_peers_sync s 0 a b Ha Hb Hneq) as (i & _ & _ & _ & Hcr & _).
exists (spawn s i).
split.
  {
  exists i, i.
  auto.
  }

  {
  subst a.
  exact Ha.
  }
Qed.


Lemma realtime_impl_self_ancestor :
  forall s x y,
    honest (creator x)
    -> creator x = creator y
    -> realtime s x y
    -> x $= y.
Proof.
intros s x y Hhonest Heqcr Hxy.
so (self_ancestor_decide x y) as [? | Hnxy]; auto.
exfalso.
so (self_ancestor_decide y x) as [Hyx | Hnyx].
  {
  so (ancestor_realtime _#3 (realtime_member _#3 Hxy andel) (self_ancestor_impl_ancestor _ _ Hyx)) as Hyx'.
  so (realtime_antisym _ _ _ Hxy Hyx').
  subst y.
  destruct Hnxy.
  apply star_refl.
  }

  {
  destruct Hxy as (i & j & -> & -> & Hij).
  apply (spawn_forks s i j); auto.
  unfold fork; auto.
  }
Qed.


Lemma event_transmit :
  forall s x a,
    member (global s) x
    -> honest (creator x)
    -> honest a
    -> exists y,
         member (global s) y
         /\ creator y = a
         /\ x @= y.
Proof.
intros s x a Hsx Hcrx Ha.
so (eq_peer_decide (creator x) a) as [Heq | Hneq].
  {
  subst a.
  exists x.
  do2 2 split; auto.
  apply star_refl.
  }
destruct Hsx as (i & _ & -> & _).
so (honest_peers_sync s i _ _ Hcrx Ha Hneq) as (j & k & Hij & Hjk & Heqij & Heqka & Hparent).
symmetry in Heqij.
assert (realtime s (spawn s i) (spawn s j)) as Hxy.
  {
  exists i, j; auto.
  }
so (realtime_impl_self_ancestor _#3 Hcrx Heqij Hxy) as Hxy'.
exists (spawn s k).
do2 2 split; auto.
  {
  exists k, k; auto.
  }

  {
  apply (star_trans _#3 (spawn s j)).
    {
    apply self_ancestor_impl_ancestor; auto.
    }

    {
    apply plus_star; auto.
    }
  }
Qed.


Lemma event_broadcast :
  forall s x,
    member (global s) x
    -> honest (creator x)
    -> exists y,
         member (global s) y
         /\ honest (creator y)
         /\ forall a,
              honest a
              -> exists w,
                   creator w = a
                   /\ x @= w
                   /\ w @= y.
Proof.
intro s.
cut (forall x l,
       member (global s) x
       -> honest (creator x)
       -> Forall honest l
       -> exists y,
            member (global s) y
            /\ honest (creator y)
            /\ x @= y
            /\ forall a,
                 In a l
                 -> exists w,
                      creator w = a
                      /\ x @= w
                      /\ w @= y).
  {
  intros Hprop x Hx Hhonest.
  destruct supermajority_honest as (_ & _ & _ & (l & _ & Hl & _) & _).
  exploit (Hprop x l) as H; auto.
    {
    apply Forall_forall.
    intros a Ha.
    apply Hl; auto.
    }
  destruct H as (y & Hy & Hhonest' & _ & Hall).
  exists y.
  do2 2 split; auto.
  intros a Ha.
  apply Hall.
  apply Hl; auto.
  }
intros x l Hx Hhonest Hl.
revert x Hx Hhonest.
induct Hl.

(** nil *)
{
intros x Hx Hhonest.
exists x.
do2 3 split; auto.
  {
  apply star_refl.
  }

  {
  intros a H.
  destruct H.
  }
}

(** cons *)
{
intros a l Ha _ IH x Hx Hhonest.
so (event_transmit _#3 Hx Hhonest Ha) as (y & Hy & <- & Hxy).
so (IH y Hy Ha) as (z & Hz & Hhonest' & Hyz & Hall).
exists z.
do2 3 split; auto.
  {
  eapply star_trans; eauto.
  }
intros b Hb.
destruct Hb as [Heq | Hb].
  {
  subst b.
  exists y.
  auto.
  }

  {
  so (Hall b Hb) as (w & Heqcr & Hyw & Hwz).
  exists w.
  do2 2 split; auto.
  eapply star_trans; eauto.
  }
}
Qed.


Lemma round_advanced :
  forall x y i j,
    round i x
    -> round j y
    -> supermajority
         stake
         (fun a => 
            exists w, 
              creator w = a
              /\ x @= w
              /\ stsees w y)
         every
    -> i < j.
Proof.
intros x y i j Hroundx Hroundy Hmaj.
assert (x @ y) as Hxy.
  {
  so (supermajority_inhabitant _#4 Hmaj) as (a & Ha).
  destruct Ha as (w & _ & Hxw & Hwy).
  eapply star_plus_trans; eauto.
  apply stsees_impl_strict_ancestor; auto.
  }
so (lt_dec i j) as [| Hnij]; auto.
assert (i = j) as Hij.
  {
  so (round_mono _#4 (plus_star _#4 Hxy) Hroundx Hroundy).
  omega.
  }
clear Hnij.
assert (exists u v, parents u v y /\ (x @= u \/ x @= v)) as (u & v & Hparents & Hxuv).
  {
  so (plus_plusr _#4 Hxy) as (u & Hxu & Huy).
  invert Huy; intros; eauto.
  }
so (round_defined u) as (k1 & Hroundu).
so (round_defined v) as (k2 & Hroundv).
assert (max k1 k2 <= j) as Hkj.
  {
  apply Nat.max_lub.
    {
    eapply round_mono; eauto.
    apply star_one.
    eapply parent1; eauto.
    }

    {
    eapply round_mono; eauto.
    apply star_one.
    eapply parent2; eauto.
    }
  }
assert (i <= max k1 k2) as Hik.
  {
  destruct Hxuv as [Hxu | Hxv].
    {
    so (round_mono _#4 Hxu Hroundx Hroundu).
    so (Nat.le_max_l k1 k2).
    omega.
    }

    {
    so (round_mono _#4 Hxv Hroundx Hroundv).
    so (Nat.le_max_r k1 k2).
    omega.
    }
  }
cut (round (S (max k1 k2)) y).
  {
  intros Hroundy'.
  so (round_fun _#3 Hroundy Hroundy').
  omega.
  }
eapply round_advance; eauto.
intros a Ha.
destruct Ha as (w & Hcrw & Hxw & Hwy).
exists w.
do2 2 split; auto.
so (round_defined w) as (l & Hroundw).
force_exact Hroundw.
f_equal.
so (round_mono _#4 Hxw Hroundx Hroundw).
so (round_mono _#4 (plus_star _#4 (stsees_impl_strict_ancestor _ _ Hwy)) Hroundw Hroundy).
omega.
Qed.


Lemma global_nonterminating :
  forall s, nonterminating (global s).
Proof.
intro s.
intro i.
cut (exists j x, i <= j /\ round j x /\ member (global s) x /\ honest (creator x)).
  {
  intros (j & x & Hij & Hround & Hx & _).
  eauto.
  }
induct i.

(** 0 *)
  {
so (honest_event_exists s) as (x & Hx & Hhonest).
so (round_defined x) as (j & Hround).
exists j, x.
do2 3 split; auto.
omega.
}

(** S *)
{
intros i IH.
destruct IH as (j & x & Hij & Hroundx & Hx & Hhonestx).
so (event_broadcast _ _ Hx Hhonestx) as (y & Hy & Hhonesty & Hally).
so (event_broadcast _ _ Hy Hhonesty) as (z & Hz & Hhonestz & Hallz).
assert (forall a,
          honest a
          -> exists w,
               creator w = a
               /\ x @= w
               /\ stsees w z) as Hadvance.
  {
  intros a Ha.
  so (Hally _ Ha) as (w & Hhonestw & Hxw & Hwy).
  exists w.
  do2 2 split; auto.
  exists z.
  split.
    { apply star_refl. }
  apply (supermajority_enlarge _ stake honest).
    {
    intros b Hb.
    so (Hallz b Hb) as (v & Hcrv & Hwv & Hvz).
    exists v.
    do2 2 split; auto.
      {
      subst a.
      apply ancestor_sees; auto.
      eapply star_trans; eauto.
      }

      {
      subst b.
      apply ancestor_sees; auto.
      }
    }

    { unfold incl, every; auto. }
    
    {
    intros b _.
    apply (dec_exists_finite _ _ (fun u => u @= z)).
      {
      intros u (_ & _ & H).
      apply sees_impl_ancestor; auto.
      }
      
      {
      apply ancestor_finite.
      }

      {
      intros u.
      apply dec_and; [| apply dec_and]; auto using eq_peer_decide, sees_decide.
      }
    }

    { exact supermajority_honest. }
  }
so (round_defined z) as (k & Hroundz).
exists k, z.
do2 3 split; auto.
exploit (round_advanced x z j k); auto.
  2:{ omega. }
apply (supermajority_enlarge _ stake honest); auto.
  {
  intros a _.
  apply (dec_exists_finite _ _ (fun u => u @ z)).
    {
    intros u (_ & _ & H).
    apply stsees_impl_strict_ancestor; auto.
    }

    {
    apply strict_ancestor_finite.
    }

    {
    intros u.
    apply dec_and; [| apply dec_and]; auto using eq_peer_decide, ancestor_decide, stsees_decide.
    }
  }

  { exact supermajority_honest. }
}
Qed.


Lemma events_are_received :
  forall s x,
    member (global s) x
    -> honest (creator x)
    -> exists i,
         forall y,
           member (global s) y
           -> rwitness i y
           -> x @= y.
Proof.
intros s x Hsx Hhonestx.
so (event_broadcast _ _ Hsx Hhonestx) as (y & Hsy & Hhonesty & Hally).
so (round_defined y) as (i & Hroundy).
assert (forall w, member (global s) w -> honest (creator w) -> rwitness (S i) w -> x @= w) as Hallsi.
  {
  intros w Hsw Hhonestw Hwitw.
  so (Hally _ Hhonestw) as (v & Hcrv & Hxv & Hvy).
  so (world_closed _#3 Hvy Hsy) as Hsv.
  rewrite <- Hcrv in Hhonestw.
  so (self_ancestor_total _ _ _ Hsv Hsw Hhonestw Hcrv) as [Hvw | Hwv].
    {
    eapply star_trans; eauto.
    apply self_ancestor_impl_ancestor; auto.
    }
  so (round_mono _#4 (star_trans _#5 (self_ancestor_impl_ancestor _ _ Hwv) Hvy) (Hwitw andel) Hroundy).
  omega.
  }
exists (2 + i).
intros z Hsz Hwitz.
cbn in Hwitz.
so (stsees_many_witnesses _ _ (Hwitz andel)) as Hmaj.
so (majority_intersect _#5 eq_peer_decide (supermajority_impl_majority _#4 Hmaj) (supermajority_impl_majority _#4 supermajority_honest)) as (a & Ha & Hhonesta).
destruct Ha as (w & <- & Hwz & Hwitw).
so (world_closed _#3 (stsees_impl_ancestor _ _ Hwz) Hsz) as Hsw.
so (Hallsi _ Hsw Hhonesta Hwitw) as Hxw.
eapply star_trans; eauto.
apply plus_star.
apply stsees_impl_strict_ancestor; auto.
Qed.


Lemma events_reach_every_world :
  forall s W x,
    extends W (global s)
    -> nonterminating W
    -> member (global s) x
    -> honest (creator x)
    -> member W x.
Proof.
intros s W x HsW Hnonterm Hsx Hhonest.
so (events_are_received _ _ Hsx Hhonest) as (i & Hall).
so (all_rounds_inhabited _ (S i) Hnonterm) as (y & Hwity & Wy).
so (stsees_many_witnesses _ _ (Hwity andel)) as Hmaj.
so (majority_inhabitant _#4 (supermajority_impl_majority _#4 Hmaj)) as (a & w & _ & Hwy & Hwitw).
so (stsees_impl_ancestor _ _ Hwy) as Hwy'.
eapply world_closed; eauto.
eapply star_trans; eauto.
apply Hall; auto.
apply HsW.
eapply world_closed; eauto.
Qed.
