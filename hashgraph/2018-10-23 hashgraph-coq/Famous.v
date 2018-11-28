(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Nat.
Require Import Bool.
Require Import List.
Require Import Omega.

Require Import Tact.
Require Import Relation.
Require Import Decide.
Require Import Weight.
Require Import Calculate.
Require Import Majority.
Require Import HashgraphFacts.
Require Import Sees.
Require Import Round.
Require Import Vote.
Require Import Decision.
Require Import Consensus.


Definition famous (s : sample) (W : world) (x : event) : Prop :=
  exists y, member W y /\ decision s x y true.


Definition fwitness s W i x :=
  rwitness i x
  /\ famous s W x.


Lemma extends_famous :
   forall s W W' x,
     extends W W'
     -> famous s W x
     -> famous s W' x.
Proof.
intros s W W' x Hextends Hfamous.
destruct Hfamous as (y & Wy & Hdecision).
exists y.
split; auto.
Qed.


Lemma fame_reaches_every_world :
  forall s W W' x,
    extends W W'
    -> nonterminating W
    -> famous s W' x
    -> famous s W x.
Proof.
intros s W W' x Hw Hnonterm Hfamous.
destruct Hfamous as (y & Hsy & Hdecision).
so Hdecision as (i & j & _ & _ & Hwitx & Hwity & Hij & _).
assert (exists k, j < k /\ (k - i) mod coin_freq <> 0) as (k & Hjk & Hnocoin).
  {
  so (eq_nat_dec ((S j - i) mod coin_freq) 0) as [Heq | Hneq].
    {
    exists (2 + j).
    split; try omega.
    replace (2 + j - i) with (S (S j - i)) by omega.
    apply succ_no_coin; auto.
    }

    {
    exists (S j).
    auto.
    }
  }
so (all_rounds_inhabited _ k Hnonterm) as (z & Hwitz & Wz).
exploit (decisions_propagate _#7 Hsy (Hwitx andel) (Hwity andel) Hdecision k z) as Hdecision'; auto.
exists z.
auto.
Qed.


Lemma famous_decide_finite :
  forall s W x,
    finite (member W)
    -> decidable (famous s W x).
Proof.
intros s W x Hfin.
apply (dec_exists_finite _ _ (member W)); auto.
  {
  intros y Hy.
  destruct Hy; auto.
  }
intros y.
apply dec_and.
  {
  apply finite_decide; auto.
  exact eq_event_decide.
  }

  {
  apply decision_decide.
  }
Qed.


Lemma famous_decide_nonterm :
  forall s W x,
    extends W (global s)
    -> nonterminating W
    -> member W x
    -> witness x
    -> decidable (famous s W x).
Proof.
intros s W x HsW Hnonterm Wx Hwitx.
so (fame_consensus _ _ (HsW _ Wx) Hwitx) as (y & b & Hsy & Hdecision).
destruct b.
  {
  left.
  apply (fame_reaches_every_world _#4 HsW Hnonterm).
  exists y.
  auto.
  }

  {
  right.
  intros (z & Wz & Hdecision').
  so (decision_consistent _#7 Hsy (HsW _ Wz) Hdecision Hdecision') as H.
  discriminate H.
  }
Qed.


Lemma elector_cardinality :
  forall i y,
    exists n, weight creatorstake (fun x => elector i x y) n. 
Proof.
intros i y.
apply finite_weight.
  { exact eq_event_decide. }

  {
  apply (finite_subset _ _ (fun w => w @ y)).
    {
    intros x (_ & Hx).
    apply stsees_impl_strict_ancestor; auto.
    }
    
    {
    intros x.
    apply dec_and.
      { apply rwitness_decide. }

      { apply stsees_decide. }
    }

    {
    apply strict_ancestor_finite.
    }
  }
Qed.


Lemma no_true_votes_election :
  forall s i x y t f,
    (forall z, z @ y -> ~ vote s x z true)
    -> election (vote s x) i y t f
    -> t = 0.
Proof.
intros s i x y t f Hno Helection.
assert (weight creatorstake (fun z => elector i z y /\ vote s x z true) 0) as Hshutout.
  {
  apply weight_empty'.
  intros z (Helector & Hvote).
  apply (Hno z); auto.
  apply stsees_impl_strict_ancestor.
  exact (Helector ander).
  }
so (destruct_election _#6 Helection) as (_ & Ht & _).
eapply weight_fun; eauto.
Qed.


Lemma unknown_event_vote :
  forall s x y,
    ~ x @= y
    -> ~ vote s x y true.
Proof.
intros s x y Hnxy.
intro Hvote.
remember true as b eqn:Heqb.
cut (b = false).
  {
  intros ->.
  discriminate Heqb.
  }
clear Heqb.
revert b Hvote Hnxy.
wfinduct y using strict_ancestor_well_founded.
intros y IH b Hvote.
revert IH.
cases Hvote.

(** first *)
{
intros _ x y m n v _ _ _ _ Hv _ Hnxy.
destruct v; auto.
destruct Hnxy.
apply plus_star.
apply Hv.
exact I.
}

(** regular *)
{
intros s x y m n t f v Hwitx Hwity Hlt Hnocoin Helection Htally IH Hnxy.
destruct Htally as [(Htf & _) | (_ & ?)]; auto.
exploit (no_true_votes_election s (pred n) x y t f); auto.
  {
  intros z Hzy Hvote.
  cut (true = false).
    { intro H; discriminate H. }
  eapply IH; eauto.
  contradict Hnxy.
  eapply star_trans; eauto.
  apply plus_star; auto.
  }
subst t.
so (destruct_election _#6 Helection) as (Hcard & _ & _).
cbn in Hcard.
eassert _ as H; [refine (elector_minimum _#3 _ Hcard) |].
  {
  replace (S (pred n)) with n by omega.
  exact (Hwity andel).
  }
omega.
}

(** coin_super *)
{
intros s x y m n t f v Hwitx Hwity Hlt Hcoin Helection Htally IH Hnxy.
destruct v; auto.
exploit (no_true_votes_election s (pred n) x y t f); auto.
  {
  intros z Hzy Hvote.
  cut (true = false).
    { intro H; discriminate H. }
  eapply IH; eauto.
  contradict Hnxy.
  eapply star_trans; eauto.
  apply plus_star; auto.
  }
omega.
}

(** coin *)
{
intros s x y m n t f Hwitx Hwity Hlt Hcoin Helection _ Hf IH Hnxy.
exploit (no_true_votes_election s (pred n) x y t f); auto.
  {
  intros z Hzy Hvote.
  cut (true = false).
    { intro H; discriminate H. }
  eapply IH; eauto.
  contradict Hnxy.
  eapply star_trans; eauto.
  apply plus_star; auto.
  }
subst t.
so (destruct_election _#6 Helection) as (Hcard & _ & _).
cbn in Hcard.
eassert _ as H; [refine (elector_minimum _#3 _ Hcard) |].
  {
  replace (S (pred n)) with n by omega.
  exact (Hwity andel).
  }
omega.
}
Qed.


Lemma no_late_fame :
  forall s i x y w b,
    rwitness i x
    -> rwitness i y
    -> decision s x w b
    -> ~ y @= w
    -> decision s y w false.
Proof.
intros s i x y w b Hwitx Hwity Hdecision Hnyw.
destruct Hdecision as (i' & j & t' & f' & Hwitx' & Hwitw & Hlt & Hnocoin & Helection' & Htally).
so (rwitness_fun _#3 Hwitx Hwitx'); subst i'.
exploit (election_defined' s y i (pred j) w) as H; auto.
  { 
  so first_regular_min.
  omega.
  }
destruct H as (t & f & Helection).
so (destruct_election _#6 Helection) as (Htf & Ht & _).
assert (t = 0).
  {
  eapply no_true_votes_election; eauto.
  intros v Hvw.
  apply unknown_event_vote.
  contradict Hnyw.
  eapply star_trans; eauto.
  apply plus_star; auto.
  }
subst t.
exists i, j, 0, f.
do2 5 split; auto.
so (destruct_election _#6 Helection') as (Htf' & _).
cbn in Htf.
so (weight_fun _#5 Htf Htf'); subst f.
destruct b; omega.
Qed.


(** Lemma 5.18 *)
Corollary no_late_fame_world :
  forall s W i x y w b,
    member W w
    -> ~ member W y
    -> rwitness i x
    -> rwitness i y
    -> decision s x w b
    -> decision s y w false.
Proof.
intros s W i x y w b Ww Wny Hwitx Hwity Hdecision.
eapply (no_late_fame _ _ x); eauto.
contradict Wny.
eapply world_closed; eauto.
Qed.


Lemma decision_ancestor :
  forall s x y,
    decision s x y true
    -> x @= y.
Proof.
intros s x y Hdecision.
so (ancestor_decide x y) as [| Hnxy]; auto.
exfalso.
so Hdecision as (i & _ & _ & _ & Hwitx & _).
so (no_late_fame _#6 Hwitx Hwitx Hdecision Hnxy) as Hdecision'.
so (decision_fun _#5 Hdecision Hdecision') as H.
discriminate H.
Qed.


Lemma famous_member :
  forall s W x,
    famous s W x
    -> member W x.
Proof.
intros s W x Hfamous.
destruct Hfamous as (y & Hsy & Hdecision).
eapply world_closed; eauto.
eapply decision_ancestor; eauto.
Qed.
