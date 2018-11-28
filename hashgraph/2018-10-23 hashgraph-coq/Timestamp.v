(* Copyright (c) 2019 by Swirlds, Inc.
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
Require Import Weight.
Require Import HashgraphFacts.
Require Import Sees.
Require Import Round.
Require Import Progress.
Require Import Vote.
Require Import Decision.
Require Import Consensus.
Require Import Famous.
Require Import Fairness.
Require Import Received.
Require Import Median.
Require Import Order.



Lemma ufwitness_fun :
  forall s W i x y,
    creator x = creator y
    -> ufwitness s W i x
    -> ufwitness s W i y
    -> x = y.
Proof.
intros s W i x y Heqcr Hx Hy.
apply (ord_antisym _ _ textorder_order).
  {
  apply (Hx ander); auto.
  exact (Hy andel).
  }

  {
  apply (Hy ander); auto.
  exact (Hx andel).
  }
Qed.


Lemma list_minimum :
  forall (T : Type) (R : T -> T -> Prop) l,
    transitive T R
    -> (forall x y, R x y \/ R y x)
    -> l = nil \/ exists x, In x l /\ forall y, In y l -> R x y.
Proof.
intros T R l Htrans Htotal.
induct l.

(* nil *)
{
left; auto.
}

(* cons *)
{
intros x l IH.
right.
destruct IH as [-> | (y & Hy)].
  {
  exists x.
  split.
    { left; auto. }
  intros y Hy.
  destruct Hy as [Heq | H].
    {
    subst y.
    destruct (Htotal x x); auto.
    }

    {
    destruct H.
    }
  }

  {
  destruct Hy as (Hin & Hy).
  so (Htotal x y) as [Hxy | Hyx].
    {
    exists x.
    split.
      { left; auto. }
    intros z Hz.
    destruct Hz as [Heq | Hz].
      {
      subst z.
      destruct (Htotal x x); auto.
      }

      {
      eapply Htrans; eauto.
      }
    }

    {
    exists y.
    split.
      { right; auto. }
    intros z Hz.
    destruct Hz as [Heq | Hz].
      {
      subst z.
      auto.
      }

      {
      apply Hy; auto.
      }
    }
  }
}
Qed.


Lemma obtain_ufwitness :
  forall s W i x,
    finite (fwitness s W i)
    -> fwitness s W i x
    -> exists y,
         creator x = creator y
         /\ ufwitness s W i y.
Proof.
intros s W i x Hfin Hfwit.
exploit (finite_subset _ (fun z => creator x = creator z /\ fwitness s W i z) (fwitness s W i)) as Hfin'; auto.
  {
  intros z (_ & H); auto.
  }

  {
  intros z.
  apply dec_and.
    { apply eq_peer_decide. }

    {
    apply finite_decide; auto.
    exact eq_event_decide.
    }
  }
destruct Hfin' as (l & Hl).
so (list_minimum _ _ l (ord_trans _ _ textorder_order) textorder_total) as [-> | (y & Hin & Hy)].
  {
  exfalso.
  refine (Hl x andel _).
  split; auto.
  }
so (Hl y ander Hin) as (Heqcr & Hfwit').
exists y.
split; auto.
split; auto.
intros z Hz Heqcr'.
apply Hy.
apply Hl.
split; auto.
transitivity (creator y); auto.
Qed.


Lemma earliest_observer_fun :
  forall x y y' z,
    earliest_observer x y z
    -> earliest_observer x y' z
    -> y = y'.
Proof.
intros x y z w Hy Hz.
destruct Hy as (Hxy & Hy & Hyw).
destruct Hz as (Hxz & Hz & Hzw).
so (star_starr _#4 Hyw) as H; renameover H into Hyw.
so (star_starr _#4 Hzw) as H; renameover H into Hzw.
revert Hyw Hzw.
wfinduct w using parent_well_founded.
intros w IH Hyw Hzw.
invertc Hyw.

(* refl *)
{
intros ->.
invertc Hzw.
  (* refl *)
  {
  intros ->.
  reflexivity.
  }

  (* step *)
  {
  intros z' Hzz' Hz'w.
  exfalso.
  apply (Hy z'); auto.
  eapply star_trans; eauto.
  apply self_ancestor_impl_ancestor.
  apply starr_star; auto.
  }
}

(* step *)
{
intros y' Hyy' Hy'w.
invertc Hzw.
  (* refl *)
  {
  intros ->.
  exfalso.
  apply (Hz y'); auto.
  apply (star_trans _#3 y); eauto.
  apply self_ancestor_impl_ancestor.
  apply starr_star; auto.
  }

  (* step *)
  {
  intros z' Hzz' Hz'w.
  destruct Hy'w as (u & Hparents).
  destruct Hz'w as (u' & Hparents').
  so (parents_fun _#5 Hparents Hparents') as (<- & _).
  apply (IH y'); auto.
  eapply parent1; eauto.
  }
}
Qed.


Lemma earliest_observer_defined :
  forall x z,
    x @= z
    -> exists y,
         earliest_observer x y z.
Proof.
intros x z Hxz.
revert x Hxz.
wfinduct z using parent_well_founded.
intros z IH x Hxz.
so (initial_decide z) as [Hinitial | (u & v & Hparents)].
  {
  so (star_plus _#4 Hxz) as [Heq | Hxz'].
    {
    subst z.
    exists x.
    do2 2 split.
      { apply star_refl. }

      {
      intros w Hwx Hxw.
      apply (strict_ancestor_irreflex x).
      eapply star_plus_trans; eauto.
      apply plus_one.
      apply self_parent_impl_parent; auto.
      }
      
      { apply star_refl. }
    }

    {
    exfalso.
    so (plus_plusr _#4 Hxz') as (u & _ & Huz).
    eapply initial_no_parent; eauto.
    }
  }
so (ancestor_decide x u) as [Hxu | Hnxu].
  {
  so (IH u (parent1 Hparents) x Hxu) as (y & Hearliest).
  exists y.
  destruct Hearliest as (Hxy & Hfirst & Hyu).
  do2 2 split; auto.
  eapply star_trans; eauto.
  apply star_one.
  exists v; auto.
  }

  {
  exists z.
  do2 2 split; auto.
    2:{ apply star_refl. }
  intros u' Hu'z Hxy.
  destruct Hu'z as (v' & Hparents').
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).
  contradiction.
  }
Qed.


Corollary honest_timestamp :
  forall s x t,
    time_received s (global s) x t
    -> exists i y y' w w',
         received s (global s) i x
         /\ honest (creator y)
         /\ honest (creator y')
         /\ ufwitness s (global s) i w
         /\ ufwitness s (global s) i w'
         /\ earliest_observer x y w
         /\ earliest_observer x y' w'
         /\ timestamp y <= t <= timestamp y'.
Proof.
intros s x t Htr.
destruct Htr as (i & l & Hrec & Hdist & Hl & ->).
so (fairness s i) as Hmaj.
exploit (majority_median (fun y => honest (creator y) /\ In y l) l) as H.
  { exact Hdist. }

  {
  unfold EventWeightAndValue.T, EventWeightAndValue.wt.
  so (supermajority_intersect_2' _#5 eq_peer_decide supermajority_honest Hmaj) as (_ & Hmaj').
  destruct Hmaj' as (m & n & _ & Hcardhonest & Hcardall & Hsize).
  exists m, n.
  so (weight_In _ creatorstake l Hdist) as Hcardl.
  eassert _ as H; [refine (weight_subset _ _ (fun y => honest (creator y) /\ In y l) _ _ _ _ Hcardl) |].
    {
    intros y Hy.
    apply dec_and.
      { apply honest_decide. }

      { left; auto. }
    }

    {
    intros y (_ & H); auto.
    }
  destruct H as (m' & Hcardhonest' & _).
  assert (m = m').
    {
    refine (weight_corr_eq _#6 (fun a y => creator y = a) _ _ _ _ _ _ Hcardhonest Hcardhonest').
      {
      intros a a' y _ _ _ Heq Heq'.
      transitivity (creator y); auto.
      }

      {
      intros a y y' _ (_ & Hy) (_ & Hy') Heqcr Heqcr'.
      rewrite <- Heqcr' in Heqcr.
      so (Hl _ ander Hy) as (w & Hw & Hearliest).
      so (Hl _ ander Hy') as (w' & Hw' & Hearliest').
      assert (creator w = creator w') as Heqcrw.
        {
        so (self_ancestor_creator _ _ (earliest_observer_impl_self_ancestor _#3 Hearliest)).
        so (self_ancestor_creator _ _ (earliest_observer_impl_self_ancestor _#3 Hearliest')).
        transitivity (creator y); auto.
        transitivity (creator y'); auto.
        }
      so (ufwitness_fun _#5 Heqcrw Hw Hw'); subst w'.
      eapply earliest_observer_fun; eauto.
      }
      
      {
      intros a (Hhonest & (w & Heqcr & Hw)).
      exploit (obtain_ufwitness s (global s) i w) as H; auto.
        {
        apply fwitness_finite_global.
        }
      destruct H as (v & Heqcrv & Hv).
      so (earliest_observer_defined _ _ (Hrec andel ander _ Hv)) as (z & Hearliest).      
      exists z.
      assert (creator z = a) as Heqcrz.
        {
        transitivity (creator w); auto.
        transitivity (creator v); auto.
        apply self_ancestor_creator.
        eapply earliest_observer_impl_self_ancestor; eauto.
        }
      do2 2 split; auto.
        {
        split.
          {
          force_exact Hhonest.
          f_equal.
          transitivity (creator w); auto.
          transitivity (creator v); auto.
          symmetry.
          apply self_ancestor_creator.
          eapply earliest_observer_impl_self_ancestor; eauto.
          }
  
          {
          apply Hl.
          exists v.
          auto.
          }
        }

        {
        unfold creatorstake.
        rewrite -> Heqcrz.
        reflexivity.
        }
      }

      {
      intros y (Hhonest & Hy).
      exists (creator y).
      do2 2 split; auto.
      split; auto.
      so (Hl _ ander Hy) as (w & Hw & Hearliest).
      exists w.
      split.
        {
        symmetry.
        apply self_ancestor_creator.
        eapply earliest_observer_impl_self_ancestor; eauto.
        }

        {
        exact (Hw andel).
        }
      }
    }
  subst m'.
  assert (n = sumweight creatorstake l) as Heq.
    {
    refine (weight_corr_eq _#6 (fun a y => creator y = a) _ _ _ _ _ _ Hcardall Hcardl).
      {
      intros a a' y _ _ _ Heq Heq'.
      transitivity (creator y); auto.
      }

      {
      intros a y y' _ Hy Hy' Heqcr Heqcr'.
      rewrite <- Heqcr' in Heqcr.
      so (Hl _ ander Hy) as (w & Hw & Hearliest).
      so (Hl _ ander Hy') as (w' & Hw' & Hearliest').
      assert (creator w = creator w') as Heqcrw.
        {
        so (self_ancestor_creator _ _ (earliest_observer_impl_self_ancestor _#3 Hearliest)).
        so (self_ancestor_creator _ _ (earliest_observer_impl_self_ancestor _#3 Hearliest')).
        transitivity (creator y); auto.
        transitivity (creator y'); auto.
        }
      so (ufwitness_fun _#5 Heqcrw Hw Hw'); subst w'.
      eapply earliest_observer_fun; eauto.
      }
      
      {
      intros a (w & Heqcr & Hw).
      exploit (obtain_ufwitness s (global s) i w) as H; auto.
        {
        apply fwitness_finite_global.
        }
      destruct H as (v & Heqcrv & Hv).
      so (earliest_observer_defined _ _ (Hrec andel ander _ Hv)) as (z & Hearliest).      
      exists z.
      assert (creator z = a) as Heqcrz.
        {
        transitivity (creator w); auto.
        transitivity (creator v); auto.
        apply self_ancestor_creator.
        eapply earliest_observer_impl_self_ancestor; eauto.
        }
      do2 2 split; auto.
        {
        apply Hl.
        exists v.
        auto.
        }

        {
        unfold creatorstake.
        rewrite -> Heqcrz.
        reflexivity.
        }
      }

      {
      intros y Hy.
      exists (creator y).
      split; auto.
      so (Hl _ ander Hy) as (w & Hw & Hearliest).
      split; auto.
      exists w.
      split.
        {
        symmetry.
        apply self_ancestor_creator.
        eapply earliest_observer_impl_self_ancestor; eauto.
        }

        {
        exact (Hw andel).
        }
      }
    }
  rewrite <- Heq in Hcardl.
  do2 3 split; auto.
  intros y (_ & H); auto.
  }
destruct H as (y & y' & (Hhonesty & Hy) & (Hhonesty' & Hy') & Hstamplo & Hstamphi).
so (Hl _ ander Hy) as (w & Hw & Hearliest).
so (Hl _ ander Hy') as (w' & Hw' & Hearliest').
exists i, y, y', w, w'.
do2 8 split; auto.
  {
  unfold EventWeightAndValue.vl, leU, EventWeightAndValue.lebU in Hstamplo.
  exact (leb_complete _ _ Hstamplo).
  }

  {
  unfold EventWeightAndValue.vl, leU, EventWeightAndValue.lebU in Hstamphi.
  exact (leb_complete _ _ Hstamphi).
  }
Qed.
