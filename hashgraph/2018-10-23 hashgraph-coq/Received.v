(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Bool.
Require Import Nat.
Require Import Omega.
Require Import List.

Require Import Tact.
Require Import Decide.
Require Import Relation.
Require Import HashgraphFacts.
Require Import Round.
Require Import Progress.
Require Import Decision.
Require Import Consensus.
Require Import Famous.
Require Import Fairness.


Definition ufwitness s W i x :=
  fwitness s W i x
  /\ forall y,
       fwitness s W i y
       -> creator x = creator y
       -> Is_true (textorder x y).


Lemma extends_fwitness :
  forall s W W' i x,
    extends W W'
    -> fwitness s W i x
    -> fwitness s W' i x.
Proof.
intros s W W' i x Hextends Hw.
destruct Hw as (Hwit & Hfamous).
split; auto.
eapply extends_famous; eauto.
Qed.


(** In a few places we need to know that the set of uniue famous witnesses is Kuratowski
   finite (in order to decide received_by).  This holds in all but pathological cases.  
   For, example, it holds for any finite world (which includes all the hashgraphs that
   peers actually manipulate), and it holds for the global world.
*)

Lemma fwitness_ufwitness_finite :
  forall s W i,
    finite (fwitness s W i) -> finite (ufwitness s W i).
Proof.
intros s W i Hfin.
apply (finite_subset' _ _ (fwitness s W i)); auto.
  {
  exact eq_event_decide.
  }

  {
  intros x H.
  destruct H; auto.
  }
intros x Hx.
cut (decidable (forall y, fwitness s W i y -> creator x = creator y -> Is_true (textorder x y))).
  {
  intros [Hyes | Hno].
    {
    left.
    split; auto.
    }

    {
    right.
    contradict Hno.
    destruct Hno; auto.
    }
  }
apply dec_forall_imp_finite; auto.
intros y Hy.
apply dec_imp.
  {
  apply eq_peer_decide.
  }

  {
  apply textorder_decide.
  }
Qed.


Lemma fwitness_finite_finite :
  forall s W,
    finite (member W)
    -> forall i, finite (fwitness s W i).
Proof.
intros s W Hfinite i.
apply (finite_subset _ _ (member W)); auto.
  {
  intros x H.
  destruct H.
  eapply famous_member; eauto.
  }

  {
  intro x.
  apply dec_and.
    {
    apply rwitness_decide.
    }

    {
    apply famous_decide_finite; auto.
    }
  }
Qed.


Lemma ufwitness_finite_finite :
  forall s W,
    finite (member W)
    -> forall i, finite (ufwitness s W i).
Proof.
intros s W Hfin i.
apply fwitness_ufwitness_finite.
apply fwitness_finite_finite; auto.
Qed.  


Lemma fwitness_finite_global :
  forall s i, finite (fwitness s (global s) i).
Proof.
intros s i.
so (famous_witness_exists s i) as (x & Hx).
eapply fwitness_finite_global_if; eauto.
Qed.    


Lemma ufwitness_finite_global :
  forall s i, finite (ufwitness s (global s) i).
Proof.
intros s i.
apply fwitness_ufwitness_finite.
apply fwitness_finite_global; auto.
Qed.    


Definition nonempty W := exists x, member W x.


Lemma nonterminating_nonempty :
  forall W, nonterminating W -> nonempty W.
Proof.
intros W Hnt.
so (Hnt 0) as (_ & x & _ & _ & Wx).
exists x; auto.
Qed.


Definition received_by (s : sample) (W : world) (i : nat) (x : event) :=
  (forall j w, j <= i -> member W w -> rwitness j w -> exists y b, member W y /\ decision s w y b)
  /\
  (forall w, ufwitness s W i w -> x @= w).


Definition received (s : sample) (W : world) (i : nat) (x : event) :=
  received_by s W i x
  /\ forall j, j < i -> ~ received_by s W j x.


Lemma received_by_inhabited :
  forall s W i x,
    nonempty W
    -> received_by s W i x
    -> exists y, member W y /\ round i y.
Proof.
intros s W i x (y & Wy) Hrb.
destruct Hrb as (Hsettled & _).
so (round_defined y) as (j & Hroundy).
so (le_dec j i) as [Hle | Hnle].
2:{
  assert (i <= j) as Hij by omega.
  so (ancestor_witness _#3 Hij Hroundy) as (z & Hzy & (Hroundz & _)).
  exists z.
  split; auto.
  eapply world_closed; eauto.
  }
revert Hsettled.
induct Hle.

(** eq *)
{
intros _.
exists y.
auto.
}

(** S *)
{
intros i Hle IH Hsettled.
exploit IH as H.
  {
  intros j' w Hle' Ww Hwitw.
  apply (Hsettled j'); auto.
  }
destruct H as (z & Wz & Hroundz).
so (ancestor_witness _#3 (le_refl _) Hroundz) as (u & Huz & Hwitu).
so (Hsettled i u (Nat.le_succ_diag_r _) (world_closed _#3 Huz Wz) Hwitu) as (v & b & Wv & Hdecision).
destruct Hdecision as (i' & k & _ & _ & Hwitu' & Hwitv & Hlt & _).
so (rwitness_fun _#3 Hwitu Hwitu'); subst i'.
assert (S i <= k) as Hle' by omega.
so (ancestor_witness _#3 Hle' (Hwitv andel)) as (w & Hwv & (Hroundw & _)).
exists w.
split; auto.
eapply world_closed; eauto.
}
Qed.


Lemma received_fun :
  forall s W i i' x,
    received s W i x
    -> received s W i' x
    -> i = i'.
Proof.
intros s W i j x Hrec Hrec'.
destruct Hrec as (Hrb & Hfirst).
destruct Hrec' as (Hrb' & Hfirst').
so (lt_eq_lt_dec i j) as [[Hij | Heq] | Hji]; auto; exfalso.
  {
  eapply Hfirst'; eauto.
  }

  {
  eapply Hfirst; eauto.
  }
Qed.


Lemma received_by_global :
  forall s i x,
    (forall w,
       ufwitness s (global s) i w -> x @= w)
    -> received_by s (global s) i x.
Proof.
intros s i x Hrb.
split; auto.
intros j w Hji Hsw Hwitw.
so (fame_consensus _ _ Hsw (Hwitw ander)) as (y & b & Hsy & Hdecision).
eauto.
Qed.


Lemma received_by_decide :
  forall s i x,
    decidable (received_by s (global s) i x).
Proof.
intros s i x.
apply (dec_equiv 
         (forall w, ufwitness s (global s) i w -> x @= w)).
  {
  split.
    {
    intro H.
    apply received_by_global; auto.
    }

    {
    intros H w Hw.
    apply H; auto.
    }
  }
apply dec_forall_imp_finite.
  {
  apply ufwitness_finite_global.
  }
intros w _.
apply ancestor_decide.
Qed.


Lemma received_by_exists :
  forall s x,
    member (global s) x
    -> honest (creator x)
    -> exists i,
         received_by s (global s) i x.
Proof.
intros s x Hsx Hhonest.
so (events_are_received s x Hsx Hhonest) as (i & Hall).
exists i.
apply received_by_global.
intros w Hw.
destruct Hw as (Hw & _).
destruct Hw as (Hwit & Hfamous).
apply Hall; auto.
eapply famous_member; eauto.
Qed.


Lemma received_defined :
  forall s x,
    member (global s) x
    -> honest (creator x)
    -> exists i,
         received s (global s) i x.
Proof.
intros s x Hsx Hhonest.
cut (forall i, (exists j, received s (global s) j x) \/ (forall j, j <= i -> ~ received_by s (global s) j x)).
  {
  intro Hprop.
  so (received_by_exists _ _ Hsx Hhonest) as (i & Hrb).
  so (Hprop i) as [? | Hall]; auto.
  so (Hall i (le_refl i)).
  contradiction.
  }
intro i.
induct i.

(** 0 *)
{
so (received_by_decide s 0 x) as [Hrb | Hnrb].
  {
  left.
  exists 0; split; auto.
  intros j H.
  omega.
  }

  {
  right.
  intros j H.
  assert (j = 0) by omega.
  subst j.
  exact Hnrb.
  }
}

(** S *)
{
intros i IH.
destruct IH as [| Hall]; [left; auto |].
so (received_by_decide s (S i) x) as [Hrb | Hnrb].
  {
  left.
  exists (S i).
  split; auto.
  intros j H.
  apply Hall.
  omega.
  }

  {
  right.
  intros j Hle.
  so (eq_nat_dec j (S i)) as [Heq | Hneq].
    {
    subst j.
    auto.
    }

    {
    apply Hall.
    omega.
    }
  }
}
Qed.


Lemma received_by_consistent :
  forall s W W' i x,
    extends W W'
    -> (forall x, decidable (member W x))
    -> nonempty W
    -> received_by s W i x
    -> received_by s W' i x.
Proof.
intros s W W' i x Hextends Hdec Hne Hrb.
so (received_by_inhabited _#4 Hne Hrb) as Hinh.
so Hrb as (Hsettled & Hall).
split.
  {
  intros j w Hji W'w Hwitw.
  so (Hdec w) as [Ww | Wnw].
    {
    so (Hsettled _ _ Hji Ww Hwitw) as (y & b & Wy & Hdecision).
    exists y, b.
    split; auto.
    }

    {
    destruct Hinh as (v & Wv & Hroundv).
    so (ancestor_witness _#3 Hji Hroundv) as (u & Huv & Hwitu).
    so (world_closed _#3 Huv Wv) as Wu.
    so (Hsettled _ _ Hji Wu Hwitu) as (y & b & Wy & Hdecision).
    exists y, false.
    split; auto.
    apply (no_late_fame s j u w y b); auto.
    contradict Wnw.
    eapply world_closed; eauto.
    }
  }

  {
  intros w Hw.
  destruct Hw as ((Hwitw & Hfamous) & Hmin).
  so (Hdec w) as [Ww | Wnw].
    {
    apply Hall; auto.
    so (Hsettled _ _ (le_refl _) Ww Hwitw) as (y & b & Wy & Hdecision).
    split; [split |]; auto.
      {
      exists y.
      split; auto.
      destruct b; auto.
      exfalso.
      destruct Hfamous as (z & W'z & Hdecision').
      so (decision_consistent _#7 (Hextends _ Wy) W'z Hdecision Hdecision') as H.
      discriminate H.
      }

      {
      intros z Hz Heqcr.
      apply Hmin; auto.
      eapply extends_fwitness; eauto.
      }
    }

    {
    exfalso.
    destruct Hinh as (v & Wv & Hroundv).
    so (ancestor_witness _#3 (le_refl _) Hroundv) as (u & Huv & Hwitu).
    so (world_closed _#3 Huv Wv) as Wu.
    so (Hsettled _ _ (le_refl _) Wu Hwitu) as (y & b & Wy & Hdecisionu).
    eassert _ as Hdecision; [refine (no_late_fame _#6 Hwitu Hwitw Hdecisionu _) |].
      {
      contradict Wnw.
      eapply world_closed; eauto.
      }
    destruct Hfamous as (z & W'z & Hdecision').
    so (decision_consistent _#7 (Hextends _ Wy) W'z Hdecision Hdecision') as H.
    discriminate H.
    }
  }
Qed.


Lemma extends_ufwitness :
    forall s W W' i x,
    extends W W'
    -> (forall y, decidable (member W y))
    -> (forall w, member W w -> rwitness i w -> exists y b, member W y /\ decision s w y b)
    -> ufwitness s W i x
    -> ufwitness s W' i x.
Proof.
intros s W W' i x Hextends HdecW Hsettled Hw.
destruct Hw as (Hw & Hfirst).
split; eauto using extends_fwitness.
intros y Hy Heqcr.
apply Hfirst; auto.
destruct Hy as (Hwity & Hfamous).
split; auto.
assert (forall u, member W u -> decision s y u false -> False) as Hnunfamous.
  {
  intros u Wu Hdecision.
  destruct Hfamous as (v & Wv & Hdecision').
  so (decision_consistent _#7 (Hextends _ Wu) Wv Hdecision Hdecision') as H.
  discriminate H.
  }
so (HdecW y) as [Wy | Wny].
  {
  so (Hsettled _ Wy Hwity) as (u & b & Wu & Hdecision).
  exists u.
  split; auto.
  destruct b; auto.
  exfalso.
  eapply Hnunfamous; eauto.
  }

  {
  exfalso.
  destruct Hw as (Hwitx & (u & Wu & Hdecision)).
  so (no_late_fame_world _#7 Wu Wny Hwitx Hwity Hdecision) as Hdecision'.
  eapply Hnunfamous; eauto.
  }
Qed.


Lemma received_consistent :
  forall s W W' i x,
    extends W W'
    -> (forall x, decidable (member W x))
    -> nonempty W
    -> received s W i x
    -> received s W' i x.
Proof.
intros s W W' i x Hextends Hdec Hne Hrec.
destruct Hrec as (Hrb & Hfirst).
split.
  {
  eapply received_by_consistent; eauto.
  }
intros j Hji Hrbj.
refine (Hfirst _ Hji _).
destruct Hrb as (Hsettled & Hall).
split.
  {
  intros k w Hkj Ww Hwitw.
  eapply (Hsettled k); eauto.
  omega.
  }

  {
  intros w Hw.
  apply (Hrbj ander); auto.
  eapply extends_ufwitness; eauto.
  intros v Wv Hwitv.
  apply (Hsettled j); auto.
  omega.
  }
Qed.


Lemma received_cumulative :
  forall s W W' x y i j,
    extends W W'
    -> (forall x, decidable (member W x))
    -> nonempty W
    -> received s W' i x
    -> received s W j y
    -> i <= j
    -> received s W i x.
Proof.
intros s W W' x y i j Hextends Hdec Hne Hrecx Hrecy Hij.
destruct Hrecx as (Hrbx & Hfirstx).
destruct Hrecy as (Hrby & Hfirsty).
split.
  {
  split.
    {
    intros k w Hki Ww Hwitw.
    apply (Hrby andel k); auto.
    omega.
    }

    {
    intros w Hw.
    apply (Hrbx ander); eauto.
    eapply extends_ufwitness; eauto.
    intros v Wv Hwitv.
    eapply (Hrby andel); eauto.
    }
  }

  {
  intros k Hki Hrb.
  refine (Hfirstx k _ _).
    { omega. }
  eapply received_by_consistent; eauto.
  }
Qed.


Lemma decisions_support :
  forall s i,
    exists j,
      i <= j
      /\ forall x y,
           rwitness i x
           -> rwitness j y
           -> member (global s) y
           -> exists b, decision s x y b.
Proof.
intros s i.
so (famous_witness_exists s i) as (z & Hwitz & Hfamousz).
destruct Hfamousz as (w & Hsw & Hdecisionz).
so Hdecisionz as (_ & n & _ & _ & _ & Hwitw & _).
exploit (finite_subset _ (fun x => x @= w /\ rwitness i x) (fun x => x @= w)) as H.
  {
  intros x (H & _).
  auto.
  }

  {
  intro x.
  apply dec_and.
    { apply ancestor_decide. }

    { apply rwitness_decide. }
  }

  {
  apply ancestor_finite.
  }
destruct H as (l & Hl).
assert (exists j, 
          i <= j
          /\ forall k x y,
               j <= k
               -> (k - i) mod coin_freq <> 0
               -> In x l 
               -> rwitness k y 
               -> member (global s) y
               -> exists b, decision s x y b) as H.
  {
  so (Forall_forall _#3 ander (fun x Hx => Hl x ander Hx)) as H.
  clear Hl.
  induct H.
    (** nil *)
    {
    exists i.
    split; auto.
    intros k x y _ _ Hx _.
    destruct Hx.
    }

    (** cons *)
    {
    intros x l Hx _ IH.
    destruct Hx as (Hxw & Hwitx).
    destruct IH as (j & Hij & Hj).
    so (fame_consensus _ _ (world_closed _#3 Hxw Hsw) (Hwitx ander)) as (y & b & Hsy & Hdecision).
    so Hdecision as (_ & k & _ & _ & _ & Hwity & _).
    so (decisions_propagate _#7 Hsy (Hwitx andel) (Hwity andel) Hdecision) as Hall.
    exists (max j (S k)).
    split.
      {
      so (Nat.le_max_l j (S k)).
      omega.
      }
    intros m u v Hle Hnocoin Hu Hwitv Hsv.
    destruct Hu as [| Hu].
      {
      subst u.
      exists b.
      apply (Hall m); auto.
        {
        so (Nat.le_max_r j (S k)).
        omega.
        }
      }

      {
      apply (Hj m); auto.
      so (Nat.le_max_l j (S k)).
      omega.
      }
    }
  }
destruct H as (j & Hij & Hj).
assert (exists k, n < k /\ j <= k /\ (k - i) mod coin_freq <> 0) as (k & Hik & Hjk & Hnocoin).
  {
  so (Nat.le_max_l (S n) j).
  so (Nat.le_max_r (S n) j).
  so (eq_nat_dec ((max (S n) j - i) mod coin_freq) 0) as [Heq | Hneq].
    {
    exists (S (max (S n) j)).
    do2 2 split; try omega.
    replace (S (max (S n) j) - i) with (S (max (S n) j - i)) by omega.
    apply succ_no_coin; auto.
    }

    {
    exists (max (S n) j).
    do2 2 split; auto.
    }
  }
exists k.
split; [omega |].
intros x y Hwitx Hwity Hsy.
so (ancestor_decide x w) as [Hxw | Hnxw].
  {
  eapply Hj; eauto.
  apply Hl; auto.
  }

  {
  exists false.
  so (no_late_fame _#6 Hwitz Hwitx Hdecisionz Hnxw) as Hdecisionx.
  exact (decisions_propagate _#7 Hsw (Hwitx andel) (Hwitw andel) Hdecisionx k y Hsy Hik Hnocoin Hwity).
  }
Qed.


Lemma cumulative_decisions_support :
  forall s i,
    exists j,
      i <= j
      /\ forall i' x y,
           i' <= i
           -> rwitness i' x
           -> round j y
           -> member (global s) y
           -> exists z b, z @= y /\ decision s x z b.
Proof.
intros s.
cut (forall i,
       exists j,
         i <= S j
         /\ forall i' x y,
              i' < i
              -> rwitness i' x
              -> round j y
              -> member (global s) y
              -> exists z b, z @= y /\ decision s x z b).
  {
  intros Hprop i.
  so (Hprop (S i)) as (j & Hij & Hj).
  exists j.
  split; [omega |].
  intros i' x y Hi Hwix Hroundy Hsy.
  apply (Hj i'); eauto.
  omega.
  }
intro i.
induct i.

(** 0 *)
{
exists 0.
split; auto.
intros i' x y H.
omega.
}

(** S *)
{
intros i IH.
destruct IH as (j & Hij & Hj).
so (decisions_support s i) as (k & Hik & Hk).
exists (max j k).
so (Nat.le_max_r j k).
split; [omega |].
intros i' x y Hlt Hwitx Hroundy Hsy.
so (eq_nat_dec i' i) as [Heq | Hneq].
  {
  subst i'.
  so (ancestor_witness _#3 (Max.le_max_r j k) Hroundy) as (z & Hzy & Hwitz).
  so (Hk _ _ Hwitx Hwitz (world_closed _#3 Hzy Hsy)) as (b & Hdecision).
  exists z, b.
  auto.
  }

  {
  so (ancestor_witness _#3 (Max.le_max_l j k) Hroundy) as (z & Hzy & Hwitz).
  assert (i' < i) as Hlt' by omega.
  so (Hj _ _ _ Hlt' Hwitx (Hwitz andel) (world_closed _#3 Hzy Hsy)) as (w & b & Hwy & Hdecision).
  exists w, b.
  split; auto.
  eapply star_trans; eauto.
  }
}
Qed.


Lemma received_by_support :
  forall s i x W,
    extends W (global s)
    -> (forall x, decidable (member W x))
    -> received_by s (global s) i x
    -> exists j,
         (exists y, member W y /\ round j y)
         -> received_by s W i x.
Proof.
intros s i x W HsW Hdec Hrb.
so (cumulative_decisions_support s i) as (k & Hik & Hk).
exists k.
intros (y & Wy & Hroundy).
destruct Hrb as (Hsettled & Hall).
split.
  {
  intros j w Hji Ww Hwitw.
  so (Hk j w y Hji Hwitw Hroundy (HsW _ Wy)) as (z & b & Hzy & Hdecision).
  exists z, b.
  split; auto.
  eapply world_closed; eauto.
  }

  {
  intros w Hw.
  apply Hall; auto.
  eapply extends_ufwitness; eauto.
  intros u Wu Hwitu.
  exploit (Hk i u y) as H; auto.
  destruct H as (z & b & Hzy & Hdecision).
  exists z, b.
  split; auto.
  eapply world_closed; eauto.
  }
Qed.


Lemma received_support :
  forall s i x W,
    extends W (global s)
    -> (forall x, decidable (member W x))
    -> nonempty W
    -> received s (global s) i x
    -> exists j,
         (exists y, member W y /\ round j y)
         -> received s W i x.
Proof.
intros s i x W HsW Hdec Hne Hrec.
destruct Hrec as (Hrb & Hfirst).
so (received_by_support _#4 HsW Hdec Hrb) as (j & Hrbif).
exists j.
intros Hinh.
split.
  {
  apply Hrbif; auto.
  }
intros k Hki.
intro Hrb'.
apply (Hfirst k); auto.
eapply received_by_consistent; eauto.
Qed.
