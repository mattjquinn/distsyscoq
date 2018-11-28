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
Require Import Weight.
Require Import Majority.
Require Import HashgraphFacts.
Require Import Sees.
Require Import Round.
Require Import Vote.


Definition decision (s : sample) (x y : event) (v : bool) :=
  exists m n t f,
    rwitness m x
    /\ rwitness n y
    /\ m + first_regular < n
    /\ (n - m) mod coin_freq <> 0
    /\ election (vote s x) (pred n) y t f
    /\ (if v then t else f) > two_thirds total_stake.



Lemma elector_rwitness :
  forall n x y, elector n x y -> rwitness n x.
Proof.
intros n x y H.
destruct H; auto.
Qed.


Lemma elector_unique :
  forall W n x y z z',
    member W z
    -> member W z'
    -> creator x = creator y
    -> elector n x z
    -> elector n y z'
    -> x = y.
Proof.
intros W n x y z z' Wz Wz' Heq Helectorx Helectory.
destruct Helectorx as (Hwitx & Hssx).
destruct Helectory as (Hwity & Hssy).
eapply (stseen_witness_unique _#4 z z'); eauto.
Qed.


Lemma elector_minimum :
  forall n x e,
    round (S n) x
    -> weight creatorstake (fun w => elector n w x) e
    -> e > two_thirds total_stake.
Proof.
intros n x e Hroundx Hcard.
so (stsees_many_witnesses _ _ Hroundx) as Hmaj.
destruct Hmaj as (p & q & _ & Hcardp & Hcardpeers & Hgt).
so (weight_fun _#5 the_total_stake Hcardpeers); subst q.
eapply lt_le_trans; eauto.
refine (weight_map_surj _ _ stake creatorstake _ _ creator _ _ _ _ Hcardp Hcard).
  {
  intros w Helector.
  split; auto.
  exists w.
  destruct Helector.
  do2 2 split; auto.
  }

  {
  intros a H.
  destruct H as (w & Heqcr & Hss & Hwit).
  subst a.
  exists w.
  split; auto.
  split; auto.
  }
Qed.


Lemma election_fun :
  forall s n x y t t' f f',
    election (vote s x) n y t f
    -> election (vote s x) n y t' f'
    -> t = t' /\ f = f'.
Proof.
intros s n x y t t' f f' Helect Helect'.
eapply election_fun_gen; eauto.
intros w _ v v' Hv Hv'.
eapply vote_fun; eauto.
Qed.


Lemma decision_fun :
  forall s x y v v',
    decision s x y v
    -> decision s x y v'
    -> v = v'.
Proof.
intros s x y v v' Hdecision Hdecision'.
destruct Hdecision as (m & n & t & f & Hwitx & Hwity & Hlt & Hnocoin & Helect & Htally).
destruct Hdecision' as (m' & n' & t' & f' & Hwitx' & Hwity' & _ & _ & Helect' & Htally').
so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
so (rwitness_fun _#3 Hwity Hwity'); subst n'.
so (election_fun _#8 Helect Helect') as (<- & <-).
so (maximum_votes _#5 Helect).
so (four_thirds_le total_stake).
destruct v; destruct v'; auto; omega.
Qed.


Lemma decision_decide :
  forall s x y b,
    decidable (decision s x y b).
Proof.
intros s x y b.
so (witness_decide x) as [Hwitx | Hnwit].
2:{
  right.
  contradict Hnwit.
  destruct Hnwit as (? & ? & ? & ? & (_ & H) & _).
  exact H.
  }
so (witness_decide y) as [Hwity | Hnwit].
2:{
  right.
  contradict Hnwit.
  destruct Hnwit as (? & ? & ? & ? & _ & (_ & H) & _).
  exact H.
  }
so (round_defined x) as (m & Hroundx).
so (round_defined y) as (n & Hroundy).
so (dec_lt (m + first_regular) n) as [Hlt | Hnlt].
2:{
  right.
  contradict Hnlt.
  destruct Hnlt as (m' & n' & _ & _ & (Hroundx' & _) & (Hroundy' & _) & Hlt & _).
  so (round_fun _#3 Hroundx Hroundx'); subst m'.
  so (round_fun _#3 Hroundy Hroundy'); subst n'.
  exact Hlt.
  }
so (eq_nat_dec ((n - m) mod coin_freq) 0) as [Hcoin | Hnocoin].
  {
  right.
  contradict Hcoin.
  destruct Hcoin as (m' & n' & _ & _ & (Hroundx' & _) & (Hroundy' & _) & _ & Hnocoin & _).
  so (round_fun _#3 Hroundx Hroundx'); subst m'.
  so (round_fun _#3 Hroundy Hroundy'); subst n'.
  exact Hnocoin.
  }
assert (m < pred n) as Hmn.
  {
  so first_regular_min.
  omega.
  }
so (election_defined' s _#3 y (conj Hroundx Hwitx) Hmn) as (t & f & Helection).
so (dec_lt (two_thirds total_stake) (if b then t else f)) as [Htally | Hntally].
2:{
  right.
  contradict Hntally.
  destruct Hntally as (_ & n' & t' & f' & _ & (Hroundy' & _) & _ & _ & Helection' & Htally).
  so (round_fun _#3 Hroundy Hroundy'); subst n'.
  so (election_fun _#8 Helection Helection') as (<- & <-).
  exact Htally.
  }
left.
exists m, n, t, f.
do2 5 split; auto; split; auto.
Qed.


Lemma destruct_election :
  forall s n x y t f,
    election (vote s  x) n y t f
    -> weight creatorstake (fun w => elector n w y) (t + f)
       /\ weight creatorstake (fun w => elector n w y /\ vote s x w true) t
       /\ weight creatorstake (fun w => elector n w y /\ vote s x w false) f.
Proof.
intros s n x y t f H.
destruct H as (T & F & Htf & Ht & Hf & HT & HF).
exploit (weight_partition _ creatorstake T F (fun w => elector n w y) t f) as Hdec; auto.
  {
  intros w Hw.
  apply HT; auto.
  }

  {
  intros w Hw.
  apply HF; auto.
  }

  {
  intros w _.
  apply stake_positive.
  }

  {
  intros w HTw HFw.
  so (HT _ HTw ander) as Htrue.
  so (HF _ HFw ander) as Hfalse.
  so (vote_fun _#5 Htrue Hfalse) as Heq.
  discriminate Heq.
  }
do2 2 split; auto.
  {
  eapply weight_iff; eauto.
  intros w.
  split; auto.
  intros (Helector, Hvote).
  so (Hdec _ Helector) as [HTw | HFw]; auto.
  so (HF _ HFw ander) as Hvote'.
  so (vote_fun _#5 Hvote Hvote') as Heq.
  discriminate Heq.
  }

  {
  eapply weight_iff; eauto.
  intros w.
  split; auto.
  intros (Helector, Hvote).
  so (Hdec _ Helector) as [HTw | HFw]; auto.
  so (HT _ HTw ander) as Hvote'.
  so (vote_fun _#5 Hvote Hvote') as Heq.
  discriminate Heq.
  }
Qed.


Lemma destruct_election' :
  forall s n x y t f,
    election (vote s x) n y t f
    -> weight creatorstake (fun w => elector n w y) (t + f)
       /\ forall v, weight creatorstake (fun w => elector n w y /\ vote s x w v) (if v then t else f).
Proof.
intros s n x y t f Helection.
so (destruct_election _#6 Helection) as (Htf & Ht & Hf).
split; auto.
intros v.
destruct v; auto.
Qed.


Definition peer_vote (s : sample) (W : world) (w : event) (n : nat) (a : peer) (v : bool) :=
  exists x y, creator x = a /\ round n x /\ vote s w x v /\ stsees x y /\ member W y.


Definition offer (n : nat) (a : peer) (y : event) :=
  exists x, creator x = a /\ elector n x y.


Lemma elector_vote_peer :
  forall s W n x y z v,
    member W z
    -> elector n y z
    -> vote s x y v
    -> peer_vote s W x n (creator y) v.
Proof.
intros s W n x y z v Wz Helector Hvote.
exists y.
exists z.
destruct Helector as (Hwit & Hss).
do2 4 split; auto.
destruct Hwit; auto.
Qed.


Lemma peer_vote_elector :
  forall s W x n a v y z,
    member W z
    -> peer_vote s W x n a v
    -> creator y = a
    -> elector n y z
    -> vote s x y v.
Proof.
intros s W x n a v y z Wz Hvotea <- Helector.
destruct Hvotea as (w & z' & Heq & Hround & Hvote & Hss' & Wz').
force_exact Hvote.
f_equal.
eapply (elector_unique _#4 z' z); eauto.
split; eauto.
split; auto.
eapply vote_witness; eauto.
Qed.


Lemma peer_vote_offer :
  forall s W x n a v y,
    member W y
    -> peer_vote s W x n a v
    -> offer n a y
    -> exists z, creator z = a /\ elector n z y /\ vote s x z v.
Proof.
intros s W x n a v y Wy Hvotea Hoffer.
destruct Hoffer as (z & Helector & Hvote).
exists z.
do2 2 split; auto.
eapply peer_vote_elector; eauto.
Qed.


Lemma decision_vote_consistent :
  forall s W w x y n v v',
    member W x
    -> member W y
    -> round n x
    -> round n y
    -> decision s w x v
    -> vote s w y v'
    -> v = v'.
Proof.
intros s W w x y n v v' Wx Wy Hroundx Hroundy Hdecision Hvote.
destruct Hdecision as (m & n' & t & f & Hwitw & Hwitx & Hlt & Hnocoin & Helect & Htally).
so Hwitx as (Hroundx' & _).
so (round_fun _#3 Hroundx Hroundx'); subst n'.
assert (exists n', n = S n') as (n' & ?).
  {
  exists (pred n).
  omega.
  }
subst n.
rename n' into n.
invert Hvote.
  {
  intros m' n' Hwitw' Hwity Hlt' Hgeq Hv.
  so (rwitness_fun _#3 Hwitw Hwitw'); subst m'.
  so Hwity as (Hroundy' & _).
  so (round_fun _#3 Hroundy Hroundy'); subst n'.
  omega.
  }

2:{
  intros m' n' _ _ Hwitw' Hwity _ Hcoin _ _.
  so (rwitness_fun _#3 Hwitw Hwitw'); subst m'.
  so Hwity as (Hroundy' & _).
  so (round_fun _#3 Hroundy Hroundy'); subst n'.
  contradiction.
  }

2:{
  intros m' n' _ _ Hwitw' Hwity _ Hcoin _ _ _ _.
  so (rwitness_fun _#3 Hwitw Hwitw'); subst m'.
  so Hwity as (Hroundy' & _).
  so (round_fun _#3 Hroundy Hroundy'); subst n'.
  contradiction.
  }
intros m' n' t' f' Hwitw' Hwity _ _ Helect' Htally'.
so (rwitness_fun _#3 Hwitw Hwitw'); subst m'.
so Hwity as (Hroundy' & _).
so (round_fun _#3 Hroundy Hroundy'); subst n'.
cbn in Helect, Helect'.
so (destruct_election' _#6 Helect) as (_ & Htfx).
so (destruct_election' _#6 Helect') as (Hally & Htfy).
assert (supermajority stake (fun a => peer_vote s W w n a v /\ offer n a x) every) as Hmajx.
  {
  exists (if v then t else f), total_stake.
  do2 3 split; auto.
    2:{ exact the_total_stake. }
  eassert _ as H; [refine (weight_image _ _ creatorstake stake _ creator _ _ _ (Htfx v)) |]; auto.
    {
    intros z z' (Helector, _) (Helector', _) Heq.
    eapply (elector_unique _#4 x x); eauto.
    }
  refine (weight_iff _#5 _ H).
  intro a.
  split.
    {
    intros (z & -> & Helector & Hvotez).
    split.
      { eapply (elector_vote_peer _#5 x); eauto. }
    exists z.
    split; auto.
    }

    {
    intros (Hvotea & Hoffer).
    so (peer_vote_offer _#7 Wx Hvotea Hoffer) as (z & Heqcr & Helector & Hvotez).
    exists z.
    do2 2 split; auto.
    }
  }
assert (supermajority stake (fun a => offer n a y) every) as Hmajy.
  {
  so (stsees_many_witnesses _ _ (Hwity andel)) as Hmaj.
  refine (supermajority_iff _#5 _ Hmaj).
  intro a.
  split.
    {
    intros (z & Heq & Hss & Hwit).
    exists z.
    split; auto.
    split; auto.
    }

    {
    intros H.
    destruct H as (z & Heq & Helector).
    destruct Helector.
    exists z.
    auto.
    }
  }
so (supermajority_intersect_2 _#5 eq_peer_decide Hmajx Hmajy) as (A & Hmajx' & Hmajy').
so (majority_incl _#4 Hmajx') as HAx.
destruct Hmajy' as (d & e & HAy & Hd & He & Hgt).
assert (d <= if v then t' else f') as Hle.
  {
  refine (weight_corr_le _#6 (fun a z => creator z = a) _ _ _ _ Hd (Htfy v)).
    {
    intros a a' z _ _ _ Heq Heq'.
    transitivity (creator z); auto.
    }

    {
    intros a Ha.
    so (HAy a Ha) as Hoffer.
    so (HAx a Ha) as (Hvotea & _).
    so (peer_vote_offer _#7 Wy Hvotea Hoffer) as (z & Heqcr & Helector & Hvotez).
    exists z.
    subst a.
    do2 2 split; auto.
    }
  }
assert (e = t' + f').
  {
  refine (weight_corr_eq _#6 (fun a z => creator z = a) _ _ _ _ _ _ He Hally).
    {
    intros a a' z _ _ _ Heq Heq'.
    transitivity (creator z); auto.
    }

    {
    intros a z z' _ Helector Helector' ? ?.
    subst a.
    eapply elector_unique; eauto.
    }

    {
    intros a Hoffer.
    destruct Hoffer as (z & <- & Helector).
    exists z.
    split; auto.
    }

    {
    intros z Helector.
    exists (creator z).
    do2 2 split; auto.
    exists z.
    auto.
    }
  }
subst e; clear He.
assert ((if v then t' else f') > (if v then f' else t')).
  {
  eapply lt_le_trans; [| exact Hle].
  eapply le_lt_trans; [| exact Hgt].
  destruct v.
    {
    apply majority_complement; omega.
    }

    {
    replace (t' + f') with (f' + t') in Hgt |- * by omega.
    apply majority_complement; omega.
    }
  }
destruct v; destruct Htally' as [(Hord & ->) | (Hord & ->)]; auto; omega.
Qed.


Lemma unanimous_election :
  forall s W n x y v e,
    member W y
    -> rwitness (S n) y
    -> (forall w, member W w -> rwitness n w -> vote s x w v)
    -> weight creatorstake (fun w => elector n w y) e
    -> election (vote s x) n y (if v then e else 0) (if v then 0 else e).
Proof.
intros s W n x y v e Wy Hwitx Hunan Helectors.
destruct v.
  {
  exists (fun w => elector n w y), (fun w => False).
  do2 4 split; auto.
    {
    replace (e + 0) with e by omega.
    auto.
    }

    { apply weight_empty. }

    {
    intros w Hw.
    split; auto.
    apply Hunan.
      {
      eapply world_closed; eauto.
      apply stsees_impl_ancestor.
      exact (Hw ander).
      }

      {
      eapply elector_rwitness; eauto.
      }
    }

    {
    intros w Hw.
    destruct Hw.
    }
  }

  {
  exists (fun w => False), (fun w => elector n w y).
  do2 4 split; auto.
    { apply weight_empty. }

    {
    intros w Hw.
    destruct Hw.
    }

    {
    intros w Hw.
    split; auto.
    apply Hunan.
      {
      eapply world_closed; eauto.
      apply stsees_impl_ancestor.
      exact (Hw ander).
      }

      {
      eapply elector_rwitness; eauto.
      }
    }
  }
Qed.


Lemma unanimity_persists :
  forall s W m n x v,
    round m x
    -> m + first_regular < n
    -> (forall y, member W y -> rwitness n y -> vote s x y v)
    -> (forall y, member W y -> rwitness (S n) y -> vote s x y v).
Proof.
intros s W m n x v Hroundx Hlt Hunan y Wy Hwity.
so (elector_weight n y) as (e & Helectors).
so (elector_minimum _ _ _ (Hwity andel) Helectors) as Hlte.
so (unanimous_election _#7 Wy Hwity Hunan Helectors) as Helection.
assert (witness x) as Hwitx.
  {
  so (ancestor_witness n (S n) y (Nat.le_succ_diag_r n) (Hwity andel)) as (z & Hzy & Hwitz).
  so (Hunan z (world_closed _#3 Hzy Wy) Hwitz) as Hvote.
  so (vote_witness _#4 Hvote) as (Hwitx & _).
  exact Hwitx.
  }
so (dec_eq_nat ((S n - m) mod coin_freq) 0) as [Hcoin | Hnocoin].
  {
  apply (@vote_coin_super s x y m (S n) (if v then e else 0) (if v then 0 else e) v); auto.
    { split; auto. }

    { omega. }

    { destruct v; auto. }
  }

  {
  apply (@vote_regular s x y m (S n) (if v then e else 0) (if v then 0 else e) v); auto.
    { split; auto. }

    {
    destruct v.
      {
      left.
      split; auto.
      omega.
      }

      {
      right.
      split; auto.
      omega.
      }
    }
  }
Qed.


Lemma unanimity :
  forall s W m n x y v,
    member W y
    -> round m y
    -> m <= n
    -> decision s x y v
    -> forall z, member W z -> rwitness n z -> vote s x z v.
Proof.
intros s W m n x y v Wy Hroundy Hleq Hdecision.
induct Hleq.

(** eq *)
{
intros z Wz Hwitz.
so Hdecision as (l & m' & _ & _ & Hwitx & Hwity & Hlt & _).
so (round_fun _#3 (Hwity andel) Hroundy); subst m'.
assert (l < m) as Hlt' by omega.
so (vote_defined s _#4 Hwitx Hwitz Hlt') as (v' & Hvote).
so (decision_vote_consistent _#8 Wy Wz Hroundy (Hwitz andel) Hdecision Hvote).
subst v'.
exact Hvote.
}

(** leq *)
{
intros n Hle IH z.
destruct Hdecision as (l & m' & _ & _ & (Hroundx & _) & (Hroundy' & _) & Hlt & _).
so (round_fun _#3 Hroundy Hroundy'); subst m'.
eapply unanimity_persists; eauto.
omega.
}
Qed.


Lemma decision_consistent :
  forall s W x y y' v v',
    member W y
    -> member W y'
    -> decision s x y v
    -> decision s x y' v'
    -> v = v'.
Proof.
intros s W.
cut (forall x y z m n v v',
       member W y
       -> member W z
       -> round m y
       -> round n z
       -> m <= n
       -> decision s x y v
       -> decision s x z v'
       -> v = v').

  {
  intros Hprop x y z v v' Wy Wz Hdecision Hdecision'.  
  so (round_defined y) as (m & Hroundy).
  so (round_defined z) as (n & Hroundz).
  so (le_dec m n) as [Hle | Hnle].
    {
    apply (Hprop x y z m n v v'); auto.
    }

    {
    symmetry.
    apply (Hprop x z y n m v' v); auto.
    omega.
    }
  }
intros x y z m n v v' Wy Wz Hroundy Hroundz Hleq Hdecisiony Hdecisionz.
so Hdecisionz as (_ & n' & _ & _ & _ & Hwitz & _).
so (round_fun _#3 Hroundz (Hwitz andel)); subst n'.
so (unanimity _#7 Wy Hroundy Hleq Hdecisiony z Wz Hwitz) as Hvote.
so (decision_vote_consistent _#8 Wz Wz Hroundz Hroundz Hdecisionz Hvote).
subst v'.
auto.
Qed.


Lemma unanimity_impl_decision :
  forall s W x y m n v,
    member W y
    -> round m x
    -> (forall z, member W z -> rwitness n z -> vote s x z v)
    -> rwitness (S n) y
    -> m + first_regular < S n
    -> (S n - m) mod coin_freq <> 0
    -> decision s x y v.
Proof.
intros s W x y m n v Wy Hroundx Hunan Hwity Hlt Hnocoin.
so (elector_weight n y) as (e & Helectors).
so (elector_minimum _ _ _ (Hwity andel) Helectors) as Hlte.
so (unanimous_election _#7 Wy Hwity Hunan Helectors) as Helection.
assert (witness x) as Hwitx.
  {
  so (ancestor_witness n (S n) y (Nat.le_succ_diag_r n) (Hwity andel)) as (z & Hzy & Hwitz).
  so (Hunan z (world_closed _#3 Hzy Wy) Hwitz) as Hvote.
  so (vote_witness s _#3 Hvote) as (Hwitx & _).
  exact Hwitx.
  }
exists m, (S n), (if v then e else 0), (if v then 0 else e).
do2 5 split; auto.
  { split; auto. }

  {
  destruct v; auto.
  }
Qed.


Lemma decisions_propagate :
  forall s W x y l m v,
    member W y
    -> round l x
    -> round m y
    -> decision s x y v
    -> forall n z,
         member W z
         -> m < n
         -> (n - l) mod coin_freq <> 0
         -> rwitness n z
         -> decision s x z v.
Proof.
intros s W x y l m v Wy Hroundx Hroundy Hdecision n z Wz Ht Hnocoin Hwitz.
destruct n as [| n]; [omega |].
eapply unanimity_impl_decision; eauto.
  {
  eapply (unanimity _#5 y); eauto.
  omega.
  }

  {
  so Hdecision as (l' & m' & _ & _ & (Hroundx' & _) & (Hroundy' & _) & Hlt & _).
  so (round_fun _#3 Hroundx Hroundx'); subst l'.
  so (round_fun _#3 Hroundy Hroundy'); subst m'.
  omega.
  }
Qed.


Lemma succ_no_coin :
  forall n,
    n mod coin_freq = 0
    -> (S n) mod coin_freq <> 0.
Proof.
intros n Heq.
so first_regular_min.
so coin_freq_min.
replace (S n) with (n + 1) by omega.
rewrite -> Nat.add_mod; [| omega].
rewrite -> Heq.
cbn.
rewrite -> Nat.mod_mod; [| omega].
rewrite -> Nat.mod_small; omega.
Qed.


(** Lemma 5.15 *)
Corollary decisions_propagate_round :
  forall s W x y m v,
    member W y
    -> nonterminating W
    -> round m y
    -> decision s x y v
    -> exists n,
         n <= m + 2
         /\ forall z,
              member W z
              -> rwitness n z
              -> decision s x z v.
Proof.
intros s W x y m v Wy Hnt Hroundy Hdecision.
so Hdecision as (l & m' & _ & _ & (Hroundx & _) & (Hroundy' & _) & Hleq & _).
so (round_fun _#3 Hroundy Hroundy'); subst m'.
so (dec_eq_nat ((S m - l) mod coin_freq) 0) as [Heq | Hneq].
  {
  exists (m + 2).
  split; auto.
  intros z HGz Hwitz.
  eapply (decisions_propagate s W x y) with (n := (m + 2)); eauto; [omega |].
  replace (m + 2 - l) with (S (S m - l)) by omega.
  apply succ_no_coin; auto.
  }

  {
  exists (S m).
  split; [omega |].
  intros z HGz Hwitz.
  eapply (decisions_propagate s W x y) with (n := S m); eauto.
  }
Qed.
