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
Require Import Cardinality.
Require Import Calculate.
Require Import Majority.
Require Import HashgraphFacts.
Require Import Sees.
Require Import Round.
Require Import Progress.
Require Import Vote.
Require Import Decision.



(** Spawn order *)

Lemma ancestor_impl_spawn_le :
  forall s i x y,
    y = spawn s i
    -> x @= y
    -> exists j, x = spawn s j /\ j <= i.
Proof.
intros s i x y Heq Hxy.
revert i Heq.
induct Hxy.

(** refl *)
{
intros x i ->.
exists i.
auto.
}

(** step *)
{
intros x y z Hparent _ IH i ->.
so (IH i (eq_refl _)) as (j & -> & Hle).
so (spawn_parent _#3 Hparent) as (k & -> & Hlt).
exists k.
split; auto.
omega.
}
Qed.


Lemma strict_ancestor_impl_spawn_lt :
  forall s i x y,
    y = spawn s i
    -> x @ y
    -> exists j, x = spawn s j /\ j < i.
Proof.
intros s i x y Heqy Hxy.
so (ancestor_impl_spawn_le _#4 Heqy (plus_star _#4 Hxy)) as (j & -> & Hle).
exists j.
split; auto.
so (le_lt_or_eq _ _ Hle) as [| Heq]; auto.
exfalso.
subst y j.
eapply strict_ancestor_irreflex; eauto.
Qed.


Lemma realtime_refl_spawn :
  forall s i,
    realtime s (spawn s i) (spawn s i).
Proof.
intros s i.
exists i, i.
auto.
Qed.


Lemma realtime_spawn_impl_leq :
  forall s i j,
    realtime s (spawn s i) (spawn s j)
    -> i <= j.
Proof.
intros s i j H.
destruct H as (i' & j' & Hi & Hj & Hle).
so (spawn_inj _#3 Hi); subst i'.
so (spawn_inj _#3 Hj); subst j'.
auto.
Qed.


(** Similarity *)

Lemma similar_weaken :
  forall s s' i j,
    j <= i
    -> similar s s' i
    -> similar s s' j.
Proof.
intros s s' i j Hij Hsim.
split.
  {
  intros k Hkj.
  apply (Hsim andel); omega.
  }

  {
  intros k Hkj.
  apply (Hsim ander); omega.
  }
Qed.


Lemma similar_symm :
  forall s s' i,
    similar s s' i
    -> similar s' s i.
Proof.
intros s s' i Hsim.
split.
  {
  intros j Hji.
  symmetry.
  apply (Hsim andel); auto.
  }

  {
  intros j Hji.
  symmetry.
  rewrite <- (Hsim andel); [| omega].
  apply (Hsim ander); auto.
  }
Qed.


Lemma similar_election :
  forall (V V' : event -> bool -> Prop) n y t f,
    (forall z v, z @ y -> V z v -> V' z v)
    -> election V n y t f
    -> election V' n y t f.
Proof.
intros V V' n y t f Hsim Helection.
destruct Helection as (T & F & Hcard & Hcardt & Hcardf & HT & HF).
exists T, F.
do2 4 split; auto.
  {
  intros w Hw.
  so (HT _ Hw) as (Helector & HVw).
  split; auto.
  apply Hsim; auto.
  apply stsees_impl_strict_ancestor.
  exact (Helector ander).
  }

  {
  intros w Hw.
  so (HF _ Hw) as (Helector & HVw).
  split; auto.
  apply Hsim; auto.
  apply stsees_impl_strict_ancestor.
  exact (Helector ander).
  }
Qed.


Lemma similar_vote :
  forall s s' x y v,
    (forall z, z @= y -> coin z s = coin z s')
    -> vote s x y v
    -> vote s' x y v.
Proof.
intros s s' x y v Hsim Hvote.
revert v Hsim Hvote.
wfinduct y using strict_ancestor_well_founded.
intros y IH v Hsim Hvote.
invertc Hvote.

(** first *)
{
intros m n Hwitx Hwity Hmn Hge Hiff.
eapply vote_first; eauto.
}

(** regular *)
{
intros m n t f Hwitx Hwity Hlt Hnocoin Helection Htally.
eapply vote_regular; eauto.
apply (similar_election (vote s x)); auto.
intros z v' Hzy Hvote.
apply (IH z); auto.
intros z' Hz'z.
apply Hsim.
eapply star_trans; eauto.
apply plus_star; auto.
}

(** coin_super *)
{
intros m n t f Hwitx Hwity Hlt Hcoin Helection Htally.
eapply vote_coin_super; eauto.
apply (similar_election (vote s x)); auto.
intros z v' Hzy Hvote.
apply (IH z); auto.
intros z' Hz'z.
apply Hsim.
eapply star_trans; eauto.
apply plus_star; auto.
}

(** coin *)
{
intros m n t f Hwitx Hwity Hlt Hcoin Helection Ht Hf <-.
rewrite -> Hsim; [| apply star_refl].
eapply (@vote_coin _#5 t f); eauto.
apply (similar_election (vote s x)); auto.
intros z v' Hzy Hvote.
apply (IH z); auto.
intros z' Hz'z.
apply Hsim.
eapply star_trans; eauto.
apply plus_star; auto.
}
Qed.



(** First witnesses *)

Definition first_witness (s : sample) (n : nat) (x : event) :=
  member (global s) x
  /\ rwitness n x
  /\ forall y,
       member (global s) y
       -> rwitness n y
       -> realtime s x y.


Lemma first_witness_fun :
  forall s n x y,
    first_witness s n x
    -> first_witness s n y
    -> x = y.
Proof.
intros s n x y Hx Hy.
apply (realtime_antisym s).
  {
  apply (Hx anderr).
    { exact (Hy andel). }
  
    { exact (Hy anderl). }
  }

  {
  apply (Hy anderr).
    { exact (Hx andel). }
  
    { exact (Hx anderl). }
  }
Qed.


Lemma first_witness_realtime :
  forall s n x y,
    first_witness s n x
    -> member (global s) y
    -> rwitness n y
    -> realtime s x y.
Proof.
intros s n x y Hx Hyy Hwity.
apply (Hx anderr); auto.
Qed.


Lemma similar_first_witness :
  forall s s' i n,
    similar s s' i
    -> first_witness s n (spawn s i)
    -> first_witness s' n (spawn s i).
Proof.
intros s s' i n Hsim Hfirst.
destruct Hfirst as (Hmem & Hwit & Hfirst).
do2 2 split; auto.
  {
  rewrite -> (Hsim andel); auto.
  exists i, i.
  auto.
  }

  {
  intros y Hmem' Hwit'.
  destruct Hmem' as (j & _ & -> & _).
  so (le_dec i j) as [Hle | Hnle].
    {
    exists i, j.
    do2 2 split; auto.
    rewrite -> (Hsim andel); auto.
    }

    {
    exfalso.
    assert (j <= i) as Hle by omega.
    exploit (Hfirst (spawn s j)) as H.
      {
      exists j, j.
      auto.
      }

      {
      rewrite <- (Hsim andel) in Hwit'; auto.
      }
    so (realtime_spawn_impl_leq _#3 H); auto.
    }
  }
Qed.


Lemma first_witness_exists :
  forall s n x,
    member (global s) x
    -> rwitness n x
    -> exists y, first_witness s n y.
Proof.
intros s n x Hmem Hwitx.
assert (forall i,
          rwitness n (spawn s i)
          -> (forall j, j < i -> ~ rwitness n (spawn s j))
          -> exists y, first_witness s n y) as Hmake.
  {
  intros i Hwit Hnone.
  exists (spawn s i).
  do2 2 split; auto.
    {
    exists i, i.
    auto.
    }

    {
    intros y Hmemy Hwity.
    destruct Hmemy as (j & _ & -> & _).
    so (lt_dec j i) as [Hlt | Hnlt].
      {
      destruct (Hnone _ Hlt Hwity).
      }

      {
      exists i, j.
      do2 2 split; auto.
      omega.
      }
    }
  }
assert (forall i,
          (forall j, j < i -> ~ rwitness n (spawn s j))
          \/
          (exists y, first_witness s n y)) as H.
  {
  intro i.
  induct i.
    (** 0 *)
    {
    left.
    intros j Hlt.
    omega.
    }

    (** S *)
    {
    intros i IH.
    destruct IH as [Hnone | Hfirst].
      2:{ right; auto. }
    so (rwitness_decide n (spawn s i)) as [Hwit | Hnwit].
      {
      right.
      eapply Hmake; eauto.
      }

      {
      left.
      intros j Hlt.
      so (lt_dec j i) as [Hji | Hnji].
        {
        apply Hnone.
        omega.
        }

        {
        assert (i = j) by omega.
        subst j.
        exact Hnwit.
        }
      }
    }
  }
destruct Hmem as (i & _ & -> & _).
destruct (H (S i)) as [Hnone | Hfirst]; auto.
eapply Hmake; eauto.
Qed.



(** The coin assumption *)

(** Proving this constructively and without any form of the axiom of choice
   is surprisingly tricky.
*)

Lemma good_coins :
  forall s m x,
    rwitness m x
    -> exists n y t f v,
         m < n
         /\ (n - m) mod coin_freq = 0
         /\ member (global s) y
         /\ rwitness n y
         /\ election (vote s x) (pred n) y t f
         /\ ((t >= f /\ v = true) \/ (f > t /\ v = false))
         /\ forall w,
              member (global s) w
              -> rwitness n w
              -> honest (creator w)
              -> coin w s = v.
Proof.
intros s m x Hwitx.
set (Q :=
       fun i y => 
         member (global s) y
         /\ honest (creator y)
         /\ rwitness ((S i) * coin_freq + m) y).
(** We can't name the specific y we want (without using choice) so we have to describe it. *)
set (P :=
       fun i s' =>
         exists y t f,
           first_witness s' (S i * coin_freq + m) y
           /\ election (vote s' x) (pred (S i * coin_freq + m)) y t f
           /\ t >= f).
exploit (eventual_agreement (S number_peers) s Q P) as Hagree.
  (** Qs are disjoint *)
  {
  intros i j y Hiy Hjy.
  destruct Hiy as (_ & _ & (Hround & _)).
  destruct Hjy as (_ & _ & (Hround' & _)).
  so (round_fun _#3 Hround Hround') as Heq.
  assert (coin_freq <> 0) as Hcoinnzero.
    {
    so first_regular_min.
    so coin_freq_min.
    omega.
    }
  so (Nat.add_cancel_r _#3 andel Heq) as Heq1.
  so (Nat.mul_cancel_r _#3 Hcoinnzero andel Heq1) as Heq2.
  injection Heq2; auto.
  }

  (** Qs are honest *)
  {
  intros i y Hy.
  exact (Hy anderl).
  }

  (** Number of Qs is bounded *)
  {
  intros i H.
  destruct H as (l & Hdist & Hl & Hlen).
  assert (cardinality (fun w => In w l) (length l)) as Hcardl.
    {
    exists l.
    do2 2 split; auto.
    intro; split; auto.
    }
  exploit (cardinality_map_inj _ _ (fun w => In w l) (@every peer) creator (length l) number_peers) as H; auto.
    {
    unfold every; auto.
    }

    {
    intros y z Hy Hz Heqcr.
    destruct (Hl _ Hy) as (Hyy & Hhonest & Hwity).
    destruct (Hl _ Hz) as (Hzz & _ & Hwitz).
    apply (honest_witness_unique (global s) (S i * coin_freq + m)); auto.
    }

    { exact number_of_peers. }
  omega.
  }

  (** P(i) is limited to before Q(i) *)
  {
  intros i j s' Hj Hsimilar.
  split.
    {
    intro H.
    destruct H as (y & t & f & Hy & Helection & Htally).
    so Hy as ((k & _ & Hspawny & _) & _).
    assert (k <= j) as Hkj.
      {
      subst y.
      exact (realtime_spawn_impl_leq _#3 (first_witness_realtime _#4 Hy (realtime_refl_spawn _ _) (Hj anderr))).
      }
    exists y, t, f.
    do2 2 split; auto.
      {
      subst y.
      eapply similar_first_witness; eauto.
      eapply similar_weaken; eauto.
      }

      {
      refine (similar_election _#6 _ Helection).
      intros z v Hzy Hvote.
      apply (similar_vote s s'); auto.
      intros w Hwz.
      exploit (strict_ancestor_impl_spawn_lt s k w y) as H; auto.
        {
        eapply star_plus_trans; eauto.
        }
      destruct H as (k' & -> & Hk'k).
      apply (Hsimilar ander).
      omega.
      }
    }
      
    {
    intro H.
    destruct H as (y & t & f & Hy & Helection & Htally).
    so Hy as ((k & _ & Hspawny & _) & _).
    assert (k <= j) as Hkj.
      {
      subst y.
      rewrite -> (Hsimilar andel) in Hj; auto.
      exact (realtime_spawn_impl_leq _#3 (first_witness_realtime _#4 Hy (realtime_refl_spawn _ _) (Hj anderr))).
      }
    exists y, t, f.
    do2 2 split; auto.
      {
      subst y.
      eapply similar_first_witness; eauto.
      eapply similar_weaken; eauto.
      apply similar_symm; auto.
      }

      {
      refine (similar_election _#6 _ Helection).
      intros z v Hzy Hvote.
      apply (similar_vote s' s); auto.
      intros w Hwz.
      exploit (strict_ancestor_impl_spawn_lt s' k w y) as H; auto.
        {
        eapply star_plus_trans; eauto.
        }
      destruct H as (k' & -> & Hk'k).
      apply (similar_symm _ _ _ Hsimilar ander).
      omega.
      }
    }
  }
destruct Hagree as (i & v & Hcoins & Hbaseline).
assert (exists y, first_witness s (S i * coin_freq + m) y) as (y & Hy).
  {
  so (all_rounds_inhabited _ (S i * coin_freq + m) (global_nonterminating s)) as (u & Hwitu & Hu).
  eapply first_witness_exists; eauto.
  }
so Hy as (_ & Hwity & _).
assert (m < pred (S i * coin_freq + m)) as Hlt.
  {
  cut (1 * 2 <= S i * coin_freq).
    {
    intro.
    omega.
    }
  transitivity (S i * 2).
    {
    apply Nat.mul_le_mono_r.
    omega.
    }

    {
    apply Nat.mul_le_mono_l.
    so first_regular_min.
    so coin_freq_min.
    omega.
    }
  }
exploit (election_defined (vote s x) (pred (S i * coin_freq + m)) y) as H.
  {
  intros; eapply vote_fun; eauto.
  }

  {
  intros w Hwy Hwitw.
  eapply vote_defined; eauto.
  }
destruct H as (t & f & Helection).
exists (S i * coin_freq + m), y, t, f, v.
do2 6 split; auto.
  { omega. }

  {
  replace (S i * coin_freq + m - m) with (S i * coin_freq) by omega.
  apply Nat.mod_mul.
  so first_regular_min.
  so coin_freq_min.
  omega.
  }

  {
  exact (Hy andel).
  }

  {
  destruct v.
    {
    left.
    split; auto.
    exploit (Hbaseline andel) as H.
      { exact I. }
    destruct H as (y' & t' & f' & Hy' & Helection' & Htally).
    so (first_witness_fun _#4 Hy Hy'); subst y'.
    so (election_fun _#8 Helection Helection') as (<- & <-).
    auto.
    }

    {
    right.
    split; auto.
    so (le_dec f t) as [Hle | Hnle].
      2:{ omega. }
    exfalso.
    apply Hbaseline.
    exists y, t, f.
    split; auto.
    }
  }

  {
  intros w Hw Hwitw Hhonest.
  apply Hcoins.
  do2 2 split; auto.
  }
Qed.


Lemma eligible_voter_maximum :
  forall s n,
    weight_lt 
      creatorstake
      (fun x => 
         exists y,
           member (global s) y
           /\ rwitness n x 
           /\ stsees x y) (S total_stake).
Proof.
intros s n.
apply weight_lt_by_contradiction.
intros P p HP Hp Hge.
cut (total_stake >= p).
  { intro; omega. }
refine (weight_map_inj _ _ creatorstake stake _ every creator _ _ _ _ Hp _).
  {
  unfold every; auto.
  }

  {
  intros x y Hx Hy Heqcr.
  so (HP _ Hx) as (z & Hmemz & Hwitx & Hxz).
  so (HP _ Hy) as (z' & Hmemz' & Hwity & Hyz').
  eapply (stseen_witness_unique (global s) _#3 z z'); eauto.
  }

  { exact the_total_stake. }
Qed.


Lemma neq_negb :
  forall b b', b <> b' -> negb b = b'.
Proof.
intros b b' Hneq.
destruct b, b'; auto.
destruct Hneq; auto.
Qed.


Lemma too_many_voters :
  forall s m n x y i j v,
    member (global s) y
    -> rwitness m x
    -> rwitness (S n) y
    -> m < n
    -> weight creatorstake (fun w => elector n w y /\ vote s x w v) i
    -> weight creatorstake (fun w => elector n w y /\ vote s x w (negb v)) j
    -> weight_lt creatorstake (fun w => exists z, member (global s) z /\ rwitness n w /\ vote s x w v /\ stsees w z) (one_third total_stake)
    -> i >= j
    -> False.
Proof.
intros s m n x y i j v Hmemy Hwitx Hwity Hmn Hi Hj Hlt Hij.
eassert _ as Hin; [refine (weight_lt_impl_lt _#6 _ Hi Hlt) |].
  {
  intros w (Helector, Hvote).
  destruct Helector as (Hwit & Hss).
  exists y; auto.
  }
exploit (weight_sum _#6 Hi Hj) as Hcardy.
  {
  intros w (_ & Hvote) (_ & Hvote').
  so (vote_fun _#5 Hvote' Hvote) as Heq.
  so (no_fixpoint_negb v).
  contradiction.
  }
cbn in Hcardy.
eassert _ as Hcardy'; [refine (weight_iff _ _ _ (fun w => elector n w y) _ _ Hcardy) |].
  {
  intros w.
  split.
    {
    intros H.
    destruct H as [(?, ?) | (?, ?)]; auto.
    }

    {
    intros Helector.
    so (vote_defined s _#4 Hwitx (Helector andel) Hmn) as (v' & Hvote).
    so (bool_dec v v') as [Heq | Hneq].
      {
      subst v'.
      left; auto.
      }

      {
      so (neq_negb _ _ Hneq).
      subst v'.
      right; auto.
      }
    }
  }
so (elector_minimum _#3 (Hwity andel) Hcardy') as Hij_n.
so (half_supermajority _#3 Hij_n Hij) as Hin'.
omega.
Qed.


Lemma too_many_voters_elector :
  forall s n x y z i j k v,
    member (global s) y
    -> member (global s) z
    -> rwitness (S n) y
    -> rwitness (S n) z
    -> weight creatorstake (fun w => elector n w y /\ vote s x w v) i
    -> weight creatorstake (fun w => elector n w y /\ vote s x w (negb v)) j
    -> weight creatorstake (fun w => elector n w z /\ vote s x w (negb v)) k
    -> i >= j
    -> k > two_thirds total_stake
    -> False.
Proof.
intros s n x y z i j k v Hmemy Hmemz Hwity Hwitz Hi Hj Hk Hij Hkn.
assert (exists m, rwitness m x /\ m < n) as (m & Hwitx & Hmn).
  {
  assert (k > 0) as Hk0 by omega.
  so (weight_nonempty _#4 Hk Hk0) as (w & ((Hwitw, _), Hvote)).
  so (vote_witness _#4 Hvote) as (Hwitx & _).
  so (vote_round _#4 Hvote) as (m & n' & Hroundx & Hroundw & Hlt).
  so (round_fun _#3 (Hwitw andel) Hroundw); subst n'.
  exists m.
  split; auto.
  split; auto.
  }
apply (too_many_voters s m n x y i j v); auto.
apply weight_lt_by_contradiction.
intros P l HP Hl Hln.
exploit (weight_sum _#6 Hk Hl) as Hcard.
  {
  intros w (_ & Hvote) HPw.
  so (HP _ HPw) as (_ & _ & _ & Hvote' & _).
  so (vote_fun _#5 Hvote Hvote') as Heq.
  so (no_fixpoint_negb v).
  contradiction.
  }
cbn in Hcard.
so (eligible_voter_maximum s n) as Hlt.
eassert _ as Hkl_n; [refine (weight_lt_impl_lt _#6 _ Hcard Hlt) |].
  {
  intros w H.
  destruct H as [H | H].
    {
    destruct H as ((Hwitw & Hwz), _).
    exists z.
    do2 2 split; auto.
    }

    {
    so (HP _ H) as H'.
    cbn beta in H'.
    destruct_all H'; eauto.
    }
  }
unfold one_third in Hln.
omega.
Qed.


Lemma too_many_voters_honest :
  forall s m n x y i j v,
    member (global s) y
    -> rwitness m x
    -> rwitness (S n) y
    -> m < n
    -> weight creatorstake (fun w => elector n w y /\ vote s x w v) i
    -> weight creatorstake (fun w => elector n w y /\ vote s x w (negb v)) j
    -> (forall w, member (global s) w -> rwitness n w -> honest (creator w) -> vote s x w (negb v))
    -> i >= j
    -> False.
Proof.
intros s m n x y i j v Hmemy Hwitx Hwity Hmn Hi Hj Hallhonest Hij.
apply (too_many_voters s m n x y i j v); auto.
apply weight_lt_by_contradiction.
intros P l HP Hl Hln.
eassert _ as Hl'; [refine (weight_image _ _ creatorstake stake _ creator _ _ _ Hl) |]; auto.
  {
  intros t u HPt HPu Heqcr.
  so (HP _ HPt) as (z & Hmemz & Hwitt & _ & Htz).
  so (HP _ HPu) as (z' & Hmemz' & Hwitu & _ & Huz').
  eapply (stseen_witness_unique (global s) _#3 z z'); eauto.
  }
match type of Hl' with
| weight _ ?P _ => assert (superminority stake P every) as Hmin
end.
  {
  exists l, total_stake.
  do2 3 split; auto.
  exact the_total_stake.
  }
so (superminority_supermajority_intersect _#5 eq_peer_decide Hmin supermajority_honest) as H.
cbn in H.
destruct H as (? & ((w & -> & HPw) & Hhonest)).
so (HP _ HPw) as (z & Hmemz & Hwitw & Hvote & Hwz).
assert (member (global s) w) as Hmemw.
  {
  apply (realtime_member s w z).
  apply ancestor_realtime; auto.
  apply stsees_impl_ancestor; auto.
  }
so (Hallhonest w Hmemw Hwitw Hhonest) as Hvote'.
so (vote_fun _#5 Hvote' Hvote).
so (no_fixpoint_negb v).
contradiction.
Qed.


Lemma plus_two_no_coin :
  forall n,
    n mod coin_freq = 0
    -> (2 + n) mod coin_freq <> 0.
Proof.
intros n Heq.
so coin_freq_min.
replace (2 + n) with (n + 2) by omega.
rewrite -> Nat.add_mod; [| omega].
rewrite -> Heq.
cbn.
rewrite -> Nat.mod_mod; [| omega].
rewrite -> Nat.mod_small; omega.
Qed.


(** Theorem 5.16 *)
Theorem fame_consensus :
  forall s x,
    member (global s) x
    -> witness x
    -> exists y v,
         member (global s) y
         /\ decision s x y v.
Proof.
intros s x Hx Hwitx.
unfold global in Hx; cbn in Hx.
so (round_defined x) as (m & Hroundx).
assert (rwitness m x) as H.
  {
  split; auto.
  }
clear Hwitx.
rename H into Hwitx.
so (good_coins s _ _ Hwitx) as (n & y & t & f & v & Hmn & Hcoin & Hy & Hwity & Helectiony & Htallyy & Hagree).
so first_regular_min as Hfrm.
so coin_freq_min as Hfrnc.
assert (n - m >= coin_freq) as Hafc.
  {
  so (lt_dec (n - m) coin_freq) as [Hlt | Hnlt].
    2:{ omega. }
  exfalso.
  so (Nat.mod_small _ _ Hlt).
  omega.
  }
assert (forall w, member (global s) w -> rwitness n w -> honest (creator w) -> vote s x w v) as Hhonest_unanimous.
  {
  intros w Hw Hwitw Hhonest.
  so (vote_defined s _#4 Hwitx Hwitw Hmn) as (v' & Hvote).
  cut (v = v').
    {
    intro; subst v'; auto.
    }
  invertc Hvote.
    (** first *)
    {
    intros m' n' Hwitx' Hwitw' Hlt Hgeq _.
    exfalso.
    so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
    so (rwitness_fun _#3 Hwitw Hwitw'); subst n'.
    omega.
    }

    (** regular *)
    {
    intros m' n' t' f' Hwitx' Hwitw' _ Hnocoin.
    exfalso.
    so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
    so (rwitness_fun _#3 Hwitw Hwitw'); subst n'.
    contradiction.
    }

    (** coin_super *)
    {
    intros m' n' t' f' Hwitx' Hwitw' _ _ Helectionw Htallyw.    
    so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
    so (rwitness_fun _#3 Hwitw Hwitw'); subst n'.
    so (destruct_election _#6 Helectiony) as (Hcardy & Hcardyt & Hcardyf).
    so (destruct_election _#6 Helectionw) as (Hcardw & Hcardwt & Hcardwf).
    destruct v; destruct v'; auto.
      {
      exfalso.
      destruct Htallyy as [(Htf & _) | (_ & Heq)].
        2:{ discriminate Heq. }
      apply (too_many_voters_elector s (pred n) x y w t f f' true); auto.
        {
        replace (S (pred n)) with n by omega.
        auto.
        }

        {
        replace (S (pred n)) with n by omega.
        auto.
        }
      }
      
      {
      exfalso.
      destruct Htallyy as [(_ & Heq) | (Htf & _)].
        { discriminate Heq. }
      apply (too_many_voters_elector s (pred n) x y w f t t' false); auto.
        {
        replace (S (pred n)) with n by omega.
        auto.
        }

        {
        replace (S (pred n)) with n by omega.
        auto.
        }

        { omega. }
      }
    }

    (** coin *)
    {
    intros m' n' _ _ Hwitx' Hwitw' _ _ _ _ _ <-.
    so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
    so (rwitness_fun _#3 Hwitw Hwitw'); subst n'.
    symmetry.
    apply Hagree; auto.
    }
  }
clear y t f Hy Hwity Helectiony Htallyy.
assert (forall w, member (global s) w -> rwitness (S n) w -> vote s x w v) as Hunanimous.
  {
  intros w Hw Hwitw.
  assert (m < S n) as Hmn' by omega.
  so (vote_defined s _#4 Hwitx Hwitw Hmn') as (v' & Hvote).
  cut (v = v').
    {
    intro; subst v'; auto.
    }
  invertc Hvote.
    (** first *)
    {
    intros m' n' Hwitx' Hwitw' Hlt Hgeq _.
    exfalso.
    so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
    so (rwitness_fun _#3 Hwitw Hwitw'); subst n'.
    omega.
    }

    (** regular *)
    {
    intros m' n' t f Hwitx' Hwitw' _ _ Helection Htally.
    so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
    so (rwitness_fun _#3 Hwitw Hwitw'); subst n'.
    cbn in Helection.
    so (destruct_election _#6 Helection) as (Hcard & Hcardt & Hcardf).
    destruct v; destruct v'; auto.
      {
      exfalso.
      destruct Htally as [(_ & Heq) | (Htf & _)].
        { discriminate Heq. }
      apply (too_many_voters_honest s m n x w f t false); auto.
      omega.
      }

      {
      exfalso.
      destruct Htally as [(Htf & _) | (_ & Heq)].
        2:{ discriminate Heq. }
      apply (too_many_voters_honest s m n x w t f true); auto.
      }
    }

    (** coin_super *)
    {
    intros m' n' _ _ Hwitx' Hwitw' _ Hcoin' _ _.
    exfalso.
    so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
    so (rwitness_fun _#3 Hwitw Hwitw'); subst n'.
    so (succ_no_coin _ Hcoin).
    replace (S n - m) with (S (n - m)) in Hcoin' by omega.
    contradiction.
    }

    (** coin *)
    {
    intros m' n' _ _ Hwitx' Hwitw' _ Hcoin' _ _ _ _.
    exfalso.
    so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
    so (rwitness_fun _#3 Hwitw Hwitw'); subst n'.
    so (succ_no_coin _ Hcoin).
    replace (S n - m) with (S (n - m)) in Hcoin' by omega.
    contradiction.
    }
  }
so (all_rounds_inhabited _ (2 + n) (global_nonterminating s)) as (z & Hwitz & Hz).
exists z, v.
split.
  { exact Hz. }
eapply unanimity_impl_decision; eauto.
  { omega. }

  {
  replace (S (S n) - m) with (2 + (n - m)) by omega.
  apply plus_two_no_coin; auto.
  }
Qed.
