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


Definition elector (n : nat) (w y : event) :=
  rwitness n w /\ stsees w y.
  

Definition creatorstake : event -> nat := fun w => stake (creator w).


(** This is phrased a bit oddly to ensure that V appears strictly positively. *)
Definition election (V : event -> bool -> Prop) (n : nat) (y : event)
  :=
  fun t f =>
    exists T F,
      weight creatorstake (fun w => elector n w y) (t + f)  (* make sure we have all the votes *)
      /\ weight creatorstake T t
      /\ weight creatorstake F f
      /\ (forall w, T w -> elector n w y /\ V w true)
      /\ (forall w, F w -> elector n w y /\ V w false).


Inductive vote : sample -> event -> event -> bool -> Prop :=
| vote_first {s x y m n v} :
    rwitness m x
    -> rwitness n y
    -> m < n
    -> m + first_regular >= n
    -> (Is_true v <-> x @ y)
    -> vote s x y v

| vote_regular {s x y m n t f v} :
    rwitness m x
    -> rwitness n y
    -> m + first_regular < n
    -> (n - m) mod coin_freq <> 0
    -> election (vote s x) (pred n) y t f
    -> ((t >= f /\ v = true) \/ (f > t /\ v = false))
    -> vote s x y v

| vote_coin_super {s x y m n t f} {v : bool} :
    rwitness m x
    -> rwitness n y
    -> m < n
    -> (n - m) mod coin_freq = 0
    -> election (vote s x) (pred n) y t f
    -> (if v then t else f) > two_thirds total_stake
    -> vote s x y v

| vote_coin {s x y m n t f} :
    rwitness m x
    -> rwitness n y
    -> m < n
    -> (n - m) mod coin_freq = 0
    -> election (vote s x) (pred n) y t f
    -> t <= two_thirds total_stake
    -> f <= two_thirds total_stake
    -> vote s x y (coin y s)
.


Lemma vote_witness :
  forall s x y b,
    vote s x y b
    -> witness x /\ witness y.
Proof.
intros s x y b H.
cases H; eauto using rwitness_witness.
Qed.


Lemma vote_round :
  forall s x y b,
    vote s x y b
    -> x << y.
Proof.
intros s x y b H.
induct H; intros; eapply rwitness_earlier; eauto; omega.
Qed.


Lemma maximum_votes :
  forall V n y t f,
    election V n y t f
    -> t + f <= total_stake.
Proof.
intros V n y t f H.
destruct H as (_ & _ & Hcard & _).
exploit (weight_map_inj _ _ creatorstake stake (fun w => elector n w y) (@every peer) creator (t + f) total_stake); auto.
  { unfold every; auto. }

  {
  intros v w Hv Hw Heq.
  destruct Hv.
  destruct Hw.
  so (event_world y) as (W & Wy).
  eapply stseen_witness_unique; eauto.
  }

  { exact the_total_stake. }
Qed.


Lemma election_fun_gen :
  forall (V : event -> bool -> Prop) n y t t' f f',
    (forall w, w @ y -> forall v v', V w v -> V w v' -> v = v')
    -> election V n y t f
    -> election V n y t' f'
    -> t = t' /\ f = f'.
Proof.
intros V n y t t' f f' IH Helect Helect'.
destruct Helect as (T & F & Hcard & HcardT & HcardF & HT & HF).
destruct Helect' as (T' & F' & Hcard' & HcardT' & HcardF' & HT' & HF').
so (weight_fun _#5 Hcard Hcard') as Heqsum.
exploit (weight_partition _ creatorstake T F (fun w => elector n w y) t f) as Hpartition; auto.
  {
  intros w Hw.
  exact (HT w Hw andel).
  }

  {
  intros w Hw.
  exact (HF w Hw andel).
  }

  {
  intros w _.
  apply stake_positive.
  }

  {
  intros w HTw HFw.
  so (HT w HTw) as (Helector & Htrue).
  so (HF w HFw ander) as Hfalse.
  destruct Helector as (_ & Hss).
  so (IH _ (stsees_impl_strict_ancestor _ _ Hss) _ _ Htrue Hfalse) as Heq.
  discriminate Heq.
  }
so (lt_eq_lt_dec t t') as [[Hlt | Heq]| Hlt].
  {
  so (weight_difference _#6 eq_event_decide HcardT HcardT' Hlt) as (x & HnTx & HT'x).
  so (HT' x HT'x) as (Helector & Htrue).
  so (Hpartition _ Helector) as [HTx | HFx].
    { contradiction. }
  so (HF x HFx) as (_ & Hfalse).
  destruct Helector as (_ & Hss).
  so (IH _ (stsees_impl_strict_ancestor _ _ Hss) _ _ Htrue Hfalse) as Heq.
  discriminate Heq.
  }

  {
  subst t'.
  split; auto.
  omega.
  }

  {
  assert (f < f') as Hlt' by omega.
  so (weight_difference _#6 eq_event_decide HcardF HcardF' Hlt') as (x & HnFx & HF'x).
  so (HF' x HF'x) as (Helector & Hfalse).
  so (Hpartition _ Helector) as [HTx | HFx].
    2:{ contradiction. }
  so (HT x HTx) as (_ & Htrue).
  destruct Helector as (_ & Hss).
  so (IH _ (stsees_impl_strict_ancestor _ _ Hss) _ _ Htrue Hfalse) as Heq.
  discriminate Heq.
  }
Qed.


(** Special case of Lemma 5.14 *)
Lemma vote_fun :
  forall s x y v v',
    vote s x y v
    -> vote s x y v'
    -> v = v'.
Proof.
intros s x y.
wfinduct y using strict_ancestor_well_founded.
intros y IH v v' Hvote Hvote'.
invertc Hvote.
(** Blech, 16 cases! *)

(** first *)
{
intros m n Hwitx Hwity Hlt Hgeq Hv.
invertc Hvote'.
  (** first *)
  {
  intros m' n' Hwitx' Hwity' _ _ Hv'.
  apply eq_bool_prop_intro.
  transitivity (x @ y); auto.
  symmetry; auto.
  }

  (** regular *)
  {
  intros m' n' _ _ Hwitx' Hwity' Hlt' _ _ _.  
  exfalso.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  omega.
  }

  (** coin_super *)
  {
  intros m' n' t f Hwitx' Hwity' _ Hcoin _ _.
  exfalso.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  so coin_freq_min.
  rewrite -> Nat.mod_small in Hcoin; omega.
  }

  (** coin *)
  {
  intros m' n' _ _ Hwitx' Hwity' _ Hcoin _ _ _ _.
  exfalso.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  so coin_freq_min.
  rewrite -> Nat.mod_small in Hcoin; omega.
  }
}

(** regular *)
{
intros m n t f Hwitx Hwity Hlt Hnocoin Helect Htally.
invertc Hvote'.
  (** first *)
  {
  intros m' n' Hwitx' Hwity' Hlt' Hgeq' _.
  exfalso.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m.
  so (rwitness_fun _#3 Hwity Hwity'); subst n.
  omega.
  }

  (** regular *)
  {
  intros m' n' t' f' Hwitx' Hwity' _ _ Helect' Htally'.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  so (election_fun_gen _#7 IH Helect Helect') as (<- & <-).
  destruct Htally as [(Hwin & ->) | (Hwin & ->)];
  destruct Htally' as [(Hwin' & ->) | (Hwin' & ->)]; auto; omega.
  }

  (** coin_super *)
  {
  intros m' n' _ _ Hwitx' Hwity' _ Hcoin _ _.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  contradiction.
  }

  (** coin *)
  {
  intros m' n' _ _ Hwitx' Hwity' _ Hcoin _ _ _ _.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  contradiction.
  }
}

(** coin_super *)
{
intros m n t f Hwitx Hwity Hlt Hcoin Helect Htally.
invertc Hvote'.
  (** first *)
  {
  intros m' n' Hwitx' Hwity' Hlt' Hgeq' _.
  exfalso.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  so coin_freq_min.
  rewrite -> Nat.mod_small in Hcoin; omega.
  }

  (** regular *)
  {
  intros m' n' _ _ Hwitx' Hwity' _ Hnocoin _ _.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  contradiction.
  }

  (** coin_super *)
  {
  intros m' n' t' f' Hwitx' Hwity' _ _ Helect' Htally'.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  so (election_fun_gen _#7 IH Helect Helect') as (<- & <-).
  so (maximum_votes _#5 Helect).
  so (four_thirds_le total_stake).
  destruct v; destruct v'; auto; omega.
  }

  (** coin *)
  {
  intros m' n' t' f' Hwitx' Hwity' _ _ Helect' Htallyt Htallyf _.
  exfalso.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  so (election_fun_gen _#7 IH Helect Helect') as (<- & <-).
  destruct v; omega.
  }
}

(** coin *)
{
intros m n t f Hwitx Hwity Hlt Hcoin Helect Htallyt Htallyf <-.
invertc Hvote'.
  (** first *)
  {
  intros m' n' Hwitx' Hwity' Hlt' Hgeq _.
  exfalso.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  so coin_freq_min.
  rewrite -> Nat.mod_small in Hcoin; omega.
  }

  (** regular *)
  {
  intros m' n' _ _ Hwitx' Hwity' _ Hnocoin _ _.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m.
  so (rwitness_fun _#3 Hwity Hwity'); subst n.
  contradiction.
  }

  (** coin_super *)
  {
  intros m' n' t' f' Hwitx' Hwity' _ _ Helect' Htally'.
  exfalso.
  so (rwitness_fun _#3 Hwitx Hwitx'); subst m'.
  so (rwitness_fun _#3 Hwity Hwity'); subst n'.
  so (election_fun_gen _#7 IH Helect Helect') as (<- & <-).
  destruct v'; omega.
  }

  (** coin *)
  {
  auto.
  }
}
Qed.


(** Lemma 5.14 *)
Lemma vote_consistent :
  forall s w x y z n b b',
    creator x = creator y
    -> round n x
    -> round n y
    -> vote s w x b
    -> vote s w y b'
    -> stsees x z
    -> stsees y z
    -> b = b'.
Proof.
intros s w x y z n b b' Heqcr Hroundx Hroundy Hvotex Hvotey Hxz Hyz.
so (vote_witness _#4 Hvotex) as (_ & Hwitx).
so (vote_witness _#4 Hvotey) as (_ & Hwity).
so (event_world z) as (W & Wz).
so (stseen_witness_unique _#6 Wz Wz Heqcr (conj Hroundx Hwitx) (conj Hroundy Hwity) Hxz Hyz).
subst y.
exact (vote_fun _#5 Hvotex Hvotey).
Qed.



Lemma elector_decide :
  forall n y w,
    decidable (elector n w y).
Proof.
intros n y w.
unfold elector, rwitness.
apply dec_and; [apply dec_and |].
  {
  so (round_defined w) as (n' & Hround).
  so (dec_eq_nat n n') as [Heq | Hneq].
    {
    subst n'.
    left; auto.
    }
    
    {
    right.
    contradict Hneq.
    eapply round_fun; eauto.
    }
  }

  { apply witness_decide. }

  { apply stsees_decide. }
Qed.


Lemma elector_weight :
  forall n y,
    exists i,
      weight creatorstake (fun w => elector n w y) i.
Proof.
intros n y.
apply finite_weight.
  { exact eq_event_decide. }
apply (finite_subset _ _ (fun x => x @ y)).
  {
  intros w Hw.
  destruct Hw as (_ & Hss).
  apply stsees_impl_strict_ancestor; auto.
  }

  { intros; apply elector_decide. }

  { apply strict_ancestor_finite. }
Qed.


Lemma election_defined :
  forall (V : event -> bool -> Prop) r y,
    (forall w v v', V w v -> V w v' -> v = v')
    -> (forall w, w @ y -> rwitness r w -> exists v, V w v)
    -> exists t f,
         election V r y t f.
Proof.
intros V r y Hfun Hvote.
so (elector_weight r y) as (n & Hcard).
so Hcard as (a & Hdista & Ha & Hlena).
exploit (enumerate_subset _ (fun w => w @ y /\ rwitness r w /\ V w true) a) as H; auto.
  {
  intros w _.
  so (strict_ancestor_decide w y) as [Hwy | Hnwy].
  2:{
    right.
    intros (H & _).
    contradiction.
    }
  so (rwitness_decide r w) as [Hwit | Hnwit].
  2:{
    right.
    intros (_ & H & _).
    contradiction.
    }
  so (Hvote _ Hwy Hwit) as (v & Hv).
  destruct v.
    { left; auto. }
  right.
  intros (_ & _ & Hv').
  so (Hfun _#3 Hv Hv') as Heq.
  discriminate Heq.
  }
destruct H as (t & Hdistt & Ht).
exploit (enumerate_subset _ (fun w => ~ In w t) a) as H; auto.
  {
  intros w _.
  apply dec_not.
  apply dec_In.
  exact eq_event_decide.
  }
destruct H as (f & Hdistf & Hf).
exists (sumweight creatorstake t), (sumweight creatorstake f).
exists (fun w => In w t), (fun w => In w f).
do2 4 split.
  {
  replace (sumweight creatorstake t + sumweight creatorstake f) with n; auto.
  rewrite <- sumweight_app.
  subst n.
  apply permutation_weight.
  apply Permutation.NoDup_Permutation; auto.
    {
    apply NoDup_app; auto.
    intros x Hxt Hxf.
    so (Hf _ andel Hxf andel).
    contradiction.
    }

    {
    intro x.
    split.
      {
      intro Hxa.
      so (dec_In _ x t eq_event_decide) as [Hin | Hnin].
        {
        apply in_or_app; left; auto.
        }

        {
        apply in_or_app; right.
        apply Hf; auto.
        }
      }

      {
      intro Hx.
      so (in_app_or _#4 Hx) as [Hin | Hin].
        { apply Ht; auto. }

        { apply Hf; auto. }
      }
    }
  }

  {
  exists t.
  do2 2 split; auto.
  intro; split; auto.
  }

  {
  exists f.
  do2 2 split; auto.
  intro; split; auto.
  }

  {
  intros w Hw.
  so (Ht w andel Hw) as ((_ & _ & Hv) & Hin).
  split; auto.
  apply Ha; auto.
  }

  {
  intros w Hw.
  so (Hf w andel Hw) as (Hw' & Hin).
  so (Ha _ ander Hin) as Helector.
  split; auto.
  destruct Helector as (Hwit & Hss).  
  so (stsees_impl_strict_ancestor _ _ Hss) as Hwy.
  so (Hvote _ Hwy Hwit) as (v & Hv).
  destruct v; auto.
  destruct Hw'.
  apply Ht; auto.
  }
Qed.  


Lemma vote_defined :
  forall s x y m n,
    rwitness m x
    -> rwitness n y
    -> m < n
    -> exists b, vote s x y b.
Proof.
intros s x y m n Hwitx Hwity Hlt.
revert n Hwity Hlt.
wfinduct y using strict_ancestor_well_founded.
intros y IH n Hwity Hlt.
so (le_dec n (m + first_regular)) as [Hge | Hnge].
  {
  so (strict_ancestor_decide x y) as [Hanc | Hnanc].
    {
    exists true.
    eapply vote_first; eauto.
    cbn.
    split; auto.
    }

    {
    exists false.
    eapply vote_first; eauto.
    cbn.
    split; auto.
    intro H; destruct H.
    }
  }
so (eq_nat_dec ((n - m) mod coin_freq) 0) as [Hcoin | Hnocoin].
2:{
  assert (m < pred n) as Hlt'.
    {
    so first_regular_min.
    omega.
    }
  so (fun w Hwy Hwitw => IH w Hwy (pred n) Hwitw Hlt') as IH'.
  so (election_defined (vote s x) (pred n) y (vote_fun s x) IH') as (t & f & Hvote).
  so (le_dec f t) as [Hle | Hgt].
    {
    exists true.
    eapply vote_regular; eauto.
    omega.
    }

    {
    exists false.
    assert (f > t) by omega.
    eapply vote_regular; eauto.
    omega.
    }
  }
assert (m < pred n) as Hlt'.
  {
  so first_regular_min.
  omega.
  }
so (fun w Hwy Hwitw => IH w Hwy (pred n) Hwitw Hlt') as IH'.
so (election_defined (vote s x) (pred n) y (vote_fun s x) IH') as (t & f & Hvote).
so (le_dec t (two_thirds total_stake)) as [Hle | Hgt].
2:{
  exists true.
  eapply vote_coin_super; eauto.
  omega.
  }
so (le_dec f (two_thirds total_stake)) as [Hle' | Hgt].
2:{
  exists false.
  eapply vote_coin_super; eauto.
  omega.
  }
exists (coin y s).
eapply vote_coin; eauto.
Qed.


Lemma election_defined' :
  forall s x m n y,
    rwitness m x
    -> m < n
    -> exists t f,
         election (vote s x) n y t f.
Proof.
intros s x m n y Hwitx Hmn.
apply election_defined.
  {
  apply vote_fun.
  }

  {
  intros.
  eapply vote_defined; eauto.
  }
Qed.
