(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Nat.
Require Import Omega.

Require Import Tact.
Require Import Decide.
Require Import Majority.
Require Import Relation.
Require Import HashgraphFacts.
Require Import Sees.


(** We differ from the technical report by making the first round 0, instead of 1.

   Also, we advance to round n+1 when an event strongly-sees an event in round n
   on 2/3 of the peers.  This differs from the technical report, which requires
   that the strongly-seen event be a witness.  The two formulations are equivalent
   because you can strongly-see a round-n witness on peer a iff you can strongly-see
   any round-n event on peer a.  Formulating it this way allows us to untangle the
   circularity between the definitions of round and witness.
*)

Inductive round : nat -> event -> Prop :=
| round_initial {x} :
    initial x
    -> round 0 x

| round_nadvance {x y z m n A} :
    parents y z x
    -> round m y
    -> round n z
    -> superminority stake A every
    -> (forall a w,
          A a
          -> creator w = a
          -> stsees w x
          -> exists i, i < max m n /\ round i w)
    -> round (max m n) x 

| round_advance {x y z m n A} :
    parents y z x
    -> round m y
    -> round n z
    -> supermajority stake A every
    -> (forall a,
          A a
          -> exists w,
               creator w = a
               /\ stsees w x
               /\ round (max m n) w)
    -> round (S (max m n)) x
.


(** The definition of nonterminating only says that a hashgraph
   receives events from a round >= n (for all n), but it is a consequence 
   (all_rounds_inhabited) that it receives events from every round.
*)
Definition nonterminating (G : world) :=
  forall m, exists n x,
     m <= n
     /\ round n x
     /\ member G x.


(** Lemma 5.13 *)
Lemma round_fun :
  forall x m n,
    round m x
    -> round n x
    -> m = n.
Proof.
intros x m n Hm Hn.
revert m n Hm Hn.
wfinduct x using strict_ancestor_well_founded.
intros x IH m n Hm Hn.
invertc Hm.

(** initial *)
{
intros Hinit <-.
invertc Hn.
  (** initial *)
  {
  intros; subst; auto.
  }

  (** nwitness *)
  {
  intros.
  destruct Hinit.
  eauto.
  }

  (** witness *)
  {
  intros.
  destruct Hinit.
  eauto.
  }
}

(** nwitness *)
{
intros y z m1 m2 A Hparents Hroundy Hroundz Hmin Hnwit <-.
invertc Hn.
  (** initial *)
  {
  intros Hinit _.
  destruct Hinit; eauto.
  }

  (** nwitness *)
  {
  intros y' z' n1 n2 _ Hparents' Hn1 Hn2 _ _ <-.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).
  f_equal.
    {
    eapply IH; eauto.
    apply plus_one.
    eapply parent1; eauto.
    }

    {
    eapply IH; eauto.
    apply plus_one.
    eapply parent2; eauto.
    }
  }

  (** witness *)
  {
  intros y' z' m1' m2' B Hparents' Hroundy' Hroundz' Hmaj Hwit _.
  exfalso.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).
  so (IH _ (plus_one _#4 (parent1 Hparents)) _ _ Hroundy Hroundy'); subst m1'.
  so (IH _ (plus_one _#4 (parent2 Hparents)) _ _ Hroundz Hroundz'); subst m2'.
  so (superminority_supermajority_intersect _#5 eq_peer_decide Hmin Hmaj) as (a & HA & HB).
  so (Hwit a HB) as (w & Hcreator & Hss & Hround).
  so (Hnwit a w HA Hcreator Hss) as (i & Hlt & Hround').
  so (IH _ (stsees_impl_strict_ancestor _ _ Hss) _ _ Hround Hround').
  omega.
  }
}

(** witness *)
{
intros y z m1 m2 A Hparents Hroundy Hroundz Hmaj Hwit <-.
invertc Hn.
  (** initial *)
  {
  intros Hinit _.
  destruct Hinit; eauto.
  }

  (** nwitness *)
  {
  intros y' z' m1' m2' B Hparents' Hroundy' Hroundz' Hmin Hnwit <-.
  exfalso.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).
  so (IH _ (plus_one _#4 (parent1 Hparents)) _ _ Hroundy Hroundy'); subst m1'.
  so (IH _ (plus_one _#4 (parent2 Hparents)) _ _ Hroundz Hroundz'); subst m2'.
  so (superminority_supermajority_intersect _#5 eq_peer_decide Hmin Hmaj) as (a & HA & HB).
  so (Hwit a HB) as (w & Hcreator & Hss & Hround).
  so (Hnwit a w HA Hcreator Hss) as (i & Hlt & Hround').
  so (IH _ (stsees_impl_strict_ancestor _ _ Hss) _ _ Hround Hround').
  omega.
  }

  (** witness *)
  {
  intros y' z' m1' m2' B Hparents' Hroundy' Hroundz' _ _ <-.
  so (parents_fun _#5 Hparents Hparents') as (<- & <-).
  so (IH _ (plus_one _#4 (parent1 Hparents)) _ _ Hroundy Hroundy'); subst m1'.
  so (IH _ (plus_one _#4 (parent2 Hparents)) _ _ Hroundz Hroundz'); subst m2'.
  reflexivity.
  }
}
Qed.


Lemma round_mono :
  forall x y m n,
    x @= y 
    -> round m x
    -> round n y
    -> m <= n.
Proof.
intros x y m n Hxy Hroundx Hroundy.
revert n Hxy Hroundy.
wfinduct y using parent_well_founded.
intros y IH n Hxy Hroundy.
so (star_plus _#4 Hxy) as [Heq | H].
  {
  subst y.
  so (round_fun _#3 Hroundx Hroundy).
  subst n.
  auto.
  }
fold (x @ y) in H.
renameover H into Hxy.
invert Hroundy.

(** initial *)
{
intros Hinit <-.
exfalso.
eapply strict_ancestor_initial; eauto.
}

(** nwitness *)
{
intros u v p q A Hparents Hroundu Hroundv Hmin Hnwit <-.
so (strict_ancestor_parents _#4 Hparents Hxy) as [Hxu | Hxv].
  {
  so (IH _ (parent1 Hparents) _ Hxu Hroundu).
  so (Nat.le_max_l p q).
  omega.
  }

  {
  so (IH _ (parent2 Hparents) _ Hxv Hroundv).
  so (Nat.le_max_r p q).
  omega.
  }
}

(** witness *)
{
intros u v p q A Hparents Hroundu Hroundv Hmaj Hwit <-.
so (strict_ancestor_parents _#4 Hparents Hxy) as [Hxu | Hxv].
  {
  so (IH _ (parent1 Hparents) _ Hxu Hroundu).
  so (Nat.le_max_l p q).
  omega.
  }

  {
  so (IH _ (parent2 Hparents) _ Hxv Hroundv).
  so (Nat.le_max_r p q).
  omega.
  }
}
Qed.


Lemma round_defined :
  forall x, exists n, round n x.
Proof.
intros x.
wfinduct x using strict_ancestor_well_founded.
intros x IH.
so (initial_decide x) as [Hinit | H].
  {
  exists 0.
  apply round_initial; auto.
  }
destruct H as (y & z & Hparents).
so (IH y (plus_one _#4 (parent1 Hparents))) as (m & Hroundy).
so (IH z (plus_one _#4 (parent2 Hparents))) as (n & Hroundz).
assert (forall a,
          decidable
          (exists w,
             creator w = a
             /\ stsees w x
             /\ round (max m n) w)) as Hdec.
  {
  intro a.
  apply (dec_exists_finite _ _ (fun y => y @ x)).
    {
    intros v Hv.
    destruct Hv as (_ & Hv & _).
    apply stsees_impl_strict_ancestor; auto.
    }

    {
    apply strict_ancestor_finite.
    }
  intros w.
  apply dec_and.
    { apply eq_peer_decide. }
  apply dec_and_dep.
    {
    apply stsees_decide.
    }
  intro Hss.
  so (IH _ (stsees_impl_strict_ancestor _ _ Hss)) as (l & Hround).
  so (dec_eq_nat l (max m n)) as [Heq | Hneq].
    {
    subst l.
    left; auto.
    }
  right.
  intros Hround'.
  so (round_fun _#3 Hround Hround').
  contradiction.
  }
eassert (_) as H; [refine (supermajority_decide _#5 Hdec _ the_total_stake) |].
  { unfold incl, every; auto. }
destruct H as [Hmaj | Hnmaj].  
  {
  exists (S (max m n)).
  eapply round_advance; eauto.
  }

  {
  exists (max m n).
  so (not_supermajority_every _#4 Hdec the_total_stake Hnmaj) as Hmin.
  eapply round_nadvance; eauto.
  cbn.
  intros a w Hnwit <- Hss.
  so (stsees_impl_strict_ancestor _ _ Hss) as Hwx.
  so (IH _ Hwx) as (i & Hround).
  exists i.
  split; auto.
  so (lt_eq_lt_dec i (max m n)) as [[Hlt | Heq]| Hlt]; auto.
    {
    subst i.
    destruct Hnwit.
    exists w.
    do2 2 split; auto.
    }
  exfalso.
  so (Nat.max_lub_lt_iff _#3 andel Hlt) as (Hltm & Hltn).
  so (strict_ancestor_parents _#4 Hparents Hwx) as [Hwy | Hwz].
    {
    so (round_mono _#4 Hwy Hround Hroundy).
    omega.
    }

    {
    so (round_mono _#4 Hwz Hround Hroundz).
    omega.
    }
  }
Qed.


Lemma round_decide :
  forall r x,
    decidable (round r x).
Proof.
intros r x.
so (round_defined x) as (r' & Hround).
so (dec_eq_nat r r') as [Heq | Hneq].
  {
  subst r'.
  left; auto.
  }
right.
contradict Hneq.
eapply round_fun; eauto.
Qed.


Definition earlier (x y : event) : Prop :=
  exists m n,
    round m x
    /\ round n y
    /\ m < n.


Notation "x << y" := (earlier x y)
  (at level 70, right associativity) : event_scope.


Lemma rounds_earlier :
  forall x y m n,
    round m x
    -> round n y
    -> m < n
    -> x << y.
Proof.
intros x y m n Hx Hy Hlt.
exists m, n.
auto.
Qed.


Lemma earlier_rounds :
  forall x y m n,
    x << y
    -> round m x
    -> round n y
    -> m < n.
Proof.
intros x y m n Hxy Hx Hy.
destruct Hxy as (m' & n' & Hx' & Hy' & Hlt).
so (round_fun _#3 Hx Hx'); subst m'.
so (round_fun _#3 Hy Hy'); subst n'.
exact Hlt.
Qed.


Lemma earlier_trans :
  forall x y z,
    x << y
    -> y << z
    -> x << z.
Proof.
intros x y z Hxy Hyz.
destruct Hxy as (m & n & Hx & Hy & Hmn).
destruct Hyz as (n' & p & Hy' & Hz & Hnp).
so (round_fun _#3 Hy Hy'); subst n'.
clear Hy Hy'.
eapply rounds_earlier; eauto.
omega.
Qed.


Definition witness (x : event) : Prop :=
  initial x
  \/ exists y, self_parent y x /\ y << x.


Lemma strict_self_ancestor_witness :
  forall x y m n,
    witness y
    -> x $ y
    -> round m x
    -> round n y
    -> m < n.
Proof.
intros x y m n Hwit Hxy Hroundx Hroundy.
destruct Hwit as [Hinit | H].
  {
  exfalso.
  eapply strict_ancestor_initial; eauto.
  apply strict_self_ancestor_impl_strict_ancestor; eauto.
  }
destruct H as (z & Hparent & Hzy).
destruct Hzy as (p & n' & Hroundz & Hroundy' & Hlt).
so (round_fun _#3 Hroundy Hroundy'); subst n'.
so (strict_self_ancestor_parent _#3 Hparent Hxy) as Hxz.
so (round_mono _#4 (self_ancestor_impl_ancestor _ _ Hxz) Hroundx Hroundz).
omega.
Qed.


Lemma witness_decide :
  forall x, decidable (witness x).
Proof.
intros x.
so (initial_decide x) as [Hinit | (y & z & Hparents)].
  {
  left.
  left; auto.
  }
assert (self_parent y x) as Hparent.
  {
  exists z; auto.
  }
so (round_defined y) as (m & Hroundy).
so (round_defined x) as (n & Hroundx).
so (lt_dec m n) as [Hlt | Hnlt].
  {
  left.
  right.
  do 3 eexists; eauto.
  }
right.
intro Hwitness.
so (strict_self_ancestor_witness _#4 Hwitness (plus_one _#4 Hparent) Hroundy Hroundx).
omega.
Qed.


Definition rwitness (n : nat) (x : event) : Prop :=
  round n x /\ witness x.


Lemma rwitness_witness :
  forall n x,
    rwitness n x
    -> witness x.
Proof.
intros n x H.
destruct H; auto.
Qed.


Lemma rwitness_fun :
  forall x m n,
    rwitness m x
    -> rwitness n x
    -> m = n.
Proof.
intros x m n (H & _) (H' & _).
eapply round_fun; eauto.
Qed.


Lemma rwitness_earlier :
  forall x y m n,
    rwitness m x
    -> rwitness n y
    -> m < n
    -> x << y.
Proof.
intros x y m n Hx Hy Hlt.
destruct Hx as (Hx & _).
destruct Hy as (Hy & _).
exists m, n.
auto.
Qed.


Lemma rwitness_decide :
  forall r x,
    decidable (rwitness r x).
Proof.
intros r x.
unfold rwitness.
apply dec_and.
  { apply round_decide. }

  { apply witness_decide. }
Qed.


(** Key corollary of the strongly-seeing lemma. *)
Lemma stseen_witness_unique :
  forall W n x y z z',
    member W z
    -> member W z'
    -> creator x = creator y
    -> rwitness n x
    -> rwitness n y
    -> stsees x z
    -> stsees y z'
    -> x = y.
Proof.
intros W n x y z z' Wz Wz' Heqcr Hwitx Hwity Hxz Hyz.
destruct Hwitx as (Hroundx & Hwitx).
destruct Hwity as (Hroundy & Hwity).
so (event_eq_dec x y) as [Heq | Hneq]; auto.
exfalso.
so (self_ancestor_decide x y) as [Hxy | Hnxy].
  {
  so (strict_self_ancestor_witness _#4 Hwity (star_neq_plus _#4 Hxy Hneq) Hroundx Hroundy).
  omega.
  }
so (self_ancestor_decide y x) as [Hyx | Hnyx].
  {
  assert (y <> x) as Hneq' by (contradict Hneq; auto).
  so (strict_self_ancestor_witness _#4 Hwitx (star_neq_plus _#4 Hyx Hneq') Hroundy Hroundx).
  omega.
  }
exfalso.
assert (fork x y) as Hfork.
  {
  do2 2 split; auto.
  }
eapply (strongly_seeing _#3 z z'); eauto.
Qed.


Lemma self_ancestor_witness :
  forall n x,
    round n x
    -> exists y, 
        y $= x
        /\ rwitness n y.
Proof.
intros n x.
wfinduct x using self_parent_well_founded.
intros x IH Hround.
invert Hround.

(** initial *)
{
intros Hinit <-.
exists x.
split.
  { apply star_refl. }
split; auto.
left; auto.
}

(** nwitness *)
{
intros y z l m _ Hparents Hroundy _ _ _ <-.
so (Nat.max_spec l m) as [(Hlt & Heq) | (_ & Heq)].
  {
  rewrite -> Heq in *.
  exists x.
  split; [apply star_refl |].
  split; auto.
  right.
  exists y.
  split; eauto using parents_self_parent.
  exists l, m.
  auto.
  }

  {
  rewrite -> Heq in *.
  so (IH y (parents_self_parent _#3 Hparents) Hroundy) as (w & Hwy & Hwit).
  exists w.
  split; auto.
  eapply star_trans; eauto.
  apply star_one.
  eapply parents_self_parent; eauto.
  }
}

(** witness *)
{
intros y z l m _ Hparents Hroundy _ _ _ <-.
exists x.
split; [apply star_refl |].
split; auto.
right.
exists y.
split.
  { eapply parents_self_parent; eauto. }
exists l, (S (max l m)).
do2 2 split; auto.
so (Nat.le_max_l l m).
omega.
}
Qed.


Lemma stsees_many_witnesses :
  forall n x,
    round (S n) x
    -> supermajority
         stake
         (fun a => 
            exists w, 
              creator w = a
              /\ stsees w x
              /\ rwitness n w)
         every.
Proof.
intros n x Hround.
revert Hround.
wfinduct x using parent_well_founded.
intros x IH Hround.
assert (forall a, decidable (exists w, creator w = a /\ stsees w x /\ rwitness n w)) as Hdec.
  {
  intro a.
  apply (dec_exists_finite _ _ (fun w => w @= x)).
    {
    intros w H.
    destruct H as (_ & H & _).
    apply stsees_impl_ancestor; auto.
    }

    {
    apply ancestor_finite.
    }
  intro w.
  apply dec_and.
    { apply eq_peer_decide. }
  apply dec_and.
    { apply stsees_decide. }

    { apply rwitness_decide. }
  }
invert Hround.

(** nwitness *)
{
intros y z l m _ Hparents Hroundy Hroundz _ _ Heq.
so (Nat.max_spec l m) as [(_ & Heqm) | (_ & Heql)].
  {
  rewrite -> Heqm in Heq.
  subst m.
  so (IH z (parent2 Hparents) Hroundz) as Hmaj.
  eapply supermajority_enlarge; eauto.
  intros a Ha.
  destruct Ha as (w & Heqcr & Hss & Hrwit).
  exists w.
  do2 2 split; auto.
  eapply stsees_ancestor_trans; eauto.
  apply star_one.
  eapply parent2; eauto.
  }

  {
  rewrite -> Heql in Heq.
  subst l.
  so (IH y (parent1 Hparents) Hroundy) as Hmaj.
  eapply supermajority_enlarge; eauto.
  intros a Ha.
  destruct Ha as (w & Heqcr & Hss & Hrwit).
  exists w.
  do2 2 split; auto.
  eapply stsees_ancestor_trans; eauto.
  apply star_one.
  eapply parent1; eauto.
  }
}

(** witness *)
{
intros _ _ l m A _ _ _ Hmaj HA Heq.
eapply supermajority_enlarge; eauto.
intros a Ha.
so (HA a Ha) as (w & Heqcr & Hss & Hwitw).
rewrite -> Heq in Hwitw.
so (self_ancestor_witness _ _ Hwitw) as (u & Huw & Hwitu).
exists u.
do2 2 split; auto.
  {
  transitivity (creator w); eauto.
  apply self_ancestor_creator; auto.
  }

  {
  eapply self_ancestor_stsees_trans; eauto.
  }
}
Qed.


Lemma ancestor_witness :
  forall m n x,
    m <= n
    -> round n x
    -> exists y, y @= x /\ rwitness m y.
Proof.
intros m n x Hle Hroundx.
revert n Hle Hroundx.
wfinduct x using strict_ancestor_well_founded.
intros x IH n Hle Hroundx.
so (self_ancestor_witness _ _ Hroundx) as (y & Hyx & Hwit).
so (le_lt_eq_dec _ _ Hle) as [Hlt | Heq].

(** succ *)
{
so (Hwit andel) as Hroundy.
invert Hroundy.
  (** initial *)
  {
  intros _ <-.
  omega.
  }

  (** nadvance *)
  {
  intros u w j k _ Hparents Hroundu Hroundw _ _ <-.
  so (Nat.max_spec j k) as [(_ & Heq) | (_ & Heq)].
    {
    rewrite -> Heq in *.
    assert (w @ x) as Hwx.
      {
      exists y.
      split.
        { eapply parent2; eauto. }

        { apply self_ancestor_impl_ancestor; auto. }
      }
    exploit (fun H => IH w H k) as H; auto.
    destruct H as (z & Hzw & Hwitz).
    exists z; split; auto.
    apply plus_star.
    eapply star_plus_trans; eauto.
    }

    {
    rewrite -> Heq in *.
    assert (u @ x) as Hux.
      {
      exists y.
      split.
        { eapply parent1; eauto. }

        { apply self_ancestor_impl_ancestor; auto. }
      }
    exploit (fun H => IH u H j) as H; auto.
    destruct H as (z & Hzu & Hwitz).
    exists z; split; auto.
    apply plus_star.
    eapply star_plus_trans; eauto.
    }
  }

  (** advance *)
  {
  intros u w j k _ Hparents Hroundu Hroundw _ _ <-.
  so (Nat.max_spec j k) as [(_ & Heq) | (_ & Heq)].
    {
    rewrite -> Heq in *.
    assert (w @ x) as Hwx.
      {
      exists y.
      split.
        { eapply parent2; eauto. }

        { apply self_ancestor_impl_ancestor; auto. }
      }
    exploit (fun H => IH w H k) as H; auto.
      { omega. }
    destruct H as (z & Hzw & Hwitz).
    exists z; split; auto.
    apply plus_star.
    eapply star_plus_trans; eauto.
    }

    {
    rewrite -> Heq in *.
    assert (u @ x) as Hux.
      {
      exists y.
      split.
        { eapply parent1; eauto. }

        { apply self_ancestor_impl_ancestor; auto. }
      }
    exploit (fun H => IH u H j) as H; auto.
      { omega. }
    destruct H as (z & Hzu & Hwitz).
    exists z; split; auto.
    apply plus_star.
    eapply star_plus_trans; eauto.
    }
  }
}

(** eq *)
{
subst n.
exists y; split; auto.
apply self_ancestor_impl_ancestor; auto.
}
Qed.


Lemma all_rounds_inhabited :
  forall W n,
    nonterminating W
    -> exists x, rwitness n x /\ member W x.
Proof.
intros W n Hnt.
so (Hnt n) as (m & x & Hle & Hroundx & HGx).
so (ancestor_witness _#3 Hle Hroundx) as (y & Hxy & Hwity).
exists y.
split; auto.
eapply world_closed; eauto.
Qed.


Lemma honest_witness_unique :
  forall W n x y,
    member W x
    -> member W y
    -> honest (creator x)
    -> creator x = creator y
    -> rwitness n x
    -> rwitness n y
    -> x = y.
Proof.
intros W n x y Wx Wy Hhonest Heqcr Hwitx Hwity.
so (eq_event_decide x y) as [| Hneq]; auto.
exfalso.
destruct (world_forks W _ Hhonest).
destruct Hwitx as (Hroundx & Hwitx).
destruct Hwity as (Hroundy & Hwity).
exists x, y.
do2 3 split; auto.
do2 2 split; auto.
  {
  intros Hxy.
  so (star_neq_plus _#4 Hxy Hneq) as Hxy'.
  so (strict_self_ancestor_witness _#4 Hwity Hxy' Hroundx Hroundy).
  omega.
  }

  {
  intros Hxy.
  eassert _ as Hxy'; [refine (star_neq_plus _#4 Hxy _) |].
    {
    contradict Hneq; auto.
    }
  so (strict_self_ancestor_witness _#4 Hwitx Hxy' Hroundy Hroundx).
  omega.
  }
Qed.
