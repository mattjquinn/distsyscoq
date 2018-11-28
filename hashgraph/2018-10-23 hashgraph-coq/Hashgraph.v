(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Bool.
Require Import List.
Require Import Omega.

Require Import Tact.
Require Import Relation.
Require Import Decide.
Require Import Cardinality.
Require Import Weight.
Require Import Majority.


(** Peers *)

Parameter number_peers : nat.

Axiom number_peers_minimum : number_peers >= 3.



Parameter peer : Type.

Axiom peer_eq_dec : forall (a b : peer), {a = b} + {a <> b}.

Axiom number_of_peers : cardinality (@every peer) number_peers.



Parameter stake : peer -> nat.

Axiom stake_positive : forall a, stake a > 0.

Axiom no_majority_stake : forall a, ~ majority stake (eq a) every.



Parameter total_stake : nat.

Axiom the_total_stake : weight stake every total_stake.



Parameter honest : peer -> Prop.

Axiom supermajority_honest : supermajority stake honest every.

Axiom distinct_honest_peers : exists a b, honest a /\ honest b /\ a <> b.



(** Events *)

Parameter event : Type.

Axiom event_eq_dec : forall (e f : event), {e = f} + {e <> f}.

Parameter creator : event -> peer.

(** parents e f g = e and f are the parents of g *)
Parameter parents : event -> event -> event -> Prop.

Axiom parents_fun :
  forall e e' f f' g,
    parents e f g
    -> parents e' f' g
    -> e = e' /\ f = f'.

(** The first parent is the self-parent *)
Axiom parents_creator :
  forall e f g,
    parents e f g
    -> creator e = creator g.

Definition initial (e : event) : Prop :=
  ~ exists f g, parents f g e.

Axiom initial_decide :
  forall e,
    initial e \/ exists f g, parents f g e.




(** Ancestors *)

(** Note that the child appears second, as opposed to first in parents. *)
Inductive parent : event -> event -> Prop :=
| parent1 {e f g} :
    parents e f g
    -> parent e g

| parent2 {e f g} :
    parents e f g
    -> parent f g.

Axiom parent_well_founded : well_founded parent.

Definition self_parent (e f : event) : Prop :=
  exists g, parents e g f.


Definition ancestor := star parent.
Definition strict_ancestor := plus parent.
Definition self_ancestor := star self_parent.
Definition strict_self_ancestor := plus self_parent.

Notation "e @ f" := (strict_ancestor e f)
  (at level 70, right associativity) : event_scope.

Notation "e @= f" := (ancestor e f)
  (at level 70, right associativity) : event_scope.

Notation "e $ f" := (strict_self_ancestor e f)
  (at level 70, right associativity) : event_scope.

Notation "e $= f" := (self_ancestor e f)
  (at level 70, right associativity) : event_scope.

Open Scope event_scope.



(** Forks *)

Definition fork (e f : event) : Prop :=
  creator e = creator f
  /\ ~ e $= f
  /\ ~ f $= e.



(** Spawn order, inaccessible to all but the adversary. *)

Parameter sample : Type.

Parameter spawn : sample -> nat -> event.

Axiom spawn_inj :
  forall s i j, spawn s i = spawn s j -> i = j.

Axiom spawn_parent :
  forall s x i,
    parent x (spawn s i)
    -> exists j, x = spawn s j /\ j < i.

Axiom spawn_forks :
  forall s i j,
    honest (creator (spawn s i))
    -> fork (spawn s i) (spawn s j)
    -> False.

Axiom no_orphans : forall x, exists s i, x = spawn s i.

(** Eventually every honest peer synchronizes with every other honest peer. *)
Axiom honest_peers_sync :
  forall s i a b,
    honest a
    -> honest b
    -> a <> b
    -> exists j k,
         i <= j
         /\ j <= k
         /\ creator (spawn s j) = a
         /\ creator (spawn s k) = b
         /\ spawn s j @ spawn s k.


Definition realtime s x y :=
  exists i j,
    x = spawn s i
    /\ y = spawn s j
    /\ i <= j.


Lemma realtime_member :
  forall s x y,
    realtime s x y
    -> realtime s x x /\ realtime s y y.
Proof.
intros s x y H.
destruct H as (i & j & -> & -> & _).
split.
  {
  exists i, i.
  do2 2 split; auto.
  }

  {
  exists j, j.
  do2 2 split; auto.
  }
Qed.


Lemma realtime_trans : forall s, transitive event (realtime s).
Proof.
intros s.
intros x y z Hxy Hyz.
destruct Hxy as (i & j & -> & -> & Hij).
destruct Hyz as (j' & k & Heq & -> & Hjk).
so (spawn_inj _#3 Heq); subst j'.
exists i, k.
do2 2 split; auto.
omega.
Qed.


Lemma realtime_antisym : forall s, antisymmetric event (realtime s).
Proof.
intros s x y Hxy Hyx.
destruct Hxy as (i & j & -> & -> & Hij).
destruct Hyx as (j' & i' & Hj & Hi & Hji).
so (spawn_inj _#3 Hi); subst i'.
so (spawn_inj _#3 Hj); subst j'.
f_equal.
omega.
Qed.


Lemma realtime_parent :
  forall s x y,
    realtime s y y
    -> parent x y
    -> realtime s x y.
Proof.
intros s x y Hyy Hparent.
destruct Hyy as (i & _ & -> & _).
so (spawn_parent _#3 Hparent) as (j & -> & Hlt).
exists j, i.
do2 2 split; auto.
omega.
Qed.


Lemma ancestor_realtime :
  forall s x y,
    realtime s y y
    -> x @= y
    -> realtime s x y.
Proof.
intros s x y Hy Hxy.
so (star_starr _#4 Hxy) as H.
clear Hxy.
revert Hy.
induct H.

(** refl *)
{
auto.
}

(** step *)
{
intros x y z _ IH Hyz Hz.
assert (realtime s y z) as Hyz'.
  {
  eapply realtime_parent; eauto.
  }
apply (realtime_trans _ _ y); auto.
apply IH.
apply (realtime_member s y z); auto.
}
Qed.


(** World *)

Record world : Type :=
mk_world
  { member : event -> Prop;

    world_closed :
      forall x y, x @= y -> member y -> member x;

    world_forks :
      forall a,
        honest a
        -> ~ exists e f, member e /\ member f /\ fork e f /\ creator e = a
  }.


Definition extends (W W' : world) :=
  incl (member W) (member W').


Definition global (s : sample) : world.
Proof.
apply (mk_world (fun x => realtime s x x)).

(** closed *)
{
intros x y Hxy Hy.
so (ancestor_realtime _#3 Hy Hxy) as Hxy'.
apply (realtime_member s x y); auto.
}

(** forks *)
{
intros a Ha.
intros (y & z & Hy & Hz & Hfork & Heqcr).
subst a.
destruct Hy as (j & _ & -> & _).
destruct Hz as (k & _ & -> & _).
apply (spawn_forks s j k); auto.
}
Defined.



(** Hashgraphs are worlds.  By the definition, there is no differences between a
   hashgraph and a world, but we reserve the term hashgraph to refer to an 
   individual peer's view of the world.
   
   Note that an event incorporates its lineage, so hashgraphs are necessarily
   consistent.  Thus, we have no explicit definition of consistent hashgraphs.
*)



(** Round parameters *)  

(** First round after an event is created in which the witnesses vote on its fame. *)
Parameter first_regular : nat.

Axiom first_regular_min : first_regular >= 2.

(** How often coin rounds take place. *)
Parameter coin_freq : nat.

Axiom coin_freq_min : coin_freq > 2 + first_regular.



(** Timestamps and textual order *)

Parameter timestamp : event -> nat.

Parameter textorder : event -> event -> bool.

Axiom textorder_order :
  order event (fun x y => Is_true (textorder x y)).

Axiom textorder_total :
  forall x y,
    Is_true (textorder x y) \/ Is_true (textorder y x).



(** Pseudo-probability *)

(** The arbitrary decision rendered by an event in a coin round. *)
Parameter coin : event -> sample -> bool.


(** The samples agree on events before (or equal to) i,
   and their coins (strictly) before i
*)
Definition similar (s s' : sample) (i : nat) :=
  (forall j, j <= i -> spawn s j = spawn s' j)
  /\
  (forall j, j < i -> coin (spawn s j) s = coin (spawn s j) s').


(** If  (1) f is a sequence of disjoint sets of honest events, each of size less than n,
   and (2) P is a sequence of predicates such that P_i depends only on events
           earlier than every event in f_i,
   then there exists some i such that all of f_i's events' coins agree with P_i
*)
Axiom eventual_agreement :
  forall
  (n : nat)
  (s : sample)
  (Q : nat -> event -> Prop)
  (P : nat -> sample -> Prop),
    (forall i j x, Q i x -> Q j x -> i = j)
    -> (forall i x, Q i x -> honest (creator x))
    -> (forall i, cardinality_lt (Q i) n)
    -> (forall i k s', Q i (spawn s k) -> similar s s' k -> P i s <-> P i s')
    -> exists i v,
         (forall x, Q i x -> coin x s = v)
         /\ (Is_true v <-> P i s).
