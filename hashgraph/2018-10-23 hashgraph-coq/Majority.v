(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Nat.
Require Import List.
Require Import Decide.
Require Import Omega.

Require Import Tact.
Require Import Weight.
Require Import Calculate.


Definition every {T : Type} : T -> Prop := fun _ => True.


Lemma incl_every :
  forall T (P : T -> Prop), incl P every.
Proof.
intros T P.
unfold incl, every; auto.
Qed.

Hint Resolve incl_every.


Definition majority {T : Type} (f : T -> nat) (P Q : T -> Prop) :=
  exists m n,
    incl P Q
    /\ weight f P m
    /\ weight f Q n
    /\ m > one_half n.


Definition supermajority {T : Type} (f : T -> nat) (P Q : T -> Prop) :=
  exists m n,
    incl P Q
    /\ weight f P m
    /\ weight f Q n
    /\ m > two_thirds n.


(** enough to deny a supermajority *)
Definition superminority {T : Type} (f : T -> nat) (P Q : T -> Prop) :=
  exists m n,
    incl P Q
    /\ weight f P m
    /\ weight f Q n
    /\ m >= one_third n.


(** enough to deny a majority *)
Definition atleasthalf {T : Type} (f : T -> nat) (P Q : T -> Prop) :=
  exists m n,
    incl P Q
    /\ weight f P m
    /\ weight f Q n
    /\ m >= one_half (S n).




(** Manipulations *)

Lemma majority_incl :
  forall (T : Type) (f : T -> nat) (P Q : T -> Prop),
    majority f P Q
    -> incl P Q.
Proof.
intros T f P Q H.
destruct H as (_ & _ & H & _).
exact H.
Qed.


Lemma unanimous_supermajority :
  forall T (f : T -> nat) (P : T -> Prop) n,
    n > 0
    -> weight f P n
    -> supermajority f P P.
Proof.
intros T f P n Hcard.
exists n, n.
do2 3 split; auto.
  { intro; auto. }

  { apply two_thirds_lt; auto. }
Qed.


Lemma supermajority_impl_majority :
  forall (T : Type) (f : T -> nat) (P U : T -> Prop),
    supermajority f P U
    -> majority f P U.
Proof.
intros T f P U Hmaj.
destruct Hmaj as (m & n & Hincl & HcardP & HcardU & Hgt).
exists m, n.
do2 3 split; auto.
unfold two_thirds in Hgt.
unfold one_half.
so (Nat.div_mod n 2 (Nat.neq_succ_0 _)) as Hmod2.
so (Nat.div_mod (2 * n) 3 (Nat.neq_succ_0 _)) as Hmod3.
rewrite -> (Nat.mul_mod 2 n 3 (Nat.neq_succ_0 _)) in Hmod3.
replace (2 mod 3) with 2 in Hmod3 by reflexivity.
remember (n mod 3) as w eqn:Heqw.
destruct w as [|[|[|]]];
autorewrite with mod3 in Hmod3; try omega.
exfalso.
so (Nat.mod_upper_bound n 3 (Nat.neq_succ_0 _)).
omega.
Qed.



Lemma majority_impl_superminority :
  forall (T : Type) (f : T -> nat) (P U : T -> Prop),
    majority f P U
    -> superminority f P U.
Proof.
intros T f P U Hmaj.
destruct Hmaj as (m & n & Hincl & HcardP & HcardU & Hgt).
exists m, n.
do2 3 split; auto.
unfold one_half in Hgt.
unfold one_third, two_thirds.
so (Nat.div_mod n 2 (Nat.neq_succ_0 _)) as Hmod2.
so (Nat.div_mod (2 * n) 3 (Nat.neq_succ_0 _)) as Hmod3.
rewrite -> (Nat.mul_mod 2 n 3 (Nat.neq_succ_0 _)) in Hmod3.
replace (2 mod 3) with 2 in Hmod3 by reflexivity.
remember (n mod 2) as v eqn:Heqv.
remember (n mod 3) as w eqn:Heqw.
destruct v as [|[|]]; [destruct w as [|[|[|]]] .. |];
autorewrite with mod3 in Hmod3; try omega; exfalso.
  {
  so (Nat.mod_upper_bound n 3 (Nat.neq_succ_0 _)).
  omega.
  }

  {
  so (Nat.mod_upper_bound n 3 (Nat.neq_succ_0 _)).
  omega.
  }

  {
  so (Nat.mod_upper_bound n 2 (Nat.neq_succ_0 _)).
  omega.
  }
Qed.


Lemma majority_enlarge :
  forall (T : Type) (f : T -> nat) (P Q U : T -> Prop),
    incl P Q
    -> incl Q U
    -> (forall x, U x -> decidable (Q x))
    -> majority f P U
    -> majority f Q U.
Proof.
intros T t P Q U HPQ HQU Hdec Hmaj.
destruct Hmaj as (m & n & _ & HcardP & HcardU & Hgt).
so (weight_subset _#5 Hdec HQU HcardU) as (l & HcardQ & _).
so (weight_incl _#6 HPQ HcardP HcardQ) as Hml.
exists l, n.
do2 3 split; auto.
omega.
Qed.  
          

Lemma supermajority_enlarge :
  forall (T : Type) (f : T -> nat)  (P Q U : T -> Prop),
    incl P Q
    -> incl Q U
    -> (forall x, U x -> decidable (Q x))
    -> supermajority f P U
    -> supermajority f Q U.
Proof.
intros T f P Q U HPQ HQU Hdec Hmaj.
destruct Hmaj as (m & n & _ & HcardP & HcardU & Hgt).
so (weight_subset _#5 Hdec HQU HcardU) as (l & HcardQ & _).
so (weight_incl _#6 HPQ HcardP HcardQ) as Hml.
exists l, n.
do2 3 split; auto.
omega.
Qed.  


Lemma supermajority_iff :
  forall (T : Type) (f : T -> nat) (P Q U : T -> Prop),
    (forall x, P x <-> Q x)
    -> supermajority f P U
    -> supermajority f Q U.
Proof.
intros T f P Q U Hiff Hmaj.
destruct Hmaj as (m & n & HPU & HcardP & HcardU & Hgt).
exists m, n.
do2 3 split; auto.
  {
  intros x Hx.
  apply HPU.
  apply Hiff; auto.
  }
destruct HcardP as (p & Hdistp & Hp & Hlenp).
exists p.
do2 2 split; auto.
intros x.
split.
  {
  intro Hx.
  apply Hp.
  apply Hiff; auto.
  }

  {
  intro Hx.
  apply Hiff.
  apply Hp; auto.
  }
Qed.


(** Intersections *)

Lemma majority_intersect :
  forall T (f : T -> nat) (P Q U : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> majority f P U
    -> majority f Q U
    -> exists x, P x /\ Q x.
Proof.
intros T f P Q U Hdeceq HP HQ.
destruct HP as (np & nu & HPU & HcardP & HcardU & Hgt).
destruct HQ as (nq & nu' & HQU & HcardQ & HcardU' & Hgt').
so (weight_fun _#5 HcardU HcardU').
subst nu'.
clear HcardU'.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
destruct HcardQ as (q & Hdistq & Hq & Hlenq).
destruct HcardU as (u & Hdistu & Hu & Hlenu).
exploit (inclusion_exclusion _ f p q u) as H; auto.
  {
  intros x Hx.
  apply Hu.
  apply HPU.
  apply Hp; auto.
  }

  {
  intros x Hx.
  apply Hu.
  apply HQU.
  apply Hq; auto.
  }
destruct H as (r & Hdistr & Hrp & Hrq & Hlen).
assert (sumweight f r > 0) as Hlen'.
  {
  unfold one_half in Hgt, Hgt'.
  subst np nq nu.
  so (majority_intersect_calculation _#3 Hgt Hgt').
  omega.
  }
destruct r as [| x r'].
  {
  simpl in Hlen'.
  omega.
  }
exists x.
split.
  {
  apply Hp.
  apply Hrp.
  left; auto.
  }

  {
  apply Hq.
  apply Hrq.
  left; auto.
  }
Qed.


Lemma majority_atleasthalf_intersect :
  forall T (f : T -> nat) (P Q U : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> majority f P U
    -> atleasthalf f Q U
    -> exists x, P x /\ Q x.
Proof.
intros T f P Q U Hdeceq HP HQ.
destruct HP as (np & nu & HPU & HcardP & HcardU & Hgt).
destruct HQ as (nq & nu' & HQU & HcardQ & HcardU' & Hgt').
so (weight_fun _#5 HcardU HcardU').
subst nu'.
clear HcardU'.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
destruct HcardQ as (q & Hdistq & Hq & Hlenq).
destruct HcardU as (u & Hdistu & Hu & Hlenu).
exploit (inclusion_exclusion _ f p q u) as H; auto.
  {
  intros x Hx.
  apply Hu.
  apply HPU.
  apply Hp; auto.
  }

  {
  intros x Hx.
  apply Hu.
  apply HQU.
  apply Hq; auto.
  }
destruct H as (r & Hdistr & Hrp & Hrq & Hlen).
assert (sumweight f r > 0) as Hlen'.
  {
  unfold one_half in Hgt, Hgt'.
  subst np nq nu.
  so (majority_atleasthalf_intersect_calculation _#3 Hgt Hgt').
  omega.
  }
destruct r as [| x r'].
  {
  simpl in Hlen'.
  omega.
  }
exists x.
split.
  {
  apply Hp.
  apply Hrp.
  left; auto.
  }

  {
  apply Hq.
  apply Hrq.
  left; auto.
  }
Qed.


Lemma supermajority_intersect_2 :
  forall T (f : T -> nat) (P Q U : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> supermajority f P U
    -> supermajority f Q U
    -> exists R,
         majority f R P
         /\ majority f R Q.
Proof.
intros T f P Q U Hdeceq HP HQ.
destruct HP as (np & nu & HPU & HcardP & HcardU & Hgt).
destruct HQ as (nq & nu' & HQU & HcardQ & HcardU' & Hgt').
so (weight_fun _#5 HcardU HcardU').
subst nu'.
clear HcardU'.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
destruct HcardQ as (q & Hdistq & Hq & Hlenq).
destruct HcardU as (u & Hdistu & Hu & Hlenu).
exploit (inclusion_exclusion _ f p q u) as H; auto.
  {
  intros x Hx.
  apply Hu.
  apply HPU.
  apply Hp; auto.
  }

  {
  intros x Hx.
  apply Hu.
  apply HQU.
  apply Hq; auto.
  }
destruct H as (r & Hdistr & Hrp & Hrq & Hlen).
exists (fun x => In x r).
split.
  {
  exists (sumweight f r), (sumweight f p).
  do2 3 split.
    {
    intros y Hy.
    apply Hp.
    apply Hrp; auto.
    }

    {
    exists r.
    do2 2 split; auto.
    intro; split; auto.
    }

    {
    exists p.
    do2 2 split; auto.
    }

    {
    unfold one_half.
    unfold two_thirds in Hgt, Hgt'.
    subst np nq nu.
    so (supermajority_intersect_2_calculation _#3 Hgt Hgt').
    omega.
    }
  }

  {
  exists (sumweight f r), (sumweight f q).
  do2 3 split.
    {
    intros y Hy.
    apply Hq.
    apply Hrq; auto.
    }

    {
    exists r.
    do2 2 split; auto.
    intro; split; auto.
    }

    {
    exists q.
    do2 2 split; auto.
    }

    {
    unfold one_half.
    unfold two_thirds in Hgt, Hgt'.
    subst np nq nu.
    so (supermajority_intersect_2_calculation _#3 Hgt' Hgt).
    omega.
    }
  }
Qed.


Lemma supermajority_intersect_2' :
  forall T (f : T -> nat) (P Q U : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> supermajority f P U
    -> supermajority f Q U
    -> majority f (fun x => P x /\ Q x) P
       /\ majority f (fun x => P x /\ Q x) Q.
Proof.
intros T f P Q U Hdeceq HP HQ.
so (supermajority_intersect_2 _#5 Hdeceq HP HQ) as (R & HmajP & HmajQ).
assert (incl R (fun x => P x /\ Q x)) as Hincl.
  {
  intros x Hx.
  split.
    {
    eapply majority_incl; eauto.
    }

    {
    eapply majority_incl; eauto.
    }
  }
split.
  {
  apply (majority_enlarge _ _ R); auto.
    {
    intros x (H & _).
    auto.
    }

    {
    intros x Hx.
    apply dec_and.
      {
      left; auto.
      }

      {
      apply finite_decide; auto.
      destruct HQ as (n & _ & _ & Hcard & _).
      eapply weight_finite; eauto.
      }
    }
  }

  {
  apply (majority_enlarge _ _ R); auto.
    {
    intros x (_ & H).
    auto.
    }

    {
    intros x Hx.
    apply dec_and.
      {
      apply finite_decide; auto.
      destruct HP as (n & _ & _ & Hcard & _).
      eapply weight_finite; eauto.
      }

      {
      left; auto.
      }
    }
  }
Qed.


Lemma supermajority_intersect_3 :
  forall T (f : T -> nat) (P Q R U : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> supermajority f P U
    -> supermajority f Q U
    -> supermajority f R U
    -> exists x, P x /\ Q x /\ R x.
Proof.
intros T f P Q R U Hdeceq HP HQ HR.
destruct HP as (np & nu & HPU & HcardP & HcardU & HgtP).
destruct HQ as (nq & nu' & HQU & HcardQ & HcardU' & HgtQ).
destruct HR as (nr & nu'' & HRU & HcardR & HcardU'' & HgtR).
so (weight_fun _#5 HcardU HcardU').
so (weight_fun _#5 HcardU HcardU'').
subst nu' nu''.
clear HcardU' HcardU''.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
destruct HcardQ as (q & Hdistq & Hq & Hlenq).
destruct HcardR as (r & Hdistr & Hr & Hlenr).
destruct HcardU as (u & Hdistu & Hu & Hlenu).
exploit (inclusion_exclusion _ f p q u) as H; auto.
  {
  intros x Hx.
  apply Hu.
  apply HPU.
  apply Hp; auto.
  }

  {
  intros x Hx.
  apply Hu.
  apply HQU.
  apply Hq; auto.
  }
destruct H as (s & Hdists & Hsp & Hsq & Hlens).
exploit (inclusion_exclusion _ f s r u) as H; auto.
  {
  intros x Hx.
  apply Hu.
  apply HPU.
  apply Hp.
  apply Hsp.
  auto.
  }

  {
  intros x Hx.
  apply Hu.
  apply HRU.
  apply Hr.
  auto.
  }
destruct H as (t & Hdistt & Hts & Htr & Hlent).
assert (sumweight f t > 0) as Hlen.
  {
  unfold two_thirds in HgtP, HgtQ, HgtR.
  subst np nq nr nu.
  so (supermajority_intersect_3_calculation _#4 HgtP HgtQ HgtR).
  omega.
  }
destruct t as [| x l].
  {
  exfalso.
  cbn in Hlen.
  omega.
  }
exists x.
do2 2 split.
  {
  apply Hp.
  apply Hsp.
  apply Hts.
  left; auto.
  }

  {
  apply Hq.
  apply Hsq.
  apply Hts.
  left; auto.
  }

  {
  apply Hr.
  apply Htr.
  left; auto.
  }
Qed.


Lemma superminority_supermajority_intersect :
  forall T (f : T -> nat) (P Q U : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> superminority f P U
    -> supermajority f Q U
    -> exists x, P x /\ Q x.
Proof.
intros T f P Q U Hdeceq HP HQ.
destruct HP as (np & nu & HPU & HcardP & HcardU & Hgt).
destruct HQ as (nq & nu' & HQU & HcardQ & HcardU' & Hgt').
so (weight_fun _#5 HcardU HcardU').
subst nu'.
clear HcardU'.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
destruct HcardQ as (q & Hdistq & Hq & Hlenq).
destruct HcardU as (u & Hdistu & Hu & Hlenu).
exploit (inclusion_exclusion _ f p q u) as H; auto.
  {
  intros x Hx.
  apply Hu.
  apply HPU.
  apply Hp; auto.
  }

  {
  intros x Hx.
  apply Hu.
  apply HQU.
  apply Hq; auto.
  }
destruct H as (r & Hdistr & Hrp & Hrq & Hlen).
assert (sumweight f r > 0) as Hlen'.
  {
  unfold one_third in Hgt.
  unfold two_thirds in Hgt'.
  subst np nq nu.
  so (superminority_supermajority_intersect_calculation _#3 Hgt Hgt').
  omega.
  }
destruct r as [| x r'].
  {
  simpl in Hlen'.
  omega.
  }
exists x.
split.
  {
  apply Hp.
  apply Hrp.
  left; auto.
  }

  {
  apply Hq.
  apply Hrq.
  left; auto.
  }
Qed.


Lemma majority_decide :
  forall (T : Type) (f : T -> nat) (P U : T -> Prop) n,
    (forall x, decidable (P x))
    -> incl P U
    -> weight f U n
    -> decidable (majority f P U).
Proof.
intros T f P U n Hdec HPU HcardU.
so (weight_gt_decide _#5 (one_half n) Hdec HPU HcardU) as [H | H].
  {
  destruct H as (m & HcardP & Hgt).
  left.
  exists m, n.
  do2 3 split; auto.
  }

  {
  right.
  contradict H.
  destruct H as (m & n' & _ & HcardP & HcardU' & Hgt).
  so (weight_fun _#5 HcardU HcardU'); subst n'.
  exists m.
  split; auto.
  }
Qed.


Lemma supermajority_decide :
  forall (T : Type) (f : T -> nat) (P U : T -> Prop) n,
    (forall x, decidable (P x))
    -> incl P U
    -> weight f U n
    -> decidable (supermajority f P U).
Proof.
intros T f P U n Hdec HPU HcardU.
so (weight_gt_decide _#5 (two_thirds n) Hdec HPU HcardU) as [H | H].
  {
  destruct H as (m & HcardP & Hgt).
  left.
  exists m, n.
  do2 3 split; auto.
  }

  {
  right.
  contradict H.
  destruct H as (m & n' & _ & HcardP & HcardU' & Hgt).
  so (weight_fun _#5 HcardU HcardU'); subst n'.
  exists m.
  split; auto.
  }
Qed.


Lemma not_supermajority :
  forall T (f : T -> nat) (P U : T -> Prop) n,
    (forall x, decidable (P x))    
    -> incl P U
    -> weight f U n
    -> ~ supermajority f P U
    -> superminority f (fun x => ~ P x /\ U x) U.
Proof.
intros T f P U n Hdec HPU HcardU Hnmaj.
so HcardU as (u & Hdistu & Hu & Hlenu).
so (enumerate_subset _ _ u (fun x _ => dec_not _ (Hdec x)) Hdistu) as (p & Hdistp & Hp).
exists (sumweight f p), n.
do2 3 split; auto.
  {
  intros x Hx.
  destruct Hx; auto.
  }

  {
  exists p.
  do2 2 split; auto.
  intros x.
  split.
    {
    intros (Hx & HxU).
    apply Hp.
    split; auto.
    apply Hu; auto.
    }

    {
    intros Hx.
    split.
      {
      apply Hp; auto.
      }

      {
      apply Hu.
      apply Hp; auto.
      }
    }
  }
so (le_lt_dec (one_third n) (sumweight f p)) as [Hle | Hlt]; auto.
exfalso.
destruct Hnmaj.
so (enumerate_subset _ _ u (fun x _ => Hdec x) Hdistu) as (q & Hdistq & Hq).
exists (sumweight f q), n.
do2 3 split; auto.
  {
  exists q.
  do2 2 split; auto.
  intro x.
  split.
    {
    intro Hx.
    apply Hq.
    split; auto.
    apply Hu.
    apply HPU; auto.
    }

    {
    intro Hx.
    apply Hq; auto.
    }
  }
so (le_lt_dec (sumweight f q) (two_thirds n)) as [Hle | Hlt']; auto.
exfalso.
assert (sumweight f (p ++ q) = sumweight f u) as Heq.
  {
  apply permutation_weight; auto.
  apply Permutation.NoDup_Permutation; auto.
    {
    apply NoDup_app; auto.
    intros x Hxp Hxq.
    so (Hp x andel Hxp andel).
    so (Hq x andel Hxq andel).
    contradiction.
    }
  intro x.
  split.
    {
    intros Hx.
    so (in_app_or _#4 Hx) as [Hxp | Hxq].
      { apply Hp; auto. }

      { apply Hq; auto. }
    }

    {
    intro Hx.
    apply in_or_app.
    so (Hdec x) as [Hyes | Hno].
      {
      right.
      apply Hq; auto.
      }
      
      {
      left.
      apply Hp; auto.
      }
    }
  }
rewrite -> sumweight_app in Heq.
unfold one_third in Hlt.
unfold two_thirds in Hle, Hlt.
omega.
Qed.


Lemma not_supermajority_every :
  forall T (f : T -> nat) (P : T -> Prop) n,
    (forall x, decidable (P x))    
    -> weight f (@every T) n
    -> ~ supermajority f P every
    -> superminority f (fun x => ~ P x) every.
Proof.
intros T f P n Hdec Hn Hnmaj.
so (not_supermajority _#5 Hdec (fun _ _ => I) Hn Hnmaj) as Hmin.
destruct Hmin as (m & n' & Hincl & Hm & Hn' & Hgt).
so (weight_fun _#5 Hn Hn'); subst n'.
exists m, n.
do2 3 split; auto.
eapply weight_iff; eauto.
intros x.
split.
  { intros (Hx & _); auto. }

  { intro Hx; auto. }
Qed.


Lemma majority_inhabitant :
  forall T (f : T -> nat) (P U : T -> Prop),
    majority f P U
    -> exists x, P x.
Proof.
intros T f P U H.
destruct H as (m & n & _ & H & _ & Hgt).
destruct H as (l & _ & Hl & Hlen).
assert (m > 0) as Hgt' by omega.
destruct l as [| x l].
  {
  cbn in Hlen; omega.
  }
exists x.
apply Hl.
left; auto.
Qed.


Lemma supermajority_inhabitant :
  forall T (f : T -> nat) (P U : T -> Prop),
    supermajority f P U
    -> exists x, P x.
Proof.
intros T f P U H.
eapply majority_inhabitant.
eapply supermajority_impl_majority; eauto.
Qed.
