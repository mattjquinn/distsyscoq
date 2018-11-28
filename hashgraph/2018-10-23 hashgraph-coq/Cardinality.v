(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Nat.
Require Import List.
Require Import Decidable.
Require Import Omega.

Require Import Tact.
Require Import Decide.


(* Almost everything here could now be reproved as a special case of a weight lemma. *)


Lemma permutation_length :
  forall (T : Type) (p q : list T),
    NoDup p
    -> NoDup q
    -> (forall x, In x p <-> In x q)
    -> length p = length q.
Proof.
intros T p q Hnodup1 Hnodup2 Hperm.
assert (length p <= length q) as Hle.
  {
  eapply NoDup_incl_length; eauto.
  intros x H.
  apply Hperm; auto.
  }
assert (length q <= length p) as Hge.
  {
  eapply NoDup_incl_length; eauto.
  intros x H.
  apply Hperm; auto.
  }
omega.
Qed.    


Lemma NoDup_app :
  forall (T : Type) (p q : list T),
    NoDup p
    -> NoDup q
    -> (forall x, In x p -> In x q -> False)
    -> NoDup (p ++ q).
Proof.
intros T p q Hdistp Hdistq Hdisj.
revert Hdistp Hdisj.
induct p.

(** nil *)
{
intros _ _.
exact Hdistq.
}

(** cons *)
{
intros x p IH Hdistxp Hdisj.
cbn.
invert Hdistxp.
intros Hnotin Hdistp.
apply NoDup_cons.
  {
  intro Hin.
  so (in_app_or _#4 Hin) as [Hinp | Hinq].
    { contradiction. }

    {
    eapply Hdisj; eauto.
    left; reflexivity.
    }
  }

  {
  apply IH; auto.
  intros y Hinp Hinq.
  eapply Hdisj; eauto.
  right; auto.
  }
}
Qed.


Lemma inclusion_exclusion :
  forall T (p q u : list T),
    (forall (x y : T), decidable (x = y))
    -> NoDup p
    -> NoDup q
    -> NoDup u
    -> List.incl p u
    -> List.incl q u
    -> exists r,
         NoDup r
         /\ List.incl r p
         /\ List.incl r q
         /\ length r >= length p + length q - length u.
Proof.
intros T p q u Hdeceq Hp Hq Hu Hpu Hqu.
revert q u Hq Hu Hpu Hqu.
induct Hp.

(** nil *)
{
intros q u Hq Hu Hpu Hqu.
exists nil.
do2 3 split.
  {
  apply NoDup_nil.
  }

  {
  intros x Hx.
  destruct Hx.
  }

  {
  intros x Hx.
  destruct Hx.
  }
assert (length q <= length u).
  {
  apply NoDup_incl_length; auto.
  }
omega.
}

(** cons *)
{
intros x p Hnotin Hp IH q u Hq Hu Hpu Hqu.
assert (In x u) as Hinu.
  {
  apply Hpu.
  left; reflexivity.
  }
so (in_split _#3 Hinu) as (u1 & u2 & ->).
assert (List.incl p (u1 ++ u2)) as Hpu'.
  {
  intros y Hyp.
  assert (In y (x :: p)) as Hyp'.
    {
    right; auto.
    }
  so (in_app_or _#4 (Hpu _ Hyp')) as [Hyu1 | Hyu2].
    {
    apply in_or_app; auto.
    }
    
    {
    apply in_or_app; right.
    cbn in Hyu2.
    destruct Hyu2; auto.
    exfalso.
    subst y.
    contradiction.
    }
  }
so (dec_In _ x q Hdeceq) as [Hinq | Hnin].
  {
  so (in_split _#3 Hinq) as (q1 & q2 & ->).
  exploit (IH (q1 ++ q2) (u1 ++ u2)) as H; eauto using NoDup_remove_1.
    {
    intros y Hyq.
    assert (In y (q1 ++ x :: q2)) as Hyq'.
      {
      so (in_app_or _#4 Hyq) as [Hyq1 | Hyq2].
        {
        apply in_or_app; auto.
        }

        {
        apply in_or_app; right.
        right.
        auto.
        }
      }
    so (Hqu y Hyq') as Hyu.
    so (in_app_or _#4 Hyu) as [Hyu1 | Hyu2].
      {
      apply in_or_app; auto.
      }

      {
      destruct Hyu2 as [Heq | Hyu2'].
        {
        exfalso.
        subst y.
        so (NoDup_remove_2 _#4 Hq).
        contradiction.
        }

        {
        apply in_or_app; auto.
        }
      }
    }
  destruct H as (r & Hr & Hrp & Hrq & Hlen).
  exists (x :: r).
  do2 3 split.
    {
    apply NoDup_cons; auto.
    }

    {
    intros y Hy.
    destruct Hy as [| Hy'].
      {
      subst y.
      left; auto.
      }

      {
      right.
      apply Hrp; auto.
      }
    }

    {
    intros y Hy.
    destruct Hy as [| Hy'].
      {
      subst y.
      apply in_or_app.
      right; left; auto.
      }

      {
      so (Hrq y Hy') as Hyq.
      so (in_app_or _#4 Hyq) as [Hyq' | Hyq'].
        {
        apply in_or_app; auto.
        }

        {
        apply in_or_app; right; right; auto.
        }
      }
    }
  
    {
    cbn.
    rewrite -> !app_length in Hlen |- *.
    cbn.
    rewrite -> Nat.add_succ_r.
    omega.
    }
  }

  {
  exploit (IH q (u1 ++ u2)) as H; eauto using NoDup_remove_1.
    {
    intros y Hy.
    so (Hqu y Hy) as Hyu.
    so (in_app_or _#4 Hyu) as [Hyu' | Hyu'].
      {
      apply in_or_app; auto.
      }

      {
      destruct Hyu' as [| Hyu''].
        {
        subst y.
        contradiction.
        }

        {
        apply in_or_app; auto.
        }
      }
    }
  destruct H as (r & Hr & Hrp & Hrq & Hlen).
  exists r.
  do2 3 split; auto.
    {
    intros y Hy.
    right; auto.
    }

    {
    rewrite -> !app_length in Hlen |- *.
    cbn.
    rewrite -> Nat.add_succ_r.
    omega.
    }
  }
}
Qed.


Lemma enumerate_subset :
  forall T (P : T -> Prop) (u : list T),
    (forall x, In x u -> decidable (P x))
    -> NoDup u
    -> exists p,
         NoDup p
         /\ forall x, In x p <-> (P x /\ In x u).
Proof.
intros T P u.
induct u.

(** nil *)
{
intros _ _.
exists nil.
split; auto using NoDup_nil.
intro x.
split.
  {
  intro H.
  destruct H.
  }

  {
  intros (_ & ?); auto.
  }
}

(** cons *)
{
intros x u IH Hdec Hdist.
invertc Hdist.
intros Hnotin Hdist.
exploit IH as H; auto.
  {
  intros y Hin.
  apply Hdec.
  right; auto.
  }
destruct H as (p & Hdistp & Hp).
so (Hdec x (or_introl (eq_refl _))) as [Hyes | Hno].
  {
  exists (cons x p).
  split.
    {
    apply NoDup_cons; auto.
    contradict Hnotin.
    apply Hp; auto.
    }
  intros y.
  split.
    {
    intro Hy.
    destruct Hy as [Heq | Hy].
      {
      subst y.
      split; auto.
      left; auto.
      }
    split.
      {
      apply Hp; auto.
      }
    
      {
      right.
      apply Hp; auto.
      }
    }
  
    {
    intros (Hy & Hiny).
    destruct Hiny as [Heq | Hiny].
      {
      subst y.
      left; auto.
      }

      {
      right.
      apply Hp; auto.
      }
    }
  }

  {
  exists p.
  split; auto.
  intro y.
  split.
    {
    intro Hy.
    split.
      {
      apply Hp; auto.
      }

      {
      right.
      apply Hp; auto.
      }
    }

    {
    intros (Hy & Hiny).
    destruct Hiny as [Heq | Hiny].
      {
      subst y.
      contradiction.
      }

      {
      apply Hp; auto.
      }
    }
  }
}
Qed.


Lemma deduplicate :
  forall T (l : list T),
    (forall (x y : T), decidable (x = y))
    -> exists l',
         NoDup l'
         /\ (forall x, In x l <-> In x l').
Proof.
intros T l Hdec.
induct l.

(** nil *)
{
exists nil.
split.
  { apply NoDup_nil. }
intros x; split; intro H; destruct H.
}

(** cons *)
{
intros x l IH.
destruct IH as (l' & Hdist & Hl').
so (dec_In _ x l' Hdec) as [Hin | Hnin].
  {
  exists l'.
  split; auto.
  intro y.
  split.
    {
    intro H.
    destruct H as [Heq | Hin'].
      {
      subst y; auto.
      }
      
      {
      apply Hl'; auto.
      }
    }

    {
    intro Hy.
    right.
    apply Hl'; auto.
    }
  }

  {
  exists (cons x l').
  split.
    {
    apply NoDup_cons; auto.
    }

    {
    intros y.
    split.
      {
      intro H.
      destruct H as [Heq | Hin'].
        {
        subst y; left; auto.
        }
        
        {
        right.
        apply Hl'; auto.
        }
      }
  
      {
      intro Hy.
      destruct Hy as [Heq | Hin].
        {
        subst; left; auto.
        }
  
        {
        right.
        apply Hl'; auto.
        }
      }
    }
  }
}
Qed.


Definition cardinality {T : Type} (P : T -> Prop) (n : nat) : Prop
  :=
  exists l,
    NoDup l
    /\ (forall x, P x <-> In x l)
    /\ length l = n.


Lemma cardinality_empty :
  forall T, cardinality (fun (x : T) => False) 0.
Proof.
intros T.
exists nil.
do2 2 split; auto.
  { apply NoDup_nil. }

  {
  intros x.
  cbn.
  split; auto.
  }
Qed.


Lemma cardinality_singleton :
  forall (T : Type) (x : T),
    cardinality (fun y => y = x) 1.
Proof.
intros T x.
exists (cons x nil).
do2 2 split; auto.
  {
  apply NoDup_cons.
    {
    intro H.
    destruct H.
    }

    { apply NoDup_nil. }
  }

  {
  intros y.
  split.
    {
    intros ->.
    left; auto.
    }

    {
    intro H.
    destruct H as [-> | H]; auto.
    destruct H.
    }
  }
Qed.


Lemma cardinality_In :
  forall (T : Type) (l : list T),
    NoDup l
    -> cardinality (fun x => In x l) (length l).
Proof.
intros T l.
exists l.
do2 2 split; auto.
intro; split; auto.
Qed.


Lemma cardinality_fun :
  forall (T : Type) (P : T -> Prop) n n',
    cardinality P n
    -> cardinality P n'
    -> n = n'.
Proof.
intros T P n n' Hn Hn'.
destruct Hn as (l & Hnodup & Hmem & <-).
destruct Hn' as (l' & Hnodup' & Hmem' & <-).
eapply permutation_length; eauto.
intro x.
split; intro Hx.
  {
  apply Hmem'; apply Hmem; auto.
  }

  {
  apply Hmem; apply Hmem'; auto.
  }
Qed.


Lemma cardinality_iff :
  forall (T : Type) (P Q : T -> Prop) n,
    (forall x, P x <-> Q x)
    -> cardinality P n
    -> cardinality Q n.
Proof.
intros T P Q n Hiff HP.
destruct HP as (p & Hdist & Hp & Hlen).
exists p.
do2 2 split; auto.
intros x.
split.
  {
  intro Hx.
  apply Hp.
  apply Hiff.
  auto.
  }

  {
  intro Hx.
  apply Hiff.
  apply Hp.
  auto.
  }
Qed.


Lemma cardinality_empty' :
  forall T (P : T -> Prop),
    (forall x, ~ P x)
    -> cardinality P 0.
Proof.
intros T P Hfalse.
apply (cardinality_iff _ (fun _ => False)).
  2:{ apply cardinality_empty. }
intros x.
split.
 { intro H; destruct H. }

 { apply Hfalse. }
Qed.


Lemma cardinality_nonempty :
  forall T (P : T -> Prop) p,
    cardinality P p
    -> p > 0
    -> exists x, P x.
Proof.
intros T P p Hp Hgt.
destruct Hp as (l & _ & Hl & Hlen).
destruct l as [| x l].
  {
  cbn in Hlen.
  omega.
  }

  {
  exists x.
  apply Hl.
  left; auto.
  }
Qed.


Lemma cardinality_subset :
  forall (T : Type) (P Q : T -> Prop) n,
    (forall x, Q x -> decidable (P x))
    -> incl P Q
    -> cardinality Q n
    -> exists m,
         cardinality P m
         /\ m <= n.
Proof.
intros T P Q n HdecP HPQ HcardQ.
destruct HcardQ as (q & Hdistq & Hq & Hlenq).
exploit (enumerate_subset _ P q) as H; auto.
  {
  intros x Hx.
  apply HdecP.
  apply Hq; auto.
  }
destruct H as (p & Hdistp & Hp).
exists (length p).
split.
  {
  exists p.
  do2 2 split; auto.
  intro x.
  split.
    {
    intro Hx.
    apply Hp.
    split; auto.
    apply Hq; auto.
    }

    {
    intro Hx.
    apply Hp; auto.
    }
  }

  {
  subst n.
  apply NoDup_incl_length; auto.
  intros x Hx.
  apply Hq.
  apply HPQ.
  apply Hp; auto.
  }
Qed.


Lemma pigeonhole :
  forall S T (P : S -> Prop) (Q : T -> Prop) (f : S -> T) l m n,
    (forall (x y : T), decidable (x = y))
    -> (forall x, P x -> Q (f x))
    -> cardinality P l
    -> cardinality Q m
    -> l > m * n
    -> exists y n',
         Q y
         /\ cardinality (fun x => P x /\ f x = y) n'
         /\ n' > n.
Proof.
intros S T P Q f l m n Hdeceq HPQ Hl Hm Hgt.
destruct Hl as (p & Hdistp & Hp & <-).
destruct Hm as (q & Hdistq & Hq & <-).
cut (exists y r,
       In y q
       /\ NoDup r
       /\ (forall x, (In x p /\ f x = y) <-> In x r)
       /\ length r > n).
  {
  intros (y & r & Hy & Hdistr & Hr & Hlenr).
  exists y, (length r).
  do2 2 split; auto.
    {
    apply Hq; auto.
    }

    {
    exists r.
    do2 2 split; auto.
    intros x.
    rewrite <- Hr.
    rewrite <- Hp.
    reflexivity.
    }
  }
assert (forall x, In x p -> In (f x) q) as Hpq.
  {
  intros x Hx.
  apply Hq.
  apply HPQ.
  apply Hp.
  auto.
  }
clear Hp Hq HPQ.
revert p Hdistp Hpq Hgt.
induct Hdistq.

(** nil *)
{
intros p Hdistp Hpq Hgt.
exfalso.
destruct p as [| x p].
  {
  cbn in Hgt.
  omega.
  }
apply (Hpq x).
left; auto.
}

(** cons *)
{
intros y q Hnin Hdistq IH p Hdistp Hpq Hgt.
cbn in Hgt.
exploit (enumerate_subset _ (fun x => f x = y) p) as H; auto.
destruct H as (p1 & Hdistp1 & Hp1).
so (lt_dec n (length p1)) as [Hgt' | Hngt].
  {
  exists y, p1.
  do2 3 split; auto.
    { left; auto. }
  intro x.
  rewrite -> Hp1.
  split; intros (? & ?); auto.
  }
exploit (enumerate_subset _ (fun x => f x <> y) p) as H; auto.
  {
  auto using dec_not.
  }
destruct H as (p2 & Hdistp2 & Hp2).
exploit (IH p2) as H; auto.
  {
  intros x Hx.
  so (Hp2 x andel Hx) as (Hneq & Hx').
  so (Hpq x Hx') as Hfx.
  destruct Hfx as [Heq | Hfx]; auto.
  subst y.
  destruct Hneq; auto.
  }

  {
  cut (length p1 + length p2 = length p).
    { omega. }
  rewrite <- app_length.
  apply permutation_length; auto.
    {
    apply NoDup_app; auto.
    intros x Hx1 Hx2.
    so (Hp1 x andel Hx1 andel).
    so (Hp2 x andel Hx2 andel).
    contradiction.
    }

    {
    intros x.
    split.
      {
      intros Hx.
      so (in_app_or _#4 Hx) as [Hx' | Hx']; auto.
        {
        apply Hp1; auto.
        }

        {
        apply Hp2; auto.
        }
      }

      {
      intros Hx.
      apply in_or_app.
      so (Hdeceq (f x) y) as [Heq | Hneq].
        {
        left.
        apply Hp1; auto.
        }

        {
        right.
        apply Hp2; auto.
        }
      }
    }
  }
destruct H as (z & r & Hz & Hdistr & Hr & Hlenr).
exists z, r.
do2 3 split; auto.
  {
  right; auto.
  }

  {
  intros x.
  split.
    {
    intros (Hx & Heqz).
    apply Hr.
    split; auto.
    apply Hp2.
    split; auto.
    intro Heqy.
    rewrite -> Heqy in Heqz.
    subst z.
    contradiction.
    }

    {
    intros Hx.
    split.
      {
      apply Hp2.
      apply Hr; auto.
      }

      {
      apply Hr; auto.
      }
    }
  }
}
Qed.


Lemma cardinality_sum :
  forall T (A B : T -> Prop) a b,
    cardinality A a
    -> cardinality B b
    -> (forall x, A x -> B x -> False)
    -> cardinality (fun x => A x \/ B x) (a + b).
Proof.
intros T A B a b Ha Hb Hdisj.
destruct Ha as (l & Hdistl & Hl & Hlenl).
destruct Hb as (m & Hdistm & Hm & Hlenm).
subst a b.
exists (l ++ m).
do2 2 split.
  {
  apply NoDup_app; auto.
  intros x Hxl Hxm.
  apply (Hdisj x).
    { apply Hl; auto. }

    { apply Hm; auto. }
  }

  {
  intros x.
  split.
    {
    intros [Hx | Hx].
      {
      apply in_or_app; left.
      apply Hl; auto.
      }

      {
      apply in_or_app; right.
      apply Hm; auto.
      }
    }

    {
    intros Hx.
    so (in_app_or _#4 Hx) as [Hxl | Hxm].
      {
      left.
      apply Hl; auto.
      }

      {
      right.
      apply Hm; auto.
      }
    }
  }

  {
  rewrite -> app_length.
  reflexivity.
  }
Qed.


Lemma cardinality_partition :
  forall T (A B U : T -> Prop) a b,
    incl A U
    -> incl B U
    -> cardinality U (a + b)
    -> cardinality A a
    -> cardinality B b
    -> (forall x, A x -> B x -> False)
    -> forall x, U x -> A x \/ B x.
Proof.
intros T A B U m n HAU HBU HcardU HcardA HcardB Hdisj.
destruct HcardU as (u & Hdistu & Hu & Hlenu).
destruct HcardA as (a & Hdista & Ha & Hlena).
destruct HcardB as (b & Hdistb & Hb & Hlenb).
assert (forall x, In x u -> In x (a ++ b)) as Hprop.
  {
  apply NoDup_length_incl.
    {
    apply NoDup_app; auto.
    intros x Hxa Hxb.
    apply (Hdisj x).
      { apply Ha; auto. }

      { apply Hb; auto. }
    }

    {
    rewrite -> app_length.
    omega.
    }

    {
    intros x Hx.
    so (in_app_or _#4 Hx) as [Hx' | Hx'].
      {
      apply Hu.
      apply HAU.
      apply Ha; auto.
      }

      {
      apply Hu.
      apply HBU.
      apply Hb; auto.
      }
    }
  }
intros x Hx.
so (in_app_or _#4 (Hprop x (Hu x andel Hx))) as [Hx' | Hx'].
  {
  left.
  apply Ha; auto.
  }

  {
  right.
  apply Hb; auto.
  }
Qed.


Lemma cardinality_difference :
  forall T (A B : T -> Prop) a b,
    (forall (x y : T), decidable (x = y))
    -> cardinality A a
    -> cardinality B b
    -> a < b
    -> exists x, ~ A x /\ B x.
Proof.
intros T A B m n Hdec HcardA HcardB Hlt.
destruct HcardA as (a & Hdista & Ha & Hlena).
destruct HcardB as (b & Hdistb & Hb & Hlenb).
cut (exists x, ~ In x a /\ In x b).
  {
  intros (x & Hnin & Hin).
  exists x.
  split.
    {
    contradict Hnin.
    apply Ha; auto.
    }

    {
    apply Hb; auto.
    }
  }
clear Ha Hb Hdista.
subst m n.
revert a Hlt.
induct Hdistb.

(** nil *)
{
intros a Hlen.
cbn in Hlen.
omega.
}

(** cons *)
{
intros x b Hninb Hdistb IH a Hlen.
so (dec_In _ x a Hdec) as [Hin | Hnina].
  {
  so (in_split _#3 Hin) as (a1 & a2 & ->).
  exploit (IH (a1 ++ a2)) as H.
    {
    rewrite -> app_length in Hlen |- *.
    cbn in Hlen.
    omega.
    }
  destruct H as (y & Hnina & Hinb).
  exists y.
  split.
    {
    contradict Hnina.
    so (in_app_or _#4 Hnina) as [Hina | Hina].
      { apply in_or_app; left; auto. }
    destruct Hina as [Heq | Hina].
      {
      subst y.
      contradiction.
      }
    apply in_or_app; right; auto.
    }

    {
    right; auto.
    }
  }

  {
  exists x.
  split; auto.
  left; auto.
  }
}
Qed.


Lemma cardinality_corr_le :
  forall S T (P : S -> Prop) (Q : T -> Prop) (R : S -> T -> Prop) p q,
    (forall x x' y, P x -> P x' -> Q y -> R x y -> R x' y -> x = x')
    -> (forall x, P x -> exists y, R x y /\ Q y)
    -> cardinality P p
    -> cardinality Q q
    -> p <= q.
Proof.
intros S T P Q R np nq Hinj Hdef HcardP HcardQ.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
destruct HcardQ as (q & Hdistq & Hq & Hlenq).
subst np nq.
cut (exists r,
       NoDup r
       /\ (forall x, In x r -> Q x /\ exists y, In y p /\ R y x)
       /\ length p = length r).
  {
  intros (r & Hdistr & Hr & Hlenr).
  rewrite -> Hlenr.
  apply NoDup_incl_length; auto.
  intros x Hx.
  apply Hq.
  apply Hr; auto.
  }
so (fun x => Hp x ander) as H.
clear Hp.
revert H.
induct Hdistp.

(** nil *)
{
intros _.
exists nil.
do2 2 split; auto.
  { apply NoDup_nil. }
intros x Hx.
destruct Hx.
}

(** cons *)
{
intros x p Hnin _ IH Hp.
exploit (Hp x) as Hx.
  {
  left; auto.
  }
so (Hdef x Hx) as (y & Hxy & Hy).
exploit IH as H.
  {
  intros z Hz.
  apply Hp.
  right; auto.
  }
destruct H as (r & Hdistr & Hr & Hlenr).
exists (cons y r).
do2 2 split.
  {
  apply NoDup_cons; auto.
  contradict Hnin.
  so (Hr y Hnin) as (_ & x' & Hinx' & Hx'y).
  so (Hinj x x' y Hx (Hp x' (or_intror Hinx')) Hy Hxy Hx'y).
  subst x'.
  exact Hinx'.
  }

  {
  intros z Hz.
  destruct Hz as [Heq | Hz].
    {
    subst z.
    split; auto.
    exists x.
    split; auto.
    left; auto.
    }

    {
    so (Hr z Hz) as (HQz & w & Hinw & Hwz).
    split; auto.
    exists w.
    split; auto.
    right; auto.
   }
  }

  {
  cbn.
  auto.
  }
}
Qed.


Lemma cardinality_corr_eq :
  forall S T (P : S -> Prop) (Q : T -> Prop) (R : S -> T -> Prop) p q,
    (forall x x' y, P x -> P x' -> Q y -> R x y -> R x' y -> x = x')
    -> (forall x y y', P x -> Q y -> Q y' -> R x y -> R x y' -> y = y')
    -> (forall x, P x -> exists y, R x y /\ Q y)
    -> (forall y, Q y -> exists x, R x y /\ P x)
    -> cardinality P p
    -> cardinality Q q
    -> p = q.
Proof.
intros S T P Q R p q Hinj Hfun Hdef Hsur HcardP HcardQ.
so (cardinality_corr_le _#7 Hinj Hdef HcardP HcardQ).
exploit (cardinality_corr_le T S Q P (fun x y => R y x) q p); auto.
  {
  intros.
  eapply Hfun; eauto.
  }
omega.
Qed.


Lemma cardinality_map_inj :
  forall S T (P : S -> Prop) (Q : T -> Prop) (f : S -> T) p q,
    (forall x, P x -> Q (f x))
    -> (forall x y, P x -> P y -> f x = f y -> x = y)
    -> cardinality P p
    -> cardinality Q q
    -> p <= q.
Proof.
intros S T P Q f m n Hincl Hinj HcardP HcardQ.
apply (cardinality_corr_le S T P Q (fun x y => f x = y) m n); auto.
  {
  intros x x' y Hx Hx' Hy Heq Heq'.
  apply Hinj; auto.
  transitivity y; auto.
  }

  {
  intros x Hx.
  exists (f x).
  split; auto.
  }
Qed.


Lemma cardinality_map_surj :
  forall S T (P : S -> Prop) (Q : T -> Prop) (f : T -> S) p q,
    (forall x, Q x -> P (f x))
    -> (forall x, P x -> exists y, Q y /\ x = f y)
    -> cardinality P p
    -> cardinality Q q
    -> p <= q.
Proof.
intros S T P Q f m n Hincl Hsurj HcardP HcardQ.
apply (cardinality_corr_le S T P Q (fun x y => x = f y) m n); auto.
  {
  intros x x' y Hx Hx' Hy Heq Heq'.
  transitivity (f y); auto.
  }

  {
  intros x Hx.
  so (Hsurj x Hx) as (y & Hy & Heq).
  subst x.
  exists y.
  split; auto.
  }
Qed.


Lemma cardinality_incl :
  forall T (P Q : T -> Prop) p q,
    incl P Q
    -> cardinality P p
    -> cardinality Q q
    -> p <= q.
Proof.
intros T P Q p q HPQ Hp Hq.
eapply cardinality_map_inj with (f := (fun x => x)); eauto.
Qed.


Lemma cardinality_image :
  forall S T (P : S -> Prop) (f : S -> T) n,
    (forall x y, P x -> P y -> f x = f y -> x = y)
    -> cardinality P n
    -> cardinality (fun x => exists y, x = f y /\ P y) n.
Proof.
intros S T P f n Hinj HcardP.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
exists (map f p).
do2 2 split.
  {
  so (fun x => Hp x ander) as H.
  revert H.
  clear Hp Hlenp.
  induct Hdistp.
    (** nil *)
    {
    intros _.
    apply NoDup_nil.
    }
    
    (** cons *)
    {
    intros x p Hnin _ IH Hp.
    cbn.
    apply NoDup_cons.
      {
      contradict Hnin.
      so (in_map_iff _#5 andel Hnin) as (x' & Heq & Hx').  
      force_exact Hx'.
      f_equal.
      apply Hinj; auto.
        {
        apply Hp.
        right; auto.
        }

        {
        apply Hp.
        left; auto.
        }
      }

      {
      apply IH.
      intros y Hy.
      apply Hp.
      right; auto.
      }
    }
  }

  {
  intro x.
  split.
    {
    intros (y & -> & Hy).
    apply in_map.
    apply Hp; auto.
    }

    {
    intros Hx.
    so (in_map_iff _#5 andel Hx) as (y & <- & Hy).
    exists y.
    split; auto.
    apply Hp; auto.
    }
  }

  {
  rewrite -> map_length.
  auto.
  }
Qed.


Lemma cardinality_tabulate :
  forall (S T : Type) (P : S -> Prop) (Q : S -> T -> Prop) l m,
    cardinality P l
    -> (forall x, P x -> exists m', cardinality (Q x) m' /\ m <= m')
    -> exists n,
         cardinality (fun xy => P (fst xy) /\ Q (fst xy) (snd xy)) n
         /\ l * m <= n.
Proof.
intros S T P Q l m HcardP HcardQ.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
subst l.
cut (exists r,
       NoDup r
       /\ (forall xy, In (fst xy) p /\ Q (fst xy) (snd xy) <-> In xy r)
       /\ length p * m <= length r).
  {
  intros (r & Hdistr & Hr & Hlenr).
  exists (length r).
  split; auto.
  exists r.
  do2 2 split; auto.
  intros xy.
  rewrite -> Hp.
  rewrite -> Hr.
  reflexivity.
  }
so (fun x Hx => Hp x ander Hx) as Hp'.
renameover Hp' into Hp.
revert Hp.
induct Hdistp.

(** nil *)
{
intros _.
exists nil.
do2 2 split; auto.
  { apply NoDup_nil. }

  {
  intros xy.
  split.
    {
    intros (Hx & _).
    destruct Hx.
    }

    {
    intros H.
    destruct H.
    }
  }
}

(** cons *)
{
intros x p Hnin Hdistp IH Hp.
exploit IH as H.
  {
  intros z Hz.
  apply Hp.
  right; auto.
  }
destruct H as (r2 & Hdistr2 & Hr2 & Hlenr2).
so (HcardQ x (Hp x (or_introl (eq_refl _)))) as (? & Hcard & Hle).
destruct Hcard as (r1 & Hdistr1 & Hr1 & <-).
exists (map (fun y => (x, y)) r1 ++ r2).
do2 2 split.
  {
  apply NoDup_app; auto.
    {
    apply (@NoDup_map_inv _ _ snd).
    rewrite -> map_map.
    cbn.
    rewrite -> map_id.
    auto.
    }

    {
    intros (x', y) H1 H2.
    so (in_map_iff _#5 andel H1) as (z & Heq & _).
    injection Heq.
    intros -> <-.
    so (Hr2 _ ander H2) as (Hinx & _).
    cbn in Hinx.
    contradiction.
    }
  }

  {
  intros (y, z).
  cbn [fst snd].
  split.
    {
    intros (Hin & Hyz).
    apply in_or_app.
    destruct Hin as [? | Hin].
      {
      subst y.
      left.
      apply in_map.
      apply Hr1; auto.
      }

      {
      right.
      apply Hr2.
      cbn.
      auto.
      }
    }

    {
    intro Hin.
    so (in_app_or _#4 Hin) as [Hin' | Hin'].
      {
      so (in_map_iff _#5 andel Hin') as (z' & Heq & Hinz).
      injection Heq.
      intros -> <-.
      split.
        { left; auto. }

        { apply Hr1; auto. }
      }

      {
      so (Hr2 _ ander Hin') as H.
      cbn in H.
      destruct H as (Hy & Hyz).
      split; auto.
      right; auto.
      }
    }
  }

  {
  cbn.
  rewrite -> app_length.
  rewrite -> map_length.
  omega.
  }
}
Qed.


Lemma cardinality_finite :
  forall T (P : T -> Prop) n, cardinality P n -> finite P.
Proof.
intros T P n Hcard.
destruct Hcard as (l & _ & H & _).
exists l.
intros; apply H; auto.
Qed.


Lemma finite_cardinality :
  forall T (P : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> finite P
    -> exists i, cardinality P i.
Proof.
intros T P Hdeceq Hfin.
destruct Hfin as (l & Hl).
so (deduplicate _ l Hdeceq) as (l' & Hdist & Hl').
exists (length l').
exists l'.
do2 2 split; auto.
intros x.
split.
  {
  intro Hx.
  apply Hl'.
  apply Hl; auto.
  }

  {
  intro Hx.
  apply Hl; auto.
  apply Hl'; auto.
  }
Qed.


Lemma cardinality_gt_decide :
  forall (T : Type) (P U : T -> Prop) n n',
    (forall x, decidable (P x))
    -> incl P U
    -> cardinality U n
    -> decidable (exists p, cardinality P p /\ p > n').
Proof.
intros T P U n n' Hdec HPU HcardU.
so HcardU as (u & Hdist & Hu & Hlenu).
so (enumerate_subset _#3 (fun x _ => Hdec x) Hdist) as (p & Hdistp & Hp).
so (le_lt_dec (length p) n') as [Hle | Hlt].
2:{
  left.
  exists (length p).
  split; auto.
  exists p.
  do2 2 split; auto.
  intros x.
  split.
    {
    intro Hx.
    apply Hp.
    split; auto.
    apply Hu.
    apply HPU; auto.
    }

    {
    intro Hx.
    apply Hp; auto.
    }
  }
right.
intro H.
destruct H as (m & HcardP & Hgt).
destruct HcardP as (p' & Hdistp' & Hp' & Hlenp).
exploit (permutation_length _ p p') as Heq; auto.
  {
  intros x.
  split.
    {
    intro Hx.
    apply Hp'.
    apply Hp; auto.
    }

    {
    intro Hx.
    apply Hp.
    split.
      {
      apply Hp'; auto.
      }

      {
      apply Hu.
      apply HPU.
      apply Hp'; auto.
      }
    }
  }
omega.
Qed.


Definition cardinality_lt {T : Type} (P : T -> Prop) (n : nat) : Prop
  :=
  ~ exists l,
      NoDup l
      /\ (forall x, In x l -> P x)
      /\ length l >= n.


Lemma cardinality_impl_cardinality_lt :
  forall T (P : T -> Prop) m n,
    m < n
    -> cardinality P m
    -> cardinality_lt P n.
Proof.
intros T P m n Hlt Hcard.
destruct Hcard as (k & Hdistk & Hk & Hlenk).
intros (l & Hdistl & Hl & Hlenl).
exploit (@NoDup_incl_length _ l k) as Hleq; auto.
  {
  intros x Hx.
  apply Hk.
  apply Hl; auto.
  }
omega.
Qed.


Lemma cardinality_lt_increase :
  forall T (P : T -> Prop) m n,
    m <= n
    -> cardinality_lt P m
    -> cardinality_lt P n.
Proof.
intros T P m n Hleq Hcard.
unfold cardinality_lt in *.
contradict Hcard.
destruct Hcard as (l & Hdist & Hl & Hlen).
exists l.
do2 2 split; auto.
omega.
Qed.


Lemma cardinality_lt_impl_lt :
  forall T (P Q : T -> Prop) p q,
    incl P Q
    -> cardinality P p
    -> cardinality_lt Q q
    -> p < q.
Proof.
intros T P Q p q HPQ Hp Hq.
so (lt_dec p q) as [| Hnlt]; auto.
exfalso.
assert (p >= q) as Hpq by omega.
destruct Hp as (l & Hdist & Hl & Hlen).
destruct Hq.
exists l.
do2 2 split; auto.
  {
  intros x Hx.
  apply HPQ.
  apply Hl; auto.
  }

  {
  omega.
  }
Qed.


Lemma cardinality_lt_by_contradiction :
  forall T (P : T -> Prop) p,
    (forall Q q, incl Q P -> cardinality Q q -> q >= p -> False)
    -> cardinality_lt P p.
Proof.
intros T P p Hprop.
intros (l & Hdist & Hl & Hlen).
apply (Hprop (fun x => In x l) (length l)); auto.
exists l.
do2 2 split; auto.
intro; split; auto.
Qed.
