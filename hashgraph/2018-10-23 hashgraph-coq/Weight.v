(* Copyright (c) 2019 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Nat.
Require Import List.
Require Import Decidable.
Require Import Omega.
Require Import Permutation.

Require Import Tact.
Require Import Decide.


Definition sumweight {T : Type} (f : T -> nat) (l : list T) : nat
  :=
  fold_right (fun x m => f x + m) 0 l.


Lemma sumweight_cons :
  forall (T : Type) (f : T -> nat) (x : T) (l : list T),
    sumweight f (cons x l) = f x + sumweight f l.
Proof.
intros T f x l.
reflexivity.
Qed.


Lemma sumweight_app :
  forall (T : Type) (f : T -> nat) (p q : list T),
    sumweight f (p ++ q) = sumweight f p + sumweight f q.
Proof.
intros T f p q.
induct p; eauto.

(* cons *)
{
intros x l IH.
rewrite <- app_comm_cons.
rewrite -> !sumweight_cons.
omega.
}
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

(* nil *)
{
intros _ _.
exact Hdistq.
}

(* cons *)
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


Lemma permutation_weight :
  forall (T : Type) (f : T -> nat) (p q : list T),
    Permutation p q
    -> sumweight f p = sumweight f q.
Proof.
intros T f p q Hperm.
induct Hperm; auto.

(* skip *)
{
intros x p q _ IH.
cbn.
f_equal; auto.
}

(* swap *)
{
intros x y p.
cbn.
omega.
}

(* trans *)
{
intros p q r _ IH1 _ IH2.
etransitivity; eauto.
}
Qed.


Lemma permutation_weight' :
  forall (T : Type) (f : T -> nat) (p q : list T),
    NoDup p
    -> NoDup q
    -> (forall x, In x p <-> In x q)
    -> sumweight f p = sumweight f q.
Proof.
intros T f p q Hdistp Hdistq Hiff.
apply permutation_weight.
apply NoDup_Permutation; auto.
Qed.


Lemma incl_weight :
  forall (T : Type) (f : T -> nat) (p q : list T),
    NoDup p
    -> NoDup q
    -> List.incl p q
    -> sumweight f p <= sumweight f q.
Proof.
intros T f p q Hp Hq Hpq.
revert q Hq Hpq.
induct Hp.

(* nil *)
{
intros q Hq Hpq.
cbn.
omega.
}

(* cons *)
{
intros x p Hnotin Hdistp IH q Hq Hpq.
rewrite -> sumweight_cons.
assert (In x q) as Hin.
  {
  apply Hpq.
  left; auto.
  }
so (in_split _#3 Hin) as (q1 & q2 & ->).
rewrite -> sumweight_app.
rewrite -> sumweight_cons.
exploit (IH (q1 ++ q2)) as H.
  {
  eapply NoDup_remove_1; eauto.
  }

  {
  intros y Hy.
  so (in_app_or _#4 (Hpq y (or_intror Hy))) as [Hiny | Hiny].
    {
    apply in_or_app; left; auto.
    }

    {
    destruct Hiny as [Heq | Hiny].
      {
      subst y.
      contradiction.
      }

      {
      apply in_or_app; right; auto.
      }
    }
  }
rewrite -> sumweight_app in H.
omega.
}
Qed.


Lemma inclusion_exclusion :
  forall T (f : T -> nat) (p q u : list T),
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
         /\ sumweight f r >= sumweight f p + sumweight f q - sumweight f u.
Proof.
intros T f p q u Hdeceq Hp Hq Hu Hpu Hqu.
revert q u Hq Hu Hpu Hqu.
induct Hp.

(* nil *)
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
cbn.
so (incl_weight _ f _ _ Hq Hu Hqu).
omega.
}

(* cons *)
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
    rewrite -> !sumweight_app, !sumweight_cons.
    rewrite -> !sumweight_app in Hlen.
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
    rewrite -> !sumweight_app, !sumweight_cons.
    rewrite -> !sumweight_app in Hlen.
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

(* nil *)
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

(* cons *)
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

(* nil *)
{
exists nil.
split.
  { apply NoDup_nil. }
intros x; split; intro H; destruct H.
}

(* cons *)
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


Definition weight {T : Type} (f : T -> nat) (P : T -> Prop) (n : nat) : Prop
  :=
  exists l,
    NoDup l
    /\ (forall x, P x <-> In x l)
    /\ sumweight f l = n.


Lemma weight_empty :
  forall T f, weight f (fun (x : T) => False) 0.
Proof.
intros T f.
exists nil.
do2 2 split; auto.
  { apply NoDup_nil. }

  {
  intros x.
  cbn.
  split; auto.
  }
Qed.


Lemma weight_singleton :
  forall (T : Type) (f : T -> nat) (x : T),
    weight f (fun y => y = x) (f x).
Proof.
intros T f x.
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

  {
  cbn.
  omega.
  }
Qed.


Lemma weight_In :
  forall (T : Type) (f : T -> nat) (l : list T),
    NoDup l
    -> weight f (fun x => In x l) (sumweight f l).
Proof.
intros T f l.
exists l.
do2 2 split; auto.
intro; split; auto.
Qed.


Lemma weight_fun :
  forall (T : Type) (f : T -> nat) (P : T -> Prop) n n',
    weight f P n
    -> weight f P n'
    -> n = n'.
Proof.
intros T f P n n' Hn Hn'.
destruct Hn as (l & Hnodup & Hmem & <-).
destruct Hn' as (l' & Hnodup' & Hmem' & <-).
eapply permutation_weight'; eauto.
intro x.
split; intro Hx.
  {
  apply Hmem'; apply Hmem; auto.
  }

  {
  apply Hmem; apply Hmem'; auto.
  }
Qed.


Lemma weight_iff :
  forall (T : Type) (f : T -> nat) (P Q : T -> Prop) n,
    (forall x, P x <-> Q x)
    -> weight f P n
    -> weight f Q n.
Proof.
intros T f P Q n Hiff HP.
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


Lemma weight_empty' :
  forall T (f : T -> nat) (P : T -> Prop),
    (forall x, ~ P x)
    -> weight f P 0.
Proof.
intros T f P Hfalse.
apply (weight_iff _ _ (fun _ => False)).
  2:{ apply weight_empty. }
intros x.
split.
 { intro H; destruct H. }

 { apply Hfalse. }
Qed.


Lemma weight_nonempty :
  forall T (f : T -> nat) (P : T -> Prop) p,
    weight f P p
    -> p > 0
    -> exists x, P x.
Proof.
intros T f P p Hp Hgt.
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


Lemma weight_subset :
  forall (T : Type) (f : T -> nat) (P Q : T -> Prop) n,
    (forall x, Q x -> decidable (P x))
    -> incl P Q
    -> weight f Q n
    -> exists m,
         weight f P m
         /\ m <= n.
Proof.
intros T f P Q n HdecP HPQ HcardQ.
destruct HcardQ as (q & Hdistq & Hq & Hlenq).
exploit (enumerate_subset _ P q) as H; auto.
  {
  intros x Hx.
  apply HdecP.
  apply Hq; auto.
  }
destruct H as (p & Hdistp & Hp).
exists (sumweight f p).
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
  apply incl_weight; auto.
  intros x Hx.
  apply Hq.
  apply HPQ.
  apply Hp; auto.
  }
Qed.


Lemma weight_subset' :
  forall (T : Type) (f : T -> nat) (P Q : T -> Prop) m n,
    (forall x, Q x -> decidable (P x))
    -> incl P Q
    -> weight f P m
    -> weight f Q n
    -> m <= n.
Proof.
intros T f P Q m n Hdec Hincl HwtP HwtQ.
so (weight_subset _#5 Hdec Hincl HwtQ) as (m' & HwtP' & Hle).
so (weight_fun _#5 HwtP HwtP'); subst m'.
exact Hle.
Qed.


Lemma weight_sum :
  forall T (f : T -> nat) (A B : T -> Prop) a b,
    weight f A a
    -> weight f B b
    -> (forall x, A x -> B x -> False)
    -> weight f (fun x => A x \/ B x) (a + b).
Proof.
intros T f A B a b Ha Hb Hdisj.
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
  rewrite -> sumweight_app.
  reflexivity.
  }
Qed.


Lemma NoDup_weight_incl :
  forall T (f : T -> nat) (l l' : list T),
    NoDup l
    -> (forall x, In x l' -> f x > 0)
    -> sumweight f l' <= sumweight f l
    -> List.incl l l'
    -> List.incl l' l.
Proof.
intros T f l m Hdist Hpos Hle Hlm.
remember (sumweight f m) as w eqn:Heqw.
revert l m Hdist Hpos Hle Hlm Heqw.
wfinduct w using lt_wf.
intros w IH l m Hdist Hpos Hle Hlm ->.
destruct l as [| x l].
  {
  destruct m as [| x m]; auto.
  rewrite -> sumweight_cons in Hle.
  cbn in Hle.
  so (Hpos x (or_introl (eq_refl _))).
  omega.
  }
so (Hlm x (or_introl (eq_refl _))) as Hmx.
so (in_split _#3 Hmx) as (m1 & m2 & ->).
cut (List.incl (m1 ++ m2) l).
  {
  intros Hincl y Hy.
  so (in_app_or _#4 Hy) as [Hy' | Hy'].
    {
    right.
    apply Hincl.
    apply in_or_app.
    left; auto.
    }

    {
    destruct Hy' as [| Hy'].
      {
      subst y.
      left; auto.
      }

      {
      right.
      apply Hincl.
      apply in_or_app; right; auto.
      }
    }
  }
invertc Hdist.
intros Hnotin Hdist.
apply (IH (sumweight f (m1 ++ m2))); auto.
  {
  rewrite -> !sumweight_app.
  rewrite -> sumweight_cons.
  exploit (Hpos x) as Hpos'.
    {
    apply in_or_app; right; left; auto.
    }
  omega.
  }

  {
  intros y Hy.
  apply Hpos.
  revert y Hy.
  apply incl_app.
    {
    apply incl_appl.
    apply incl_refl.
    }

    {
    apply incl_appr.
    apply incl_tl.
    apply incl_refl.
    }
  }

  {
  rewrite -> sumweight_app.
  rewrite -> sumweight_app in Hle.
  rewrite -> !sumweight_cons in Hle.
  omega.
  }

  {
  intros y Hy.
  so (in_app_or _#4 (Hlm y (or_intror Hy))) as [Hy' | Hy'].
    {
    apply in_or_app; left; auto.
    }

    {
    destruct Hy' as [| Hy'].
      {
      subst y.
      contradiction.
      }

      {
      apply in_or_app; right; auto.
      }
    }
  }
Qed.


Lemma weight_partition :
  forall T (f : T -> nat) (A B U : T -> Prop) a b,
    incl A U
    -> incl B U
    -> (forall x, U x -> f x > 0)
    -> weight f U (a + b)
    -> weight f A a
    -> weight f B b
    -> (forall x, A x -> B x -> False)
    -> forall x, U x -> A x \/ B x.
Proof.
intros T f A B U m n HAU HBU Hpos HcardU HcardA HcardB Hdisj.
destruct HcardU as (u & Hdistu & Hu & Hlenu).
destruct HcardA as (a & Hdista & Ha & Hlena).
destruct HcardB as (b & Hdistb & Hb & Hlenb).
assert (forall x, In x u -> In x (a ++ b)) as Hprop.
  {
  apply (NoDup_weight_incl _ f); auto.
    {
    apply NoDup_app; auto.
    intros x Hxa Hxb.
    apply (Hdisj x).
      { apply Ha; auto. }
      
      { apply Hb; auto. }
    }

    {
    intros x Hx.
    apply Hpos.
    apply Hu; auto.
    }

    {
    rewrite -> sumweight_app.
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


Lemma weight_difference :
  forall T (f : T -> nat) (A B : T -> Prop) a b,
    (forall (x y : T), decidable (x = y))
    -> weight f A a
    -> weight f B b
    -> a < b
    -> exists x, ~ A x /\ B x.
Proof.
intros T f A B m n Hdec HcardA HcardB Hlt.
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

(* nil *)
{
intros a Hlen.
cbn in Hlen.
omega.
}

(* cons *)
{
intros x b Hninb Hdistb IH a Hlen.
so (dec_In _ x a Hdec) as [Hin | Hnina].
  {
  so (in_split _#3 Hin) as (a1 & a2 & ->).
  exploit (IH (a1 ++ a2)) as H.
    {
    rewrite -> sumweight_app in Hlen |- *.
    rewrite -> !sumweight_cons in Hlen.
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


Lemma weight_corr_le :
  forall S T (f : S -> nat) (g : T -> nat) (P : S -> Prop) (Q : T -> Prop) (R : S -> T -> Prop) p q,
    (forall x x' y, P x -> P x' -> Q y -> R x y -> R x' y -> x = x')
    -> (forall x, P x -> exists y, R x y /\ Q y /\ f x <= g y)
    -> weight f P p
    -> weight g Q q
    -> p <= q.
Proof.
intros S T f g P Q R np nq Hinj Hdef HcardP HcardQ.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
destruct HcardQ as (q & Hdistq & Hq & Hlenq).
subst np nq.
cut (exists r,
       NoDup r
       /\ (forall x, In x r -> Q x /\ exists y, In y p /\ R y x)
       /\ sumweight f p <= sumweight g r).
  {
  intros (r & Hdistr & Hr & Hlenr).
  rewrite -> Hlenr.
  apply incl_weight; auto.
  intros x Hx.
  apply Hq.
  apply Hr; auto.
  }
so (fun x => Hp x ander) as H.
clear Hp.
revert H.
induct Hdistp.

(* nil *)
{
intros _.
exists nil.
do2 2 split; auto.
  { apply NoDup_nil. }
intros x Hx.
destruct Hx.
}

(* cons *)
{
intros x p Hnin _ IH Hp.
exploit (Hp x) as Hx.
  {
  left; auto.
  }
so (Hdef x Hx) as (y & Hxy & Hy & Hle).
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
  rewrite -> !sumweight_cons.
  omega.
  }
}
Qed.


Lemma weight_corr_eq :
  forall S T (f : S -> nat) (g : T -> nat) (P : S -> Prop) (Q : T -> Prop) (R : S -> T -> Prop) p q,
    (forall x x' y, P x -> P x' -> Q y -> R x y -> R x' y -> x = x')
    -> (forall x y y', P x -> Q y -> Q y' -> R x y -> R x y' -> y = y')
    -> (forall x, P x -> exists y, R x y /\ Q y /\ f x = g y)
    -> (forall y, Q y -> exists x, R x y /\ P x /\ f x = g y)
    -> weight f P p
    -> weight g Q q
    -> p = q.
Proof.
intros S T f g P Q R p q Hinj Hfun Hdef Hsur HcardP HcardQ.
exploit (weight_corr_le S T f g P Q R p q); auto.
  {
  intros x Hx.
  so (Hdef x Hx) as (y & Hxy & Hy & Heq).
  exists y.
  do2 2 split; auto.
  omega.
  }
exploit (weight_corr_le T S g f Q P (fun x y => R y x) q p); auto.
  {
  intros.
  eapply Hfun; eauto.
  }

  {
  intros x Hx.
  so (Hsur x Hx) as (y & Hxy & Hy & Heq).
  exists y.
  do2 2 split; auto.
  omega.
  }
omega.
Qed.


Lemma weight_map_inj :
  forall S T (g : S -> nat) (h : T -> nat) (P : S -> Prop) (Q : T -> Prop) (f : S -> T) p q,
    (forall x, P x -> Q (f x) /\ g x <= h (f x))
    -> (forall x y, P x -> P y -> f x = f y -> x = y)
    -> weight g P p
    -> weight h Q q
    -> p <= q.
Proof.
intros S T g h P Q f m n Hincl Hinj HcardP HcardQ.
apply (weight_corr_le S T g h P Q (fun x y => f x = y) m n); auto.
  {
  intros x x' y Hx Hx' Hy Heq Heq'.
  apply Hinj; auto.
  transitivity y; auto.
  }

  {
  intros x Hx.
  so (Hincl x Hx) as (Hy & Hle).
  exists (f x).
  do2 2 split; auto.
  }
Qed.


Lemma weight_map_surj :
  forall S T (g : S -> nat) (h : T -> nat) (P : S -> Prop) (Q : T -> Prop) (f : T -> S) p q,
    (forall x, Q x -> P (f x) /\ g (f x) <= h x)
    -> (forall x, P x -> exists y, Q y /\ x = f y)
    -> weight g P p
    -> weight h Q q
    -> p <= q.
Proof.
intros S T g h P Q f m n Hincl Hsurj HcardP HcardQ.
apply (weight_corr_le S T g h P Q (fun x y => x = f y) m n); auto.
  {
  intros x x' y Hx Hx' Hy Heq Heq'.
  transitivity (f y); auto.
  }

  {
  intros x Hx.
  so (Hsurj x Hx) as (y & Hy & Heq).
  subst x.
  exists y.
  do2 2 split; auto.
  exact (Hincl _ Hy ander).
  }
Qed.



Lemma weight_incl :
  forall T (f : T -> nat) (P Q : T -> Prop) p q,
    incl P Q
    -> weight f P p
    -> weight f Q q
    -> p <= q.
Proof.
intros T f P Q p q HPQ Hp Hq.
eapply weight_map_inj with (f := (fun x => x)) (P := P) (Q := Q); eauto.
Qed.


(* Strange that these aren't in the library *)

Lemma fold_right_map :
  forall S T U (f : S -> T) (g : T -> U -> U) (l : list S) (x : U),
    fold_right g x (map f l) = fold_right (fun y z => g (f y) z) x l.
Proof.
intros S T U f g l x.
induct l; auto.
(* cons *)
intros y l IH.
cbn.
rewrite -> IH.
reflexivity.
Qed.


Lemma fold_right_ext_in :
  forall T U (f f' : T -> U -> U) (l : list T) (x : U),
    (forall y z, In y l -> f y z = f' y z)
    -> fold_right f x l = fold_right f' x l.
Proof.
intros T U f f' l x.
induct l; auto.
(* cons *)
intros y l IH Hext.
cbn.
rewrite <- IH.
  {
  apply Hext.
  left; auto.
  }

  {
  intros t u Ht.
  apply Hext.
  right; auto.
  }
Qed.


Lemma weight_image :
  forall S T (g : S -> nat) (h : T -> nat) (P : S -> Prop) (f : S -> T) n,
    (forall x, P x -> g x = h (f x))
    -> (forall x y, P x -> P y -> f x = f y -> x = y)
    -> weight g P n
    -> weight h (fun x => exists y, x = f y /\ P y) n.
Proof.
intros S T g h P f n Hwt Hinj HcardP.
destruct HcardP as (p & Hdistp & Hp & Hlenp).
exists (map f p).
do2 2 split.
  {
  so (fun x => Hp x ander) as H.
  revert H.
  clear Hp Hlenp.
  induct Hdistp.
    (* nil *)
    {
    intros _.
    apply NoDup_nil.
    }
    
    (* cons *)
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
  unfold sumweight.
  rewrite -> fold_right_map.
  unfold sumweight in Hlenp.
  force_exact Hlenp.
  f_equal.
  apply fold_right_ext_in.
  intros y z Hy.
  f_equal.
  apply Hwt.
  apply Hp; auto.
  }
Qed.


Lemma weight_finite :
  forall T (f : T -> nat) (P : T -> Prop) n, weight f P n -> finite P.
Proof.
intros T f P n Hcard.
destruct Hcard as (l & _ & H & _).
exists l.
intros; apply H; auto.
Qed.


Lemma finite_weight :
  forall T (f : T -> nat) (P : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> finite P
    -> exists n, weight f P n.
Proof.
intros T f P Hdeceq Hfin.
destruct Hfin as (l & Hl).
so (deduplicate _ l Hdeceq) as (l' & Hdist & Hl').
exists (sumweight f l').
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


Lemma weight_gt_decide :
  forall (T : Type) (f : T -> nat) (P U : T -> Prop) n n',
    (forall x, decidable (P x))
    -> incl P U
    -> weight f U n
    -> decidable (exists p, weight f P p /\ p > n').
Proof.
intros T f P U n n' Hdec HPU HcardU.
so HcardU as (u & Hdist & Hu & Hlenu).
so (enumerate_subset _#3 (fun x _ => Hdec x) Hdist) as (p & Hdistp & Hp).
so (le_lt_dec (sumweight f p) n') as [Hle | Hlt].
2:{
  left.
  exists (sumweight f p).
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
exploit (permutation_weight' _ f p p') as Heq; auto.
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


Definition weight_lt {T : Type} (f : T -> nat) (P : T -> Prop) (n : nat) : Prop
  :=
  ~ exists l,
      NoDup l
      /\ (forall x, In x l -> P x)
      /\ sumweight f l >= n.


Lemma weight_impl_weight_lt :
  forall T (f : T -> nat) (P : T -> Prop) m n,
    m < n
    -> weight f P m
    -> weight_lt f P n.
Proof.
intros T f P m n Hlt Hcard.
destruct Hcard as (k & Hdistk & Hk & Hlenk).
intros (l & Hdistl & Hl & Hlenl).
exploit (incl_weight _ f l k) as Hleq; auto.
  {
  intros x Hx.
  apply Hk.
  apply Hl; auto.
  }
omega.
Qed.


Lemma weight_lt_increase :
  forall T (f : T -> nat) (P : T -> Prop) m n,
    m <= n
    -> weight_lt f P m
    -> weight_lt f P n.
Proof.
intros T f P m n Hleq Hcard.
unfold weight_lt in *.
contradict Hcard.
destruct Hcard as (l & Hdist & Hl & Hlen).
exists l.
do2 2 split; auto.
omega.
Qed.


Lemma weight_lt_impl_lt :
  forall T (f : T -> nat) (P Q : T -> Prop) p q,
    incl P Q
    -> weight f P p
    -> weight_lt f Q q
    -> p < q.
Proof.
intros T f P Q p q HPQ Hp Hq.
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


Lemma weight_lt_by_contradiction :
  forall T (f : T -> nat) (P : T -> Prop) p,
    (forall Q q, incl Q P -> weight f Q q -> q >= p -> False)
    -> weight_lt f P p.
Proof.
intros T f P p Hprop.
intros (l & Hdist & Hl & Hlen).
apply (Hprop (fun x => In x l) (sumweight f l)); auto.
exists l.
do2 2 split; auto.
intro; split; auto.
Qed.
