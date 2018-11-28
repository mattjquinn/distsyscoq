(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Bool.
Require Import List.
Require Export Decidable.

Require Import Tact.
Require Import Relation.


Definition incl {T : Type} (P Q : T -> Prop) :=
  forall x, P x -> Q x.


(** Kuratowski finite, I think. *)
Definition finite {T : Type} (P : T -> Prop) : Prop
  :=
  exists l, forall x, P x <-> In x l.


Lemma Is_true_decide :
  forall b, decidable (Is_true b).
Proof.
intro b.
destruct b.
  {
  left.
  exact I.
  }

  {
  right.
  intros H.
  destruct H.
  }
Qed.


Lemma dec_In :
  forall (T : Type) (x : T) (l : list T),
    (forall (x y : T), decidable (x = y))
    -> decidable (In x l).
Proof.
intros T x l Hdeceq.
induct l.

(** nil *)
{
right.
intro H.
destruct H.
}

(** cons *)
{
intros y l IH.
so (Hdeceq x y) as [Heq | Hneq].
  {
  subst.
  left; left; reflexivity.
  }

  {
  destruct IH as [Hin | Hnin].
    {
    left; right; auto.
    }

    {
    right.
    intro H.
    destruct H.
      {
      subst.
      destruct Hneq; reflexivity.
      }

      {
      contradiction.
      }
    }
  }
}
Qed.


Lemma dec_and_dep :
  forall P Q,
    decidable P
    -> (P -> decidable Q)
    -> decidable (P /\ Q).
Proof.
intros P Q HdecP HdecQ.
so HdecP as [Hyes | Hno].
  {
  so (HdecQ Hyes) as [Hyes' | Hno].
    {
    left; auto.
    }
  right.
  contradict Hno.
  destruct Hno; auto.
  }
right.
contradict Hno.
destruct Hno; auto.
Qed.


Lemma dec_equiv :
  forall (P Q : Prop),
    (P <-> Q)
    -> decidable P
    -> decidable Q.
Proof.
intros P Q Hiff Hdec.
destruct Hdec as [Hyes | Hno].
  {
  left.
  apply Hiff; auto.
  }

  {
  right.
  contradict Hno.
  apply Hiff; auto.
  }
Qed.


Lemma finite_decide :
  forall (T : Type) (P : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> finite P
    -> forall x, decidable (P x).
Proof.
intros T P Hdec Hfin x.
destruct Hfin as (l & Hl).
apply (dec_equiv (In x l)).
  {
  split.
    { intro H; apply Hl; auto. }

    { intro H; apply Hl; auto. }
  }
apply dec_In; auto.
Qed.


Lemma dec_exists_finite :
  forall (T : Type) (P Q : T -> Prop),
    incl P Q
    -> finite Q
    -> (forall x, decidable (P x))
    -> decidable (exists x, P x).
Proof.
intros T P Q HPQ Hfin Hdec.
destruct Hfin as (l & Hl).
cut (decidable (exists x, In x l /\ P x)).
  {
  intro H.
  destruct H as [Hyes | Hno].
    {
    left.
    destruct Hyes as (x & _ & Hx).
    exists x; auto.
    }

    {
    right.
    contradict Hno.
    destruct Hno as (x & Hx).
    exists x.
    split; auto.
    apply Hl; auto.
    }
  }
clear Hl.
induct l.

(** nil *)
{
right.
intro H.
destruct H as (x & Hin & _).
destruct Hin.
}

(** cons *)
{
intros x l IH.
so (Hdec x) as [Hyes | Hno].
  {
  left.
  exists x.
  split; auto.
  left; auto.
  }
destruct IH as [Hyes | Hno'].
  {
  destruct Hyes as (y & Hiny & Hy).
  left.
  exists y.
  split; auto.
  right; auto.
  }
right.
intros (y & Hiny & Hy).
destruct Hiny as [Heq | Hiny'].
  {
  subst y.
  contradiction.
  }
destruct Hno'.
eexists; eauto.
}
Qed.


Lemma dec_forall_imp_finite :
  forall (T : Type) (P Q : T -> Prop),
    finite P
    -> (forall x, P x -> decidable (Q x))
    -> decidable (forall x, P x -> Q x).
Proof.
intros T P Q Hfinite Hdec.
destruct Hfinite as (p & Hp).
apply (dec_equiv (forall x, In x p -> Q x)).
  {
  split.
    {
    intros Hall x Hx.
    apply Hall.
    apply Hp; auto.
    }

    {
    intros Hall x Hx.
    apply Hall.
    apply Hp; auto.
    }
  }
so (fun x Hx => Hp x ander Hx) as H.
clear Hp.
revert H.
induct p.

(** nil *)
{
intros _.
left.
intros x Hx.
destruct Hx.
}

(** cons *)
{
intros x p IH Hp.
exploit IH as H.
  {
  intros y Hy.
  apply Hp.
  right; auto.
  }
destruct H as [Hall | Hnall].
2:{
  right.
  contradict Hnall.
  intros y Hy.
  apply Hnall.
  right; auto.
  }
exploit (Hdec x) as H.
  {
  apply Hp.
  left; auto.
  }
destruct H as [HQx | HnQx].
2:{
  right.
  contradict HnQx.
  apply HnQx.
  left; auto.
  }
left.
intros y Hy.
destruct Hy as [Hy | Hy].
  {
  subst y.
  exact HQx.
  }

  {
  apply Hall; auto.
  }
}
Qed.


Lemma finite_equiv :
  forall (T : Type) (P Q : T -> Prop),
    (forall x, P x <-> Q x)
    -> finite P
    -> finite Q.
Proof.
intros T P Q HPQ Hfin.
destruct Hfin as (l & Hl).
exists l.
intros x.
rewrite <- HPQ.
rewrite -> Hl.
reflexivity.
Qed.


Lemma filter_to_finite :
  forall T (P : T -> Prop) l,
    (forall x, decidable (P x))
    -> (forall x, P x -> In x l)
    -> finite P.
Proof.
intros T P l Hdec Hl.
cut (exists l', forall x, In x l' <-> (In x l /\ P x)).
  {
  intros H.
  destruct H as (l' & Hl').
  exists l'.
  intros x.
  split.
    {
    intro Hx.
    apply Hl'; auto.
    }

    {
    intro Hx.
    apply Hl'; auto.
    }
  }
clear Hl.
induct l.

(** nil *)
{
exists nil.
intros x.
split.
  {
  intros H.
  destruct H.
  }

  {
  intros (H & _).
  destruct H.
  }
}

(** cons *)
{
intros x l IH.
destruct IH as (l' & Hl').
so (Hdec x) as [HPx | HnPx].
  {
  exists (cons x l').
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

      {
      split.
        {
        right.
        apply Hl'; auto.
        }

        {
        apply Hl'; auto.
        }
      }
    }

    {
    intros (Hy & HPy).
    destruct Hy as [Heq | Hy].
      {
      subst y.
      left; auto.
      }

      {
      right.
      apply Hl'; auto.
      }
    }
  }

  {
  exists l'.
  intros y.
  split.
    {
    intro Hy.
    split.
      {
      right.
      apply Hl'; auto.
      }

      { apply Hl'; auto. }
    }

    {
    intros (Hy & HPy).
    destruct Hy as [Heq | Hy].
      {
      subst y.
      contradiction.
      }

      {
      apply Hl'; auto.
      }
    }
  }
}
Qed.    


Lemma finite_subset :
  forall T (P Q : T -> Prop),
    incl P Q
    -> (forall x, decidable (P x))
    -> finite Q
    -> finite P.
Proof.
intros T P Q Hincl Hdec HQ.
destruct HQ as (l & Hl).
apply (filter_to_finite _ _ l); auto.
intros x Hx.
apply Hl.
apply Hincl; auto.
Qed.


Lemma finite_subset' :
  forall T (P Q : T -> Prop),
    (forall (x y : T), decidable (x = y))
    -> incl P Q
    -> (forall x, Q x -> decidable (P x))
    -> finite Q
    -> finite P.
Proof.
intros T P Q Hdeceq Hincl Hdec HQ.
so HQ as (l & Hl).
apply (filter_to_finite _ _ l); auto.
  {
  intro x.
  so (finite_decide _ _ Hdeceq HQ x) as [HQx | HnQx].
    {
    apply Hdec; auto.
    }

    {
    right.
    contradict HnQx.
    apply Hincl; auto.
    }
  }

  {
  intros x Hx.
  apply Hl.
  apply Hincl; auto.
  }
Qed.


Lemma finite_plus :
  forall (T : Type) (R : T -> T -> Prop) x,
    well_founded R
    -> (forall x y, decidable (R x y))
    -> (forall x, finite (fun y => R y x))
    -> finite (fun y => plus R y x).
Proof.
intros T R x Hwf Hdec Hfin.
wfinduct x using Hwf.
intros x IH.
so (Hfin x) as (l & Hl).
cut (exists m, forall y, (exists z, star R y z /\ R z x /\ In z l) <-> In y m).
  {
  intro H.
  destruct H as (m & Hm).
  exists m.
  intros y.
  split.
    {
    intro Hyx.
    apply Hm.
    so (plus_plusr _#4 Hyx) as (z & Hyz & Hzx).
    exists z.
    do2 2 split; auto.
    apply Hl; auto.
    }

    {
    intros Hy.
    so (Hm y ander Hy) as (z & Hyz & Hxz & Hz).
    apply plusr_plus.
    exists z; auto.
    }
  }
clear Hl.
induct l.

(** nil *)
{
exists nil.
intros y.
split.
  {
  intros (z & _ & _ & Hinz).
  destruct Hinz.
  }

  {
  intros Hiny.
  destruct Hiny.
  }
}

(** cons *)
{
intros z l IHl.
so (Hdec z x) as [Hzx | Hnxz].
  {
  so (IH _ Hzx) as (m1 & Hm1).
  destruct IHl as (m2 & Hm2).
  exists (z :: m1 ++ m2).
  intro y.
  split.
    {
    intros Hy.
    destruct Hy as (w & Hyw & Hwx & Hinw).
    destruct Hinw as [Heq | Hinw].
      {
      subst w.
      so (star_plus _#4 Hyw) as [Heq | Hyw'].
        {
        subst y.
        left; auto.
        }
      right.
      apply in_or_app.
      left.
      apply Hm1; auto.
      }
  
      {
      right.
      apply in_or_app.
      right.
      apply Hm2.
      exists w.
      auto.
      }
    }

    {
    intros Hiny.
    destruct Hiny as [Heq | Hiny].
      {
      subst z.
      exists y.
      do2 2 split; auto using star_refl.
      left; auto.
      }

      {
      so (in_app_or _#4 Hiny) as [Hiny' | Hiny'].
        {
        so (Hm1 _ ander Hiny') as Hyz.
        exists z.
        do2 2 split; auto.
          { apply plus_star; auto. }

          { left; auto. }
        }

        {
        so (Hm2 _ ander Hiny') as (w & Hyw & Hwx & Hinw).
        exists w.
        do2 2 split; auto.
        right; auto.
        }
      }
    }
  }

  {
  destruct IHl as (m2 & Hm2).
  exists m2.
  intro y.
  split.
    {
    intros Hy.
    destruct Hy as (w & Hyw & Hwx & Hinw).
    destruct Hinw as [Heq | Hinw]; auto.
      {
      subst w.
      contradiction.
      }
    apply Hm2.
    exists w.
    auto.
    }

    {
    intro Hiny.
    so (Hm2 _ ander Hiny) as (w & Hyw & Hwx & Hinw).
    exists w.
    do2 2 split; auto.
    right; auto.
    }
  }
}
Qed.


Lemma finite_star :
  forall (T : Type) (R : T -> T -> Prop) x,
    well_founded R
    -> (forall x y, decidable (R x y))
    -> (forall x, finite (fun y => R y x))
    -> finite (fun y => star R y x).
Proof.
intros T R x Hwf Hdec Hfin.
so (finite_plus _ _ x Hwf Hdec Hfin) as (l & Hl).
exists (cons x l).
intro y.
split.
  {
  intro Hyx.
  so (star_plus _#4 Hyx) as [Heq | Hyx'].
    {
    subst y.
    left; auto.
    }
  right.
  apply Hl; auto.
  }

  {
  intros Hiny.
  destruct Hiny as [Heq | Hiny].
    {
    subst y.
    apply star_refl.
    }

    {
    apply plus_star.
    apply Hl; auto.
    }
  }
Qed.


Lemma finite_exists :
  forall (S T : Type) (P : S -> Prop) (Q : S -> T -> Prop),
    finite P
    -> (forall x, P x -> finite (Q x))
    -> finite (fun y => exists x, P x /\ Q x y).
Proof.
intros S T P Q HfinP HfinQ.
destruct HfinP as (p & Hp).
cut (exists l, forall y, (exists x, In x p /\ Q x y) <-> In y l).
  {
  intros (l & Hl).
  exists l.
  intro y.
  split.
    {
    intros (x & Hx & Hxy).
    apply Hl.
    exists x.
    split; auto.
    apply Hp; auto.
    }

    {
    intro Hy.
    so (Hl _ ander Hy) as (x & Hx & Hxy).
    exists x.
    split; auto.
    apply Hp; auto.
    }
  }
so (fun x Hx => Hp x ander Hx) as H.
clear Hp.
revert H.
induct p.

(** nil *)
{
intros Hp.
exists nil.
intro y.
split.
  {
  intros (x & Hx & _).
  destruct Hx.
  }

  {
  intros Hy.
  destruct Hy.
  }
}

(** cons *)
{
intros x p IH Hp.
exploit IH as H.
  {
  intros z Hz.
  apply Hp.
  right.
  auto.
  }
destruct H as (l2 & Hl2).
so (HfinQ x (Hp x (or_introl (eq_refl _)))) as (l1 & Hl1).
exists (l1 ++ l2).
intro y.
split.
  {
  intros (z & Hz & Hzy).
  apply in_or_app.
  destruct Hz as [| Hz].
    {
    subst z.
    left.
    apply Hl1; auto.
    }

    {
    right.
    apply Hl2.
    exists z; auto.
    }
  }

  {
  intros Hy.
  so (in_app_or _#4 Hy) as [Hy' | Hy'].
    {
    so (Hl1 y ander Hy') as Hxy.
    exists x.
    split; auto.
    left; auto.
    }

    {
    so (Hl2 y ander Hy') as (z & Hz & Hzy).
    exists z.
    split; auto.
    right; auto.
    }
  }
}
Qed.
