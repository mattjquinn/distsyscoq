Require Import Arith List Omega.

Require Import Cpdt.CpdtTactics Cpdt.Coinductive.

Require Extraction.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
    | nil => x :: nil
    | h :: ls' =>
      if le x h
      then x :: ls
      else h :: insert x ls'
    end.

  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
    | nil => ls2
    | h :: ls' => insert h (merge ls' ls2)
    end.

  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
    | nil => (nil, nil)
    | h :: nil => (h :: nil, nil)
    | h1 :: h2 :: ls' =>
      let (ls1, ls2) := split ls' in
      (h1 :: ls1, h2 :: ls2)
    end.

  (*Fixpoint mergeSort (ls : list A) : list A :=
    if leb (length ls) 1
    then ls
    else let lss := split ls in
         merge (mergeSort (fst lss)) (mergeSort (snd lss)). *)

  Print well_founded.
  Print Acc.

  CoInductive infiniteDecreasingChain A (R : A -> A -> Prop) : stream A -> Prop :=
  | ChainCons : forall x y s, infiniteDecreasingChain R (Cons y s)
                              -> R y x
                              -> infiniteDecreasingChain R (Cons x (Cons y s)).

  Lemma noBadChains' : forall A (R : A -> A -> Prop) x, Acc R x
                                                        -> forall s, ~infiniteDecreasingChain R (Cons x s).
    induction 1; crush;
      match goal with
      | [ H : infiniteDecreasingChain _ _ |- _ ] => inversion H; eauto
      end.
  Qed.

  Theorem noBadChains : forall A (R : A -> A -> Prop), well_founded R
                                                       -> forall s, ~infiniteDecreasingChain R s.
    destruct s; apply noBadChains'; auto.
  Qed.

  
      
  