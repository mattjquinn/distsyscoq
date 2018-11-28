Require Export MQuinnIndProp.

Print ev.

Check ev_SS.

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print ev_4. (* EXAMPLE OF A PROOF OBJECT *)

Check (ev_SS 2 (ev_SS 0 ev_0)).

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.
Print ev_4'.
Print ev_4''.
Print ev_4'''.

Theorem ev_8 : ev 8.
Proof. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS. apply ev_SS. apply H. Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) => ev_SS (S (S n)) (ev_SS n H).
Check ev_plus4'.

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).
Check ev_plus4''.

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).
Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).
Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

Definition add1 : nat -> nat.
Show Proof.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.
(* Not completely sure about the reason for using 'Defined'
   here instead of 'Qed' as it relates to definition "transparency"
   but I'm letting that go for now. *)

Print add1.
Compute add1 2.

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

Print prod.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).
Print and_comm'.

Definition conj_fact_aux P Q R (H1 : P /\ Q) (H2 : Q /\ R) :=
  match H1 with
  | conj HP _ =>
    match H2 with
    | conj _ HR => conj HP HR
    end
  end.

Lemma conj_fact' : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
Proof. intros P Q R H1 H2. apply (conj_fact_aux P Q R H1 H2). Qed.

Definition conj_fact: forall P Q R, (P /\ Q) -> (Q /\ R) -> (P /\ R) :=
  conj_fact_aux.
Print conj_fact.

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

End Or.

Definition or_comm_aux P Q (H : P \/ Q) :=
  match H with
  | or_introl P => or_intror P
  | or_intror Q => or_introl Q
  end.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P := or_comm_aux.

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

End Ex.

Check ex (fun n => ev n).

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 3 (ev_SS 2 (ev_SS 0 ev_0)).

Inductive True : Prop :=
  | I : True.

Inductive False : Prop :=.

End Props.

Module MyEquality.

Inductive eq {X : Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity) : type_scope.

Lemma leibniz_equality : forall (X : Type) (x y : X),
  x = y -> forall P : X -> Prop, P x -> P y.
Proof.
  intros X x y H1 P H2. destruct H1. apply H2. Qed.

Lemma four: 2 + 2 = 1 + 3.
Proof. apply eq_refl. Qed.

Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X : Set) (x : X),
  [] ++ [x] = x :: [] :=
    fun (X : Set) (x : X) => eq_refl [x].

End MyEquality.

Definition quiz6 : exists x, x + 3 = 4 :=
  ex_intro (fun z => (z + 3 = 4)) 1 (refl_equal 4).