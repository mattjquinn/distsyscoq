Require Import List.
Require Import Nat.
Require Import String.
Require Import Omega.

Delimit Scope string_scope with string.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition channel : Type := list string.
Record netstate := NetState {t : nat; r : nat; c1 : channel; c2 : channel}.
Definition msg : string := " ""Message."" ".
Definition initial := {| t := 5 ; r := 5 ; c1 := nil ; c2 := nil |}.

Inductive netEvalR : netstate -> netstate -> Prop :=
| Initial : (netEvalR initial initial)
| Step1 : forall st st',
    netEvalR st st' ->
    st'.(t) > 0 ->
    (netEvalR st' {| t := st'.(t) - 1 ; r := st'.(r) ;
                     c1 := msg :: st'.(c1) ; c2 := st'.(c2) |})
| Step2 : forall st st',
    netEvalR st st' ->
    st'.(c2) <> nil ->
    (netEvalR st' {| t := st'.(t) + 1 ; r := st'.(r) ;
                     c1 := st'.(c1) ; c2 := (tl st'.(c2)) |})
| Step3 : forall st st',
    netEvalR st st' ->
    st'.(c1) <> nil ->
    (netEvalR st' {| t := st'.(t) ; r := st'.(r) + 1 ;
                    c1 := (tl st'.(c1)) ; c2 := st'.(c2) |})
| Step4 : forall st st',
    netEvalR st st' ->
    st'.(r) > 0 ->
    (netEvalR st' {| t := st'.(t) ; r := st'.(r) - 1 ;
                     c1 := st'.(c1) ; c2 := (msg :: st'.(c2)) |}).

Definition safety1 (st' : netstate) : Prop := st'.(t) >= 0 /\ st'.(r) >= 0.
      
Lemma safety1_holds: forall st st' : netstate,
         (netEvalR st st') ->
         safety1 st'.
Proof.
  intros st st' H. split.
  - inversion H; omega. 
  - inversion H; omega.
Qed.


Lemma nonempty_list_tail_len {A : Type} : forall (l : list A) ,
    l <> nil ->
    (List.length (tl l)) = (List.length l) - 1.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. omega.
Qed.

Lemma nonempty_list_len {A : Type} : forall (l : list A),
    l <> nil ->
    List.length l > 0.
Proof.
  intros. induction l.
  - destruct H. reflexivity.
  - simpl. omega.
Qed.

Definition safety2 (st' : netstate) : Prop :=
    (List.length st'.(c1) + List.length st'.(c2) + st'.(t) + st'.(r))  = 10.

Lemma safety2_holds : forall st st' : netstate,
    (netEvalR st st') ->
    safety2 st'.
  Proof.
  intros. unfold safety2. induction H; simpl.
  - reflexivity.
  - omega.
  - remember H0 as H1. clear HeqH1.
    apply nonempty_list_tail_len in H0. apply nonempty_list_len in H1. omega.
  - remember H0 as H1. clear HeqH1.
    apply nonempty_list_tail_len in H0. apply nonempty_list_len in H1. omega.
  - omega.
Qed.

Theorem safety_holds : forall st st' : netstate,
      (netEvalR st st') -> safety1 st' /\ safety2 st'.
Proof.
  intros. split. apply (safety1_holds st st'). assumption.
  apply (safety2_holds st st'). assumption.
Qed.