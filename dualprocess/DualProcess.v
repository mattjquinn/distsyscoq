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
      
Lemma safety1_holds: forall st st' : netstate,
         (netEvalR st st') ->
         st'.(t) >= 0 /\ st'.(r) >= 0.
Proof.
  intros st st' H. split.
  - inversion H; omega. 
  - inversion H; omega.
Qed.

Lemma safety2_holds : forall st st' : netstate,
    (netEvalR st st') ->
    (List.length st'.(c1) + List.length st'.(c2) + st'.(t) + st'.(r))  = 10.
Proof.
  intros. induction H; simpl.
  - reflexivity.
  - omega.
  - admit. (* For this and next case, must use H0's assumption of nonempty list
              to show that tail will reduce by 1, canceled out by + 1 in other term. *)
  - admit.
  - omega.
Qed.
