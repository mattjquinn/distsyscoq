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
| Step1 : forall st,
    st.(t) > 0 ->
    (netEvalR st {| t := st.(t) - 1 ; r := st.(r) ;
                    c1 := msg :: st.(c1) ; c2 := st.(c2) |})
| Step2 : forall st,
    st.(c2) <> nil ->
    (netEvalR st {| t := st.(t) + 1 ; r := st.(r) ;
                    c1 := st.(c1) ; c2 := (tl st.(c2)) |}).
(*
| Step3 : forall n1 n2 c1 c2,
    c1 <> nil ->
    (netEvalR n1 (Node (lvar n2 + 1)) (tl c1) c2)
| Step4 : forall n1 n2 c1 c2,
    lvar n2 > 0 ->
    (netEvalR n1 (Node (lvar n2 - 1)) c1 (msg :: c2)).
*)

Theorem safety_holds: forall st st' : netstate,
         (netEvalR st st') ->
         st'.(t) >= 0 /\ st'.(r) >= 0.
Proof.
  intros st st' H. split.
  - inversion H. omega. omega. omega.
  - inversion H. omega. omega. omega.
Qed.