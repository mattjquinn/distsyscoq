Require Import List.
Require Import Nat.
Require Import String.

Delimit Scope string_scope with string.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition channel : Type := list string.

Inductive node : Type :=
| Node : nat -> node.

Definition lvar (n : node) : nat := match n with | Node lv => lv end.

Definition msg : string := " ""Message."" ".

Inductive netEvalR : node -> node -> channel -> channel -> Prop :=
| Step1 : forall n1 n2 c1 c2,
    lvar n1 > 0 ->
    (netEvalR (Node (lvar n1 - 1)) n2 (msg :: c1) c2)
| Step2 : forall n1 n2 c1 c2,
    c2 <> nil ->
    (netEvalR (Node (lvar n1 + 1)) n2 c1 (tl c2))
| Step3 : forall n1 n2 c1 c2,
    c1 <> nil ->
    (netEvalR n1 (Node (lvar n2 + 1)) (tl c1) c2)
| Step4 : forall n1 n2 c1 c2,
    lvar n2 > 0 ->
    (netEvalR n1 (Node (lvar n2 - 1)) c1 (msg :: c2)).

Definition T : node := Node 5.
Definition R : node := Node 5.
Definition c1 : channel := nil.
Definition c2 : channel := nil.

