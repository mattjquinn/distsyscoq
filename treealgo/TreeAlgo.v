Add Rec LoadPath "GraphBasics" as GraphBasics.

Require Import List String Omega ZArith.
Require Import GraphBasics.Acyclic.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition msg := nat.

Inductive edge (v1 v2 : nat) (msgs : list msg): Type :=
  | Edge : edge v1 v2 msgs.

Inductive node (vid : nat) (edges : list edge) : Type :=
  | Node : node vid edges.

(* IDEA: Before representing as actual acyclic graphs, make a simpler
   representation using lists of vertices/edges and prove the in-book
   example configuration first.*)
Definition p := 0.
Definition q := 1.
Definition nodes := [p].


Definition v0 := (index 0).
Definition vset0 := V_empty.
Definition aset0 := A_empty.
Definition testg0 := (AC_vertex vset0 aset0 AC_empty v0).
Print testg0.
Definition test := testg0 (v0 In vset0).
Definition v1 := (index 1).
Definition vset1 := (V_union (V_single v0) vset0).
Definition aset1 := A_empty.
Definition testg1 := (AC_leaf vset1 aset1 (testg0 v0 v1)) v0.
Print testg.

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
  intros st st' H. split; induction H; simpl; omega.
Qed.

Definition safety2 (st' : netstate) : Prop :=
  Zlength st'.(c1) + Zlength st'.(c2) + st'.(t) + st'.(r) = 10.

Lemma safety2_holds : forall st st' : netstate,
    (netEvalR st st') ->
    safety2 st'.
Proof.
  intros st st' H. unfold safety2. induction H; simpl;
    try reflexivity;                           (* Initial state *)
    try (rewrite Zlength_cons; omega);         (* Steps 1 and 4 *)
    [destruct (c2 st') | destruct (c1 st')];   (* Steps 2 and 3 *)
      try contradiction;
      (simpl; rewrite Zlength_cons in IHnetEvalR; omega).
Qed.

Theorem safety_holds : forall st st' : netstate,
      (netEvalR st st') -> safety1 st' /\ safety2 st'.
Proof.
  intros st st' H. split;
  [apply (safety1_holds st st') | apply (safety2_holds st st')];
    assumption.
Qed.