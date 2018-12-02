Require Import List String Omega ZArith.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition channel : Type := list string.
Definition msg : string := " ""Message."" ".
Record netstate := NetState {t : Z; r : Z; c1 : channel; c2 : channel}.
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