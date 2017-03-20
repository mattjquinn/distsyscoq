Require Export MQuinnLists.

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1: repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
Example test_repeat2: repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X : Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* d (b a 5) : is not well-typed; it lacks a type argument; should be: *)
Check d nat (b a 5).
(* d mumble (b a 5) : is well-typed. *)
Check d mumble (b a 5).
(* d bool (b a 5) : is well-typed. *)
Check d bool (b a 5).
(* e bool true : is well-typed. *)
Check e bool true.
(* e mumble (b c 0) : is well-typed. *)
Check e mumble (b c 0).
(* e bool (b c 0) : is not well-typed; (b c 0) is not of type bool; should be: *)
Check e mumble (b c 0).
(* c : is well-typed. *)
Check c.

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.
Check repeat.
