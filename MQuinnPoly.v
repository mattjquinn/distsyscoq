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

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 := cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X:Type} (x:X) (count:nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

Fixpoint app {X:Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1:
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.
Definition mynil : list nat := nil.

Check @nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123''' := [1; 2; 3].