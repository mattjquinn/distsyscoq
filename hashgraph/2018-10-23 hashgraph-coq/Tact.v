(** Copyright (c) 2018 by Karl Crary

  Permission is hereby granted, free of charge, to any person obtaining
  a copy of this software and associated documentation files (the
  "Software"), to deal in the Software without restriction, including
  without limitation the rights to use, copy, modify, merge, publish,
  distribute, sublicense, and/or sell copies of the Software, and to
  permit persons to whom the Software is furnished to do so, subject to
  the following conditions:

  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
*)

Require Import EqdepFacts.
Require Import Eqdep_dec.


(** UIP *)

Lemma inj_pair2_UIP :
  forall (A : Type),
    (forall (x y : A) (p1 p2 : x = y), p1 = p2)
    -> forall (P : A -> Type) (p : A) (x y: P p),
         existT P p x = existT P p y
         -> x = y.
Proof.
intros A Huip P p x y Heq.
apply eq_dep_eq__inj_pair2; auto; [].
apply eq_rect_eq__eq_dep_eq; [].
apply Streicher_K__eq_rect_eq; [].
apply UIP_refl__Streicher_K; [].
apply UIP__UIP_refl; auto.
Qed.


Hint Resolve UIP_dec : uip.


(** Simpler induction. *)

Tactic Notation "clear" "codependent" hyp(H)
  :=
  let T := type of H
  in
    clear H;
    repeat
      (match goal with
         x:_ |- _ =>
           (match T with
              context [x] => 
                (** This might fail because:
                   * x is mentioned in a hyp that should have been reverted but wasn't,
                     so leaving it is necessary; or
                   * x is fixed (ie, non-inductive) argument to H,
                     so leaving it is actually desired.
                *)
                clear x
            end)
       end).


Tactic Notation "induct" hyp(H)
  :=
  elim H;
  clear codependent H.


Tactic Notation "cases" hyp(H)
  :=
  case H;
  clear codependent H.


Tactic Notation "induct" hyp(H) "using" constr(ind)
  :=
  elim H using ind;
  clear codependent H.


Tactic Notation "wfinduct" hyp(H) "using" constr(T) :=
  revert H;
  match goal with
  | |- forall x, @?P x => apply (well_founded_ind T P)
  end.



(** Better inversion *)

Definition Marker_invert := True.

(** Intro down to marker, split equalities, subst redundant variables, and revert back. *)
Ltac invproc stac rtac :=
  (lazymatch goal with
   | |- Marker_invert -> _ => intros _; stac; rtac

   | |- ?x = ?x -> _ => intros _; invproc stac rtac

   | |- existT _ ?p ?x = existT _ ?p ?y -> _ =>
       let H := fresh "Heq" in
       let H' := fresh
       in
         intro H;
         first
         [
           assert (x = y) as H';
           [
             refine (inj_pair2_UIP _ _ _ _ _ _ H); auto with uip eqdec; fail
           |
             clear H;
             revert H';
             invproc stac rtac
           ]
         |
           invproc stac ltac:(try (revert H); rtac)
         ]

   | |- _ = _ -> _ =>
       let H := fresh "Heq"
       in
         intro H;
         first
         [
           injection H;
           clear H;
           invproc stac rtac
         |
           invproc stac ltac:(try (revert H); rtac)
         ]

   | |- forall (x : _), _ =>
       let y := fresh x
       in
         intro y;
         invproc ltac:(try (subst y); stac) ltac:(try (revert y); rtac)

   end).


Tactic Notation "invert" constr(t) :=
  let Hinv := fresh in
  let Hgoal := fresh in
  let Hmark1 := fresh in
  let Hmark2 := fresh
  in
    (** Keep inversion from messing with the goal. *)
    (lazymatch goal with
     | |- ?T => change (let Hgoal := T in Hgoal); intro Hgoal
     end);
    pose proof t as Hinv;
    assert Marker_invert as Hmark1; [exact I | pose proof Hmark1 as Hmark2; revert Hmark2];
    inversion Hinv;
    clear Hinv;
    subst Hgoal;  (** Put the goal back. *)
    repeat
      (lazymatch goal with
       | H : ?T |- _ =>
           (lazymatch T with
            | Marker_invert => fail
            | _ => revert H
            end)
       end);
    clear Hmark1;
    invproc idtac idtac.


Tactic Notation "invertc" hyp(H) :=
  invert H; clear H.


(** Use a hypothesis/lemma. *)

Ltac exploit_main t T pat cleanup
  :=
  (lazymatch T with
   | ?U1 -> ?U2 =>
       let H := fresh
       in
         assert U1 as H;
         [cleanup () | exploit_main (t H) U2 pat ltac:(fun _ => clear H; cleanup ())]
   | _ =>
       pose proof t as pat;
       cleanup ()
   end).


Tactic Notation "exploit" constr(t) "as" simple_intropattern(pat)
  :=
  exploit_main t ltac:(type of t) pat ltac:(fun _ => idtac).


Tactic Notation "exploit" constr(t)
  :=
  let H := fresh "H"
  in
    exploit_main t ltac:(type of t) H ltac:(fun _ => idtac).


Tactic Notation "so" constr(T) "as" simple_intropattern(pat)
  :=
  pose proof T as pat.


Tactic Notation "so" constr(T)
  :=
  pose proof T.


(** Misc *)

Lemma eq_fn_apply :
  forall {T U : Type} {x y : T} (f : T -> U),
    x = y
    -> f x = f y.
Proof.
intros; f_equal; auto.
Qed.


Ltac force_exact H :=
  (match goal with
   | |- ?C => 
     let D := type of H
     in
       replace C with D; [exact H |]
   end).


Ltac do2_main n tac :=
  (lazymatch n with
   | 0 => idtac
   | S ?n' => tac; [| do2_main n' tac]
   end).


Tactic Notation "do2" constr(n) tactic3(tac)
  :=
  do2_main n tac.


Ltac repeat2_main tac :=
  try (tac; [| repeat2_main tac]).


Tactic Notation "repeat2" tactic3(tac)
  :=
  repeat2_main tac.


Tactic Notation "renameover" hyp(H1) "into" hyp(H2) :=
  clear H2; rename H1 into H2.


Tactic Notation "injectionc" hyp(H) :=
  injection H; clear H.


Ltac destruct_all_main H :=
  (lazymatch type of H with
   | exists _:_, _ => 
               let H' := fresh "x"
               in
                 destruct H as [H' H]; destruct_all_main H'; destruct_all_main H

   | _ /\ _ => let H' := fresh "H"
               in
                 destruct H as [H' H]; destruct_all_main H'; destruct_all_main H

   | prod _ _ =>
               let H' := fresh "x"
               in
                 destruct H as [H' H]; destruct_all_main H'; destruct_all_main H

   | _ => idtac
   end).


Ltac destruct_all t :=
  first [
        destruct_all_main t
        |
        let H := fresh
        in
          pose proof t as H;

          destruct_all_main H
        ].


Ltac done := fail.


(** Notation *)

Definition car {P Q : Prop} (x : P /\ Q) : P.
elim x.
exact (fun p q => p).
Defined.

Definition cdr {P Q : Prop} (x : P /\ Q) : Q.
elim x.
exact (fun p q => q).
Defined.


Notation "a 'andel'" := (car a)
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'ander'" := (cdr a)
  (at level 11, left associativity, only parsing) : tactics_scope.

Open Scope tactics_scope.

Notation "a 'anderl'" := (a ander andel)
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderr'" := (a ander ander)
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderrl'" := (a ander ander andel)
  (at level 11, left associativity, only parsing) : tactics_scope.


Notation " x _#2 " := (x _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#3 " := (x _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#4 " := (x _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#5 " := (x _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#6 " := (x _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#7 " := (x _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#8 " := (x _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#9 " := (x _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#10 " := (x _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#11 " := (x _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#12 " := (x _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#13 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#14 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#15 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#16 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#17 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#18 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#19 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#20 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
