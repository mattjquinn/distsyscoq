(*********************************************************************
 * TODO: Write lexer/parser for Verilog to Coq intermediate form.
 * TODO: Write inductive execution relation; execution proceeds by
 *       clock ticks; each tick, all modules are "evaluated" once.
 * TODO: Look at bitwise OR/AND/NOT - are these definitions defined correctly
 *       in the face of Verilog's X and Z signal states?
 * TODO: Extend module relation to handle multiple output assocSignal
         assertions (will need in future).
 *********************************************************************)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Import ListNotations.
Open Scope string_scope.

Inductive id : Type :=
  | Id : string -> id.

Definition beq_id x y :=
  match x, y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Check string_dec.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros id. destruct id. simpl. destruct (string_dec s s).
  - reflexivity.
  - unfold not in n. exfalso. apply n. reflexivity.
Qed.

Definition total_map (A:Type) := id -> A.
Definition t_empty {A:Type} (v : A) : total_map A := (fun _ => v).
Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Proof.
  intros [s1] [s2].
  unfold beq_id.
  destruct (string_dec s1 s2).
  - subst. split. reflexivity. reflexivity.
  - split.
    + intros contra. inversion contra.
    + intros H. inversion H. subst. destruct n. reflexivity.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros. unfold t_update. rewrite <-beq_id_refl. reflexivity.
Qed.

Theorem t_update_neq : forall (X : Type) v x1 x2 (m : total_map X),
  x1 <> x2 -> (t_update m x1 v) x2 = m x2.
Proof.
  intros. unfold t_update. apply beq_id_false_iff in H.
  rewrite H. reflexivity. Qed.

Inductive signal : Set := | L | H | X | Z.

(**
 * TODO: IMPORTANT
 * NEED TO SET THIS UP so that ANY GIVEN id can only be associated with one
 * signal at any given time. Current setup makes it possible to prove
 * that an identifier can be associated with multiple signals at once.
 *)
Inductive assocSignal : id -> signal -> Prop :=
| AssocIdSignal : forall i s, (assocSignal i s).

Lemma sig_assoc_eq : forall i s1 s2,
    (assocSignal i s1) ->
    (assocSignal i s2) ->
    s1 = s2.
  Admitted.
(* TODO: Do something with identifier? *)

Lemma one_signal_assoc_per_id : forall i s1 s2,
    (assocSignal i s1) ->
    s1 <> s2 ->
    ~ (assocSignal i s2).
Proof.
  intros. unfold not. intros.
  unfold not in H1. apply H1. apply sig_assoc_eq with (i:=i); assumption.
Qed.

Notation "i @ s" := (assocSignal (Id i) s) (at level 70).
    
Inductive option (A : Type) : Type :=
| Some : A -> option A
| None : string -> option A.
Arguments Some {A} _.
Arguments None {A}.

Definition bitwiseOr (s1 s2 : signal) : signal :=
  match s1, s2 with
  | H, _ => H
  | _, H => H
  | _, _ => L
  end.

Definition bitwiseAnd (s1 s2 : signal) : signal :=
  match s1, s2 with
  | H, H => H
  | _, _ => L
  end.

Definition bitwiseNot (s : signal) : signal :=
  match s with
  | L => H
  | H => L
  | _ => s
  end.

Inductive io : Set :=
| IOInWire : list id -> io
| IOOutWire : list id -> io.

Definition extractIoIdents (i : io) : list id :=
  match i with
  | IOInWire l => l
  | IOOutWire l => l
  end.

Inductive exp : Set :=
| EUnassigned : exp
| EId : id -> exp
| EBitOr : exp -> exp -> exp
| EBitAnd : exp -> exp -> exp
| EBitNot : exp -> exp.

Definition exp_map := total_map exp.
Definition empty_exp_map := t_empty EUnassigned.

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l: list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Inductive expEvalR : exp -> exp_map -> signal -> Prop :=
| E_BitOrLeft : forall e1 e2 em outsig,
    expEvalR e1 em outsig ->
    expEvalR (EBitOr e1 e2) em outsig
| E_BitOrRight : forall e1 e2 em outsig,
    expEvalR e2 em outsig ->
    expEvalR (EBitOr e1 e2) em outsig
| E_IdExpression : forall i em outsig e,
    em i = e ->
    expEvalR e em outsig ->
    expEvalR (EId i) em outsig
| E_IdSignal : forall i em outsig,
    i @ outsig ->
    expEvalR (EId (Id i)) em outsig
| E_BitAnd : forall e1 e2 em outsig,
    expEvalR e1 em outsig ->
    expEvalR e2 em outsig ->
    expEvalR (EBitAnd e1 e2) em outsig
| E_BitNot : forall e em outsig,
    expEvalR e em (bitwiseNot outsig) ->
    expEvalR (EBitNot e) em outsig.

Inductive modstmt: Set :=
| MSWire : list id -> modstmt
| MSAssign : id -> exp -> modstmt.

Inductive modEvalR : exp_map -> Prop -> Prop :=
| E_SelectOutput: forall i exp sig em,
    em (Id i) = exp ->
    expEvalR exp em sig ->
    modEvalR em (i @ sig).
(*
 * Trying to get multiple clause propositions to work...
| E_ReduceSignalsHead : forall em tail i sig,
    modEvalR em (i @ sig) ->
    modEvalR em tail ->
    modEvalR em ((i @ sig) \/ tail).
*)

Inductive module : Set :=
| CModule : string -> list io -> list modstmt -> module.

Definition MComparator_1Bit : module :=
  (CModule "eq1"
           [(IOInWire [Id "io1"; Id "io2"]); (IOOutWire [Id "eq"])]
           [(MSWire [Id "p0"; Id "p1"]) ;
            (MSAssign (Id "eq") (EBitOr (EId (Id "p0")) (EId (Id "p1")))) ;
            (MSAssign (Id "p0") (EBitAnd (EBitNot (EId (Id "i0")))
                                         (EBitNot (EId (Id "i1"))))) ;
            (MSAssign (Id "p1") (EBitAnd (EId (Id "i0")) (EId (Id "i1")))) 
 ]).

Definition buildExpMap (m : module) : exp_map :=
  match m with
  | CModule _ io stmts =>
    fold (fun stmt s =>
            match stmt with
            | MSWire ids => s
            | MSAssign i e => t_update s i e
            end) (rev stmts) empty_exp_map
  end.

Notation "m #~# outputs" := (modEvalR (buildExpMap m) outputs)
                           (at level 70).

Example mcomp1bit_high : "i0" @ H ->
                         "i1" @ H ->
                         MComparator_1Bit #~# ("eq" @ H).
Proof.
  intros. simpl. eapply E_SelectOutput.
  - rewrite t_update_neq. rewrite t_update_neq. apply t_update_eq.
    apply beq_id_false_iff. reflexivity.
    apply beq_id_false_iff. reflexivity.
  - apply E_BitOrRight. eapply E_IdExpression.
    + apply t_update_eq.
    + apply E_BitAnd; apply E_IdSignal; assumption.
Qed.

Example mcomp1bit_low : "i0" @ L ->
                        "i1" @ L ->
                        MComparator_1Bit #~# ("eq" @ H).
Proof.
  intros. simpl. eapply E_SelectOutput.
  - rewrite t_update_neq. rewrite t_update_neq. apply t_update_eq.
    apply beq_id_false_iff. reflexivity.
    apply beq_id_false_iff. reflexivity.
  - apply E_BitOrLeft. eapply E_IdExpression.
    + rewrite t_update_neq. apply t_update_eq. apply beq_id_false_iff.
      reflexivity.
    + apply E_BitAnd;
        apply E_BitNot; simpl; apply E_IdSignal; assumption.
Qed.

Lemma mcomp1bit_low_with_nonlow_not_high :
  MComparator_1Bit #~# ("eq" @ H) ->
   ("i0" @ L /\ "i1" @ L)
   \/ ("i1" @ L /\ "i0" @ L)
   \/ ("i0" @ H /\ "i1" @ H)
   \/ ("i1" @ H /\ "i0" @ H).
Admitted.

Theorem mcomp1bit_only_high_on_equal_inputs : forall s1 s2,
    "i0" @ s1 ->
    "i1" @ s2 ->
    s1 <> s2 ->
    ~ MComparator_1Bit #~# ("eq" @ H).
Proof.
  intros. destruct s1, s2; try (destruct H2; reflexivity); unfold not; intros.
  - apply mcomp1bit_low_with_nonlow_not_high in H3
      as [| [| [| ] ] ]; destruct H3 as [].
    + apply one_signal_assoc_per_id with (s2:=L) in H1.
      unfold not in H1. apply H1. apply H4. auto.
    + apply one_signal_assoc_per_id with (s2:=L) in H1.
      unfold not in H1. apply H1. apply H3. auto.
    + apply one_signal_assoc_per_id with (s2:=H) in H0.
      unfold not in H0. apply H0. apply H3. auto.
    + apply one_signal_assoc_per_id with (s2:=H) in H0.
      unfold not in H0. apply H0. apply H4. auto.
  - apply mcomp1bit_low_with_nonlow_not_high in H3
      as [| [| [| ] ] ]; destruct H3 as [].
    + apply one_signal_assoc_per_id with (s2:=L) in H1.
      unfold not in H1. apply H1. apply H4. auto.
    
    
    
