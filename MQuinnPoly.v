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

Theorem app_nil_r : forall (X:Type), forall l : list X,
  l ++ [] = l.
Proof.
  intros X l. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity. Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity. Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity. Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity. Qed.

Theorem rev_involutive : forall X: Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite IHl. reflexivity. Qed.

Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.
Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
  : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* Exercise combine_checks
   - What does Check @combine print?
     combine := forall X : Type,
      forall Y : Type, forall lx : list X, forall ly : list Y
      : list (X * Y)
*)
Check @combine.
(* Correct answer: 
   @combine : forall X Y : Type, list X -> list Y -> list (X * Y)

   - What does Compute (combine [1;2] [false;false;true;true]) print?
     [(1,false),(2,false)]
*)
Compute (combine [1;2] [false;false;true;true]).
(* Above is correct, but missing type annotation : list (nat * bool) *)

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (a, b) :: l' => (a :: (fst (split l')), b :: (snd (split l')))
  end.
Example test_split: split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X:Type) : Type :=
  | Some: X -> option X
  | None: option X.
Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X: Type} (l:list X) (n:nat) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n 0 then Some a else nth_error l' (pred n) end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X:Type} (l:list X) : option X :=
  match l with
  | [] => None
  | h :: t => Some h
  end.
Check @hd_error.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l : list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t) else (filter test t)
  end.

Example test_filter1 : filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X:Type} (l : list X): bool :=
  beq_nat (length l) 1.

Example test_filter2:
  filter length_is_1
    [ [1;2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun': doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (fun l => beq_nat (length l) 1)
    [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (blt_nat 7 n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type}
                     (test: X -> bool)
                     (l : list X) : list X * list X :=
 (filter test l, filter (fun l => negb (test l)) l).
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3: map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Lemma map_distr : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros X Y f l1 l2. induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity. Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. rewrite map_distr. simpl. reflexivity. Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.
Example test_flat_map1: flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
  : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Module ImplicitArgsPlayground.
Fixpoint filter (X:Type) (test: X -> bool) (l : list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter X test t) else (filter X test t)
  end.

Example test_filter1 : filter nat evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X:Type} (l : list X): bool :=
  beq_nat (length l) 1.

Example test_filter2:
  filter (list nat) length_is_1
    [ [1;2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter nat oddb l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun': doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (list nat) (fun l => beq_nat (length l) 1)
    [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter nat (fun n => andb (evenb n) (blt_nat 7 n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type}
                     (test: X -> bool)
                     (l : list X) : list X * list X :=
 (filter X test l, filter X (fun l => negb (test l)) l).
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map (X Y : Type) (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map X Y f t)
  end.

Example test_map1: map nat nat (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2: map nat bool oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3: map nat (list bool) (fun n => [evenb n;oddb n]) 
  [2;1;2;5] = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

End ImplicitArgsPlayground.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb).
Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.
Example fold_example3 : fold app [[1]; []; [2;3]; [4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* Exercise: fold_types_different
   Since X and Y are different types, we can apply functions that
   map from X to Y and combine them; for instance, checking of all
   numbers in a list are even:
*)
Example fold_example4 : fold (fun n b => andb (evenb n) b)
  [2; 4; 6; 8] true = true.
Proof. reflexivity. Qed.
Example fold_example5 : fold (fun n b => andb (evenb n) b)
  [2; 3; 6; 8] true = false.
Proof. reflexivity. Qed.

Definition constfun {X: Type} (x : X) : nat -> X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plust3': doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plust3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Module Exercises.

Definition fold_length {X: Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(*Lemma fold_length_distr : forall X (l : list X) (x : X),
  fold_length ([x] ++ l) = fold_length [x] + fold_length l.
Proof.
  intros X l x. induction l.
  - simpl. reflexivity.
  - simpl.*)

Lemma fold_length_replace : forall X (l : list X),
  fold_length l = fold (fun _ n => S n) l 0.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite fold_length_replace. simpl.
    rewrite <- IHl. rewrite fold_length_replace. reflexivity.
Qed.

Theorem fold_length_correct' : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l.
  - simpl. reflexivity.
  - simpl. unfold fold_length. simpl.
    rewrite <- IHl. unfold fold_length. reflexivity.
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x l_of_y => (f x) :: l_of_y) l [].
Example test_fold_map1: fold_map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_fold_map2: fold_map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_fold_map3: fold_map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Theorem fold_map_correct : forall X Y (l : list X) (f : X -> Y),
  fold_map f l = map f l.
Proof.
  intros X Y l f. induction l.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. unfold fold_map. simpl. reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := (f (fst p)) (snd p).

(* Check @prod_curry will return: forall X : Type, forall Y : Type,
  forall Z : Type -> f : X * Y -> X -> Y -> Z. *)
Check @prod_curry.
(* CORRECT ANSWER: forall X Y Z : Type, (X * Y -> Z) -> X -> Y -> Z *)
(* Check @prod_uncurry will return: forall X Y Z : Type,
    (X -> Y -> Z) -> (X * Y) -> Z. *)
Check @prod_uncurry.
(* ANSWER IS CORRECT *)

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y. unfold prod_curry.
  unfold prod_uncurry. simpl. reflexivity. Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p. unfold prod_uncurry.
  unfold prod_curry. destruct p. simpl. reflexivity.
Qed.

(* Exercise: nth_error_informal
   Theorem: ∀X n l, length l = n -> @nth_error X l n = None
   Proof: By induction on n.
     Base: Our induction hypothesis is:
        length l = 0 -> @nth_error X l 0 = None
     The only list of length 0 is the nil list []. Thus l is [],
     and by definition of nth_error, [] is mapped to None, satisfying
     our hypothesis.

     Inductive: Our induction hypothesis is:
        length l = n + 1 -> @nth_error X l (n + 1) = None
     Any list X of length (n + 1) has (n + 1) elements of type X within
     it. If each is mapped to an index (natural number) starting with 0,
     as done in nth_error, the (n + 1)th element will be []. By definition
     of nth_error, [] is mapped to None, satisfying our hypothesis.
*)

Module Church.

Definition nat := forall X : Type, (X -> X) -> X -> X.
Definition one : nat := fun (X : Type) (f : X -> X) (x : X) => f x.
Definition two : nat := fun (X : Type) (f : X -> X) (x : X) => f (f x).
Definition zero: nat := fun (X : Type) (f : X -> X) (x : X) => x.
Definition three: nat := @doit3times.
Check @doit3times.


Definition succ (n : nat) : nat := 
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).
Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).
Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition mult (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.
Compute mult one three.
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(* I do not understand this definition for exp, I barely
   understand the above ones for plus and mult. I had to look
   this one up online. The polymorphism here is extremely confusing,
   and I don't currently know of a way to step through or visualize
   this definition. *)
Definition exp (n m : nat) : nat :=
  fun (X : Type) => m (X -> X) (n X).
Compute exp two three.
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.
Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.

End Church.
End Exercises.