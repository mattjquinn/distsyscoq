Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith.
Require Import MQuinnImp MQuinnMaps.

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        t_update st l (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
        st (* bogus *)
  end.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_state
  | S i' =>
    match c with
    | SKIP => st
    | l ::= a1 => t_update st l (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step2 st c1 i'
          else ceval_step2 st c2 i'
    | WHILE b1 DO c1 END =>
        if (beval st b1)
        then let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c i'
        else st
    end
  end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
    | SKIP => Some st
    | l ::= a1 => Some (t_update st l (aeval st a1))
    | c1 ;; c2 =>
        match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step3 st c1 i'
          else ceval_step3 st c2 i'
    | WHILE b1 DO c1 END =>
        if (beval st b1)
        then match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c i'
          | None => None
          end
        else Some st
  end
end.

Notation "'LETOPT' x <== e1 'IN' e2"
  := (match e1 with
      | Some x => e2
      | None => None
    end)
  (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP => Some st
      | l ::= a1 => Some (t_update st l (aeval st a1))
      | c1 ;; c2 => LETOPT st' <== ceval_step st c1 i' IN
                    ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
  end
end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
    | None => None
    | Some st => Some (st X, st Y, st Z)
  end.

Compute
     (test_ceval empty_state
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3
            ELSE Z ::= ANum 4
          FI)).

Definition pup_to_n : com :=
  WHILE (BNot (BEq (ANum 0) (AId X))) DO
    Y ::= (APlus (AId Y) (AId X)) ;;
    X ::= (AMinus (AId X) (ANum 1))
  END.

Compute (test_ceval (t_update empty_state X 5) pup_to_n).

Example pup_to_n_1 :
  test_ceval (t_update empty_state X 5) pup_to_n = Some (0, 15, 0).
Proof. reflexivity. Qed.

