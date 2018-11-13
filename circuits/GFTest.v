Require Import ZArith.

Open Scope Z_scope.
Goal forall a b c:Z,
    (a + b + c) ^ 2 =
    a * a + b ^ 2 + c * c + 2 * a * b + 2 * a * c + 2 * b * c.
Proof.
  intros. ring.
Qed.

Lemma step1 : forall qH qL x : Z,
    ((qH * x) + qL) ^ 2 = ((qH ^ 2) * (x ^ 2)) + (2 * qH * qL * x) + qL ^ 2.
  intros. ring.
Qed.

(*
Lemma step2 : forall qH qL x : Z,
    ((qH ^ 2) * (x ^ 2)) + (2 * qH * qL * x) + qL ^ 2 = (qH^2) * (x^2) + qL^2.
  intros. ring.
Qed.

Lemma step2 : forall qH qL x phi : Z,
    ((qH * x) + qL) ^ 2 = (qH ^ 2) * (x + phi) + (qL ^ 2).
  intros. rewrite step1.
Qed.
*)


(* TODO: Define irreducibles as axioms; later find out better defn. *)


