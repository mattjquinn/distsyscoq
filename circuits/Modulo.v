Require Import Coq.Arith.Arith.
Require Import Omega.

Print Nat.modulo.
Print Nat.divmod.

Inductive GF2 : Set := | z : GF2 | o : GF2.

Lemma mod_diff : forall n m : nat, n>=m /\ m <> 0 -> (n - m) mod m = n mod m.
  intros n m [H1 H2].
  rewrite <- (Nat.mod_add _ 1); try rewrite mult_1_l, Nat.sub_add; auto.
Qed.