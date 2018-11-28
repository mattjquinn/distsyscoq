(** Copyright (c) 2018 by Swirlds, Inc.
   Implemented by Karl Crary.
*)

Require Import Nat.
Require Import Omega.

Require Import Tact.


Definition one_half (n : nat) := n / 2.
Definition two_thirds (n : nat) := 2 * n / 3.
Definition one_third (n : nat) := n - two_thirds n.


Lemma majority_intersect_calculation :
  forall x y z,
    x > z / 2
    -> y > z / 2
    -> x + y - z > 0.
Proof.
intros x y z Hx Hy.
so (Nat.div_mod z 2 (Nat.neq_succ_0 _)) as Hzmod.
remember (z mod 2) as w eqn:Heqw.
destruct w as [|[|]]; try omega.
exfalso.
so (Nat.mod_upper_bound z 2 (Nat.neq_succ_0 _)).
omega.
Qed.


Lemma majority_atleasthalf_intersect_calculation :
  forall x y z,
    x > z / 2
    -> y >= S z / 2
    -> x + y - z > 0.
Proof.
intros x y z Hx Hy.
so (Nat.div_mod z 2 (Nat.neq_succ_0 _)) as Hzmod.
so (Nat.div_mod (S z) 2 (Nat.neq_succ_0 _)) as Hzmod'.
remember (z mod 2) as w eqn:Heqw.
destruct w as [|[|]].
  {
  replace (S z mod 2) with 1 in Hzmod'.
    { omega. }
  replace (S z) with (z + 1) by omega.
  rewrite -> (Nat.add_mod z 1 2 (Nat.neq_succ_0 _)).
  rewrite <- Heqw.
  cbn.
  reflexivity.
  }

  {
  replace (S z mod 2) with 0 in Hzmod'.
    { omega. }
  replace (S z) with (z + 1) by omega.
  rewrite -> (Nat.add_mod z 1 2 (Nat.neq_succ_0 _)).
  rewrite <- Heqw.
  cbn.
  reflexivity.
  }

  {
  exfalso.
  so (Nat.mod_upper_bound z 2 (Nat.neq_succ_0 _)).
  omega.
  }
Qed.


Lemma mod3_0 : (2 * 0) mod 3 = 0.
Proof. reflexivity. Qed.

Lemma mod3_1 : (2 * 1) mod 3 = 2.
Proof. reflexivity. Qed.

Lemma mod3_2 : (2 * 2) mod 3 = 1.
Proof. reflexivity. Qed.

Hint Rewrite mod3_0 mod3_1 mod3_2 : mod3.


Lemma supermajority_intersect_2_calculation :
  forall x y z,
    x > 2 * z / 3
    -> y > 2 * z / 3
    -> x + y - z > x / 2.
Proof.
intros x y z Hx Hy.
so (Nat.div_mod z 3 (Nat.neq_succ_0 _)) as Hzmod.
so (Nat.div_mod x 2 (Nat.neq_succ_0 _)) as Hxmod.
so (Nat.div_mod (2 * z) 3 (Nat.neq_succ_0 _)) as H2zmod.
rewrite -> (Nat.mul_mod 2 z 3 (Nat.neq_succ_0 _)) in H2zmod.
replace (2 mod 3) with 2 in H2zmod by reflexivity.
remember (z mod 3) as w eqn:Heqw.
destruct w as [|[|[|]]];
autorewrite with mod3 in H2zmod; try omega.
exfalso.
so (Nat.mod_upper_bound z 3 (Nat.neq_succ_0 _)).
omega.
Qed.


Lemma supermajority_intersect_3_calculation :
  forall w x y z,
    w > 2 * z / 3
    -> x > 2 * z / 3
    -> y > 2 * z / 3
    -> w + x + y - 2 * z > 0.
Proof.
intros w x y z Hw Hx Hy.
so (Nat.div_mod (2 * z) 3 (Nat.neq_succ_0 _)) as H2zmod.
rewrite -> (Nat.mul_mod 2 z 3 (Nat.neq_succ_0 _)) in H2zmod.
replace (2 mod 3) with 2 in H2zmod by reflexivity.
remember (z mod 3) as v eqn:Heqv.
destruct v as [|[|[|]]];
autorewrite with mod3 in H2zmod; try omega.
exfalso.
so (Nat.mod_upper_bound z 3 (Nat.neq_succ_0 _)).
omega.
Qed.


Lemma superminority_supermajority_intersect_calculation :
  forall x y z,
    x >= z - 2 * z / 3
    -> y > 2 * z / 3
    -> x + y - z > 0.
Proof.
intros x y z Hx Hy.
so (Nat.div_mod (2 * z) 3 (Nat.neq_succ_0 _)) as H2zmod.
rewrite -> (Nat.mul_mod 2 z 3 (Nat.neq_succ_0 _)) in H2zmod.
replace (2 mod 3) with 2 in H2zmod by reflexivity.
remember (z mod 3) as v eqn:Heqv.
destruct v as [|[|[|]]];
autorewrite with mod3 in H2zmod; try omega.
Qed.


Lemma four_thirds_le :
  forall n,
    n > 1 -> two_thirds n + two_thirds n >= n.
Proof.
intros n Hgt.
unfold two_thirds.
so (Nat.div_mod (2 * n) 3 (Nat.neq_succ_0 _)) as Hmod.
rewrite -> (Nat.mul_mod 2 n 3 (Nat.neq_succ_0 _)) in Hmod.
replace (2 mod 3) with 2 in Hmod by reflexivity.
remember (n mod 3) as w eqn:Heqw.
destruct w as [|[|[|]]];
autorewrite with mod3 in Hmod; try omega.
exfalso.
so (Nat.mod_upper_bound n 3 (Nat.neq_succ_0 _)).
omega.
Qed.


Lemma two_thirds_lt :
  forall n, n > 0 -> n > two_thirds n.
Proof.
intros n Hnonzero.
unfold two_thirds.
so (Nat.div_mod (2 * n) 3 (Nat.neq_succ_0 _)) as Hmod.
omega.
Qed.


Lemma majority_complement :
  forall x y,
    one_half (x + y) < x
    -> y <= one_half (x + y).
Proof.
intros x y H.
unfold one_half in *.
so (Nat.div_mod (x + y) 2 (Nat.neq_succ_0 _)) as Hmod.
remember ((x + y) mod 2) as w eqn:Heqw.
destruct w as [|[|]]; try omega.
so (Nat.mod_upper_bound (x + y) 2 (Nat.neq_succ_0 _)).
omega.
Qed.


Lemma half_supermajority :
  forall x y z,
    x + y > two_thirds z
    -> x >= y
    -> x >= one_third z.
Proof.
intros x y z Hplus Hxy.
unfold one_third.
unfold two_thirds in Hplus |- *.
so (Nat.div_mod (2 * z) 3 (Nat.neq_succ_0 _)) as H2zmod.
rewrite -> (Nat.mul_mod 2 z 3 (Nat.neq_succ_0 _)) in H2zmod.
replace (2 mod 3) with 2 in H2zmod by reflexivity.
remember (z mod 3) as w eqn:Heqw.
destruct w as [|[|[|]]];
autorewrite with mod3 in H2zmod; try omega.
exfalso.
so (Nat.mod_upper_bound z 3 (Nat.neq_succ_0 _)).
omega.
Qed.


Lemma two_thirds_mono :
  forall x y, x <= y -> two_thirds x <= two_thirds y.
Proof.
intros x y Hxy.
unfold one_third.
unfold two_thirds.
so (Nat.div_mod (2 * x) 3 (Nat.neq_succ_0 _)) as H2xmod.
rewrite -> (Nat.mul_mod 2 x 3 (Nat.neq_succ_0 _)) in H2xmod.
replace (2 mod 3) with 2 in H2xmod by reflexivity.
so (Nat.div_mod (2 * y) 3 (Nat.neq_succ_0 _)) as H2ymod.
rewrite -> (Nat.mul_mod 2 y 3 (Nat.neq_succ_0 _)) in H2ymod.
replace (2 mod 3) with 2 in H2ymod by reflexivity.
remember (x mod 3) as v eqn:Heqv.
remember (y mod 3) as w eqn:Heqw.
so (Nat.mod_upper_bound x 3 (Nat.neq_succ_0 _)).
so (Nat.mod_upper_bound y 3 (Nat.neq_succ_0 _)).
destruct v as [|[|[|]]]; try omega; destruct w as [|[|[|]]];
autorewrite with mod3 in H2xmod, H2ymod;
try omega.
Qed.


Lemma one_third_mono :
  forall x y, x <= y -> one_third x <= one_third y.
Proof.
intros x y Hxy.
unfold one_third.
unfold two_thirds.
so (Nat.div_mod (2 * x) 3 (Nat.neq_succ_0 _)) as H2xmod.
rewrite -> (Nat.mul_mod 2 x 3 (Nat.neq_succ_0 _)) in H2xmod.
replace (2 mod 3) with 2 in H2xmod by reflexivity.
so (Nat.div_mod (2 * y) 3 (Nat.neq_succ_0 _)) as H2ymod.
rewrite -> (Nat.mul_mod 2 y 3 (Nat.neq_succ_0 _)) in H2ymod.
replace (2 mod 3) with 2 in H2ymod by reflexivity.
remember (x mod 3) as v eqn:Heqv.
remember (y mod 3) as w eqn:Heqw.
so (Nat.mod_upper_bound x 3 (Nat.neq_succ_0 _)).
so (Nat.mod_upper_bound y 3 (Nat.neq_succ_0 _)).
destruct v as [|[|[|]]]; try omega; destruct w as [|[|[|]]];
autorewrite with mod3 in H2xmod, H2ymod;
try omega.
Qed.


Lemma div3_one_third :
  forall x,
    one_third x <= S (x / 3).
Proof.
intros x.
unfold one_third.
unfold two_thirds.
so (Nat.div_mod x 3 (Nat.neq_succ_0 _)) as Hxmod.
so (Nat.div_mod (2 * x) 3 (Nat.neq_succ_0 _)) as H2xmod.
rewrite -> (Nat.mul_mod 2 x 3 (Nat.neq_succ_0 _)) in H2xmod.
replace (2 mod 3) with 2 in H2xmod by reflexivity.
remember (x mod 3) as w eqn:Heqw.
destruct w as [|[|[|]]];
autorewrite with mod3 in H2xmod;
try omega.
so (Nat.mod_upper_bound x 3 (Nat.neq_succ_0 _)).
omega.
Qed.


(** Messy! *)
Lemma two_thirds_shift :
  forall x y,
    0 < y
    -> x * two_thirds y < y * S (two_thirds x).
Proof.
unfold two_thirds.
intros x y Hy.
replace (y * S (2 * x / 3)) with (y + y * (2 * x / 3)).
2:{
  rewrite -> (Nat.mul_comm y (S (2 * x / 3))).
  rewrite -> (Nat.mul_succ_l (2 * x / 3) y).
  rewrite -> (Nat.mul_comm (2 * x / 3) y).
  omega.
  }
rewrite -> (Nat.div_mod x 3 (Nat.neq_succ_0 _)).
rewrite -> (Nat.div_mod y 3 (Nat.neq_succ_0 _)).
remember (x / 3) as x'.
remember (y / 3) as y' eqn:Heqy'.
remember (x mod 3) as a.
remember (y mod 3) as b eqn:Heqb.
rewrite -> (Nat.mul_add_distr_r (3 * x') a).
rewrite -> (Nat.mul_add_distr_r (3 * y') b).
rewrite -> (Nat.mul_add_distr_l 2 _ b).
rewrite -> (Nat.mul_add_distr_l 2 _ a).
replace (2 * (3 * y') + 2 * b) with (2 * b + (2 * y') * 3) by omega.
replace (2 * (3 * x') + 2 * a) with (2 * a + (2 * x') * 3) by omega.
rewrite -> !Nat.div_add; try omega.
rewrite -> (Nat.mul_add_distr_l (3 * x')).
rewrite -> (Nat.mul_add_distr_l (3 * y')).
replace (3 * y' * (2 * x')) with (3 * x' * (2 * y')).
2:{
  rewrite <- !Nat.mul_assoc.
  f_equal.
  rewrite -> (Nat.mul_comm x').
  rewrite -> (Nat.mul_comm y').
  rewrite <- !Nat.mul_assoc.
  f_equal.
  rewrite -> Nat.mul_comm.
  reflexivity.
  }
cut (3 * x' * (2 * b / 3) + a * (2 * b / 3 + 2 * y') < 3 * y' + b + (3 * y' * (2 * a / 3)) + (b * (2 * a / 3 + 2 * x'))).  
  {
  intro.
  omega.
  }
rewrite -> !Nat.mul_add_distr_l.
replace (a * (2 * y')) with (2 * a * y').
2:{
  rewrite -> (Nat.mul_comm 2 a).
  rewrite <- Nat.mul_assoc.
  reflexivity.
  }
replace (b * (2 * x')) with (2 * b * x').
2:{
  rewrite -> (Nat.mul_comm 2 b).
  rewrite <- Nat.mul_assoc.
  reflexivity.
  }
replace (3 * x' * (2 * b / 3)) with (3 * ((2 * b) / 3) * x').
2:{
  rewrite <- (Nat.mul_assoc 3).
  rewrite <- (Nat.mul_assoc 3).
  f_equal.
  rewrite <- Nat.mul_comm.
  reflexivity.
  }
replace (3 * y' * (2 * a / 3)) with (3 * ((2 * a) / 3) * y').
2:{
  rewrite <- (Nat.mul_assoc 3).
  rewrite <- (Nat.mul_assoc 3).
  f_equal.
  rewrite <- Nat.mul_comm.
  reflexivity.
  }
so (Nat.mod_upper_bound x 3 (Nat.neq_succ_0 _)).
so (Nat.mod_upper_bound y 3 (Nat.neq_succ_0 _)).
assert (b = 0 -> y' > 0).
  {
  intro Hb.
  destruct y'; try omega.
  rewrite -> Hb in Heqb.
  cut (y = 0).
    {
    intro.
    omega.
    }
  rewrite -> (Nat.div_exact y 3 (Nat.neq_succ_0 _) ander); omega.
  }
destruct b as [|[|[|]]]; try omega; destruct a as [|[|[|]]]; cbn; omega.
Qed.


Lemma two_thirds_of_three :
  forall x,
    x >= 3
    -> two_thirds x >= 2.
Proof.
intros x Hx3.
unfold two_thirds.
so (Nat.div_mod (2 * x) 3 (Nat.neq_succ_0 _)) as Hmod.
rewrite -> (Nat.mul_mod 2 x 3 (Nat.neq_succ_0 _)) in Hmod.
replace (2 mod 3) with 2 in Hmod by reflexivity.
remember (x mod 3) as v eqn:Heqv.
so (Nat.mod_upper_bound x 3 (Nat.neq_succ_0 _)).
destruct v as [|[|[|]]]; autorewrite with mod3 in Hmod; omega.
Qed.


Lemma average_range :
  forall x y, x <= y -> x <= (x + y) / 2 <= y.
Proof.
intros x y Hxy.
split.
  {
  rewrite <- (Nat.div_mul x 2 (Nat.neq_succ_0 _)) at 1.
  apply Nat.div_le_mono; omega.
  }

  {
  rewrite <- (Nat.div_mul y 2 (Nat.neq_succ_0 _)) at 2.
  apply Nat.div_le_mono; omega.
  }
Qed.


Lemma one_half_plus_two :
  forall x, (2 + x) / 2 = S (x / 2).
Proof.
intro x.
replace (2 + x) with (1 * 2 + x) by reflexivity.
rewrite -> Nat.div_add_l; omega.
Qed.


Lemma atleasthalf_le_all :
  forall n,
    S n / 2 <= n.
Proof.
intros n.
so (Nat.div_mod (S n) 2 (Nat.neq_succ_0 _)) as Hzmod.
omega.
Qed.


Lemma under_half_complement :
  forall m n,
    m < S n / 2
    -> S n / 2 <= n - m.
Proof.
intros m n Hlt.
so (Nat.div_mod (S n) 2 (Nat.neq_succ_0 _)) as Hzmod.
omega.
Qed.
