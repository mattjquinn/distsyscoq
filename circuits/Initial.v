(*
Require Coq.Bool.Bool.
Require Coq.Bool.Bvector.
Compute Bvector.Bvect_true 4.
Compute Bvector.Blow 4 (Bvector.Bvect_false 5).
Compute Bvector.BVand 4 (Bvector.Bvect_false 4) (Bvector.Bvect_true 4).

Require Coq.Numbers.Integer.NatPairs.ZNatPairs.
Require Coq.ZArith.Znat.
Require Import ZArith Coq.ZArith.Int.

https://coq.inria.fr/library/Coq.Bool.Bvector.html
https://github.com/adampetcher/fcf (oracles, group theory, etc in Coq)
https://github.com/PrincetonUniversity/VST/blob/master/sha/SHA256.v
  - Purely Coq
https://github.com/secworks/sha256/tree/master/src/rtl
  - In Verilog

https://www.nandland.com/vhdl/modules/module-full-adder.html
*)

Require Import Verilog.

Notation "b1 & b2" := (bitwise_and b1 b2)
                      (at level 40, left associativity).
Notation "b1 'XOR' b2" := (bitwise_xor b1 b2)
                          (at level 40, left associativity).
Notation "b1 | b2" := (bitwise_or b1 b2)
                      (at level 40, left associativity).

Record FullAdderOut := {
  sum : bit;
  carry : bit;
}.

Definition FullAdder (i1 i2 ic : bit) : FullAdderOut :=
  {| sum   :=  i1 XOR i2 XOR ic;
     carry :=  ((i1 XOR i2) & ic) | (i1 & i2);
  |}.
Example fulladder_case1 : (FullAdder L L L) = {| sum := L; carry := L; |}.
Proof. reflexivity. Qed.
Example fulladdr_case2 : (FullAdder L L H) = {| sum := H; carry := L; |}.
Proof. reflexivity. Qed.
Example fulladder_case3 : (FullAdder L H L) = {| sum := H; carry := L; |}.
Proof. reflexivity. Qed.
Example fulladder_case4 : (FullAdder L H H) = {| sum := L; carry := H; |}.
Proof. reflexivity. Qed.
Example fulladder_case5 : (FullAdder H L L) = {| sum := H; carry := L; |}.
Proof. reflexivity. Qed.
Example full_adder_case6 : (FullAdder H L H) = {| sum := L; carry := H; |}.
Proof. reflexivity. Qed.
Example full_adder_case7 : (FullAdder H H L) = {| sum := L; carry := H; |}.
Proof. reflexivity. Qed.
Example full_adder_case8 : (FullAdder H H H) = {| sum := H; carry := H; |}.
Proof. reflexivity. Qed.

(* TODO PROVE: If two ANDs with same inputs are ANDed together,
   the output will be true only if inputs are true. *)

(* TODO: Implement Caesar's cipher
   - Use bitvectors to represent each possible character
   - How to represent gates?
   - Prove that shifting by any multiple
            of 26 yields a ciphertext equivalent to plaintext.
   - Figure out how to extract this to Verilog.
   - Run extracted Verilog with Icarus simulator.
References
https://electronics.stackexchange.com/questions/316831/caesar-cipher-digital-circuit

A -> 00
B -> 01
C -> 10
D -> 11

Shift by 1: A -> B, B -> C, C -> D, D -> A
*)