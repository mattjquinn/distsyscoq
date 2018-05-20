(*
module nBitAdder(f, cOut, a, b, cIn);
  parameter n = 7;

  output reg [n:0] f;
  output reg cOut;
  input [n:0] a;
  input [n:0] b;
  input cIn;

  always @(a, b, cIn)
    {cOut, f} = a + b + cIn;
endmodule

LOOK AT: http://color.inria.fr/doc/CoLoR.Util.Vector.VecUtil.html
         (* Require Import CoLoR.Util.Vector.VecArith. *)

GOAL
Here we focus on building something that can encode/decode
*a single letter* at a time; doing multiple is simply repetition and
doesn't involve any additional proofs. The goal is to define Coq
constructs that allow for a PROOF that encoding/decoding with a shift
key equal to the size of the alphabet simply returns the original
ciphertext. Then we should be able to translate the gate definitions
to Verilog for waveform visualization.

DEVELOPMENT STEPS
0) Define n-bit addition with n-bit vector inputs/outputs + cin such that
   the definition can be translated to Verilog (see above).
1) Enumerate the alphabet (start small at first).
2) Use this adder to add an element from the alphabet (n-bit vector)
   with the shift key (n-bit vector).
3) Define a subtractor (modulo gate?) (or modify the adder, see
   https://en.wikipedia.org/wiki/Adder%E2%80%93subtractor)
   that continually subtracts the size of the alphabet from the ciphertext
   as long as the CT is > the size of the alphabet.
4) PROVE that for every key, adding the size of the alphabet to it
   results in the same CT.
*)

Require Import Verilog.

Notation "b1 & b2" := (VerilogOperations.bitwise_and b1 b2)
                      (at level 40, left associativity).
Notation "b1 'XOR' b2" := (VerilogOperations.bitwise_xor b1 b2)
                          (at level 40, left associativity).
Notation "b1 | b2" := (VerilogOperations.bitwise_or b1 b2)
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

Require Import Coq.Vectors.Vector.
(* Use this library for useful lemmas/axioms : *)
Require Import CoLoR.Util.Vector.VecArith.
Import VectorNotations.
Notation bitvec := (Vector.t bit).
Notation empty_bitvec := (Vector.t bit []).
Notation vector := Vector.t.
Notation Vnil := Vector.nil.
Notation Vcons := Vector.cons.
Notation Vhead := Vector.hd.
Notation Vtail := Vector.tl.
Notation Vconst := Vector.const.
Check (bitvec 4).
Check Vector.tl([L ; L ; L ; H]).
Check L :: [H ; L].



Record NBitVectorAdderOut (n:nat) := {
  s: bitvec n;
  c: bit;
}.

Print Grammar constr.

Fixpoint NBitAdder (n:nat) (a b : bitvec (S n)) : n :=
  match a, b with
    | [], [] => O
    | ah::at, (bh::bt) => 1 + (NBitAdder at bt)
  end.

Fixpoint NBitAdder (n:nat) (a b : bitvec (S n))
                   (carry : bit) (sum : bitvec (S n))
                      : NBitVectorAdderOut (S n) :=
  match (Vector.hd a), (Vector.hd b) with
    | a0, b0 => let fa := (FullAdder a0 b0 carry) in
      (NBitAdder (n - 1) (Vector.tl a) (Vector.tl b) fa.(carry) fa.(sum))
    | _ , _ => {| s := sum; c := carry |}
  end.


Require Import Coq.Bool.Bvector.
Compute Bvect_true 4.
Compute Blow 4 (Bvect_false 5).
Compute BVand 4 (Bvect_false 4) (Bvect_true 4).

Record BVectorAdderOut (n:nat) := {
  s: Bvector n;
  c: bit;
}.

Fixpoint BitVectorAdder (n:nat) (a b : Bvector n)

Definition BVectorAdder (n:nat) (a b : Bvector n) : (BVectorAdderOut n) :=
  {| s := Bvect_false n;
     c := L
  |}.

Record TwoBitAdderOut := {
  s0: bit;
  s1 : bit;
  c2 : bit;
}.

Definition TwoBitAdder (a0 a1 b0 b1 c0 : bit) : TwoBitAdderOut :=
  let fa0 := (FullAdder a0 b0 c0) in
    let fa1 := (FullAdder a1 b1 fa0.(carry)) in
      {| s0 := fa0.(sum);
         s1 := fa1.(sum);
         c2 := fa1.(carry);
      |}.

(* TODO: Implement Caesar's cipher
   - Start with alphabet of size 2, then 4, then 8.
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




00 -> A
01 -> B
10 -> C
11 -> D

00 (A) + 01 (shift) -> B
00 (A) + 11 (shift) -> D
00 (A) + 00 (shift) -> A

Need 2-bit adder in Coq
Need to define alphabet in Coq

*)