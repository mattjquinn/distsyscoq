Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import Verilog.

Definition bitvec := (Vector.t bit).

Fixpoint list_of_vec {n} (v : bitvec n) : nat :=
  match v with
    | [] => 0
    | h::t => 1 + (list_of_vec t)
  end.

Record FullAdderOut := {
  sum : bit;
  carry : bit;
}.

Definition FullAdder (i1 i2 ic : bit) : FullAdderOut :=
  {| sum   :=  (VerilogOperations.bitwise_xor
                  (VerilogOperations.bitwise_xor i1 i2) ic);
     carry :=  (VerilogOperations.bitwise_or
                ((VerilogOperations.bitwise_and
                  (VerilogOperations.bitwise_xor i1 i2) ic))
                (VerilogOperations.bitwise_and i1 i2));
  |}.

Record NBitVectorAdderOut (n:nat) := {
  s: bitvec n;
  c: bit;
}.

Fixpoint NBitAdder n (a b : bitvec n) : (bitvec n) :=
  match n with
    | 0 => Vector.nil bit
    | S n' => L :: (NBitAdder n' (Vector.tl a) (Vector.tl b))
  end.

(* LEFT OFF HERE ON MARCH 2nd; may need to read more about
   dependent types to get the above to succeed. *)
(* MARCH 5: Look at:
   - https://github.com/AbsInt/CompCert/blob/master/lib/Integers.v
   - https://github.com/mit-plv/bbv/blob/4dcd180f06/Word.v
      (and more generally: https://github.com/mit-plv/bbv)
   - http://plv.csail.mit.edu/bedrock/Tutorial.html
*)

    | x::y, j::k => H :: (NBitAdder y k)
    | _, _ => (Vector.nil bit)
  end.


    | j::k, x::y => let fa := (FullAdder j x carry) in
      (NBitAdder k y fa.(carry) fa.(sum)::sum)
    | [] , [] => {| s := sum; c := carry |}
  end.