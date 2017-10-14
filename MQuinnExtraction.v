Extraction Language Ocaml.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import MQuinnImpCEvalFun.

Extraction "imp1.ml" ceval_step.

Extract Inductive bool => "bool" [ "true" "false" ].

 Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant beq_nat => "( = )".

Extraction "imp2.ml" ceval_step.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inductive sumbool => "bool" ["true" "false"].

Require Import MQuinnImp.
Require Import MQuinnImpParser.
Extraction "imp.ml" empty_state ceval_step parse.

