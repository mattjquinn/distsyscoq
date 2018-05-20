Inductive bit :=
  | H : bit
  | L : bit.

Module VerilogOperations.

Definition bitwise_and (b1 b2 : bit) : bit :=
  match b1, b2 with
  | L, _ | _, L => L
  | H, H => H
  end.
Notation "b1 & b2" := (bitwise_and b1 b2)
                      (at level 40, left associativity).
Example bitwise_and_case1 : (L & L) = L.
Proof. reflexivity. Qed.
Example bitwise_and_case2 : (L & H) = L.
Proof. reflexivity. Qed.
Example bitwise_and_case3 : (H & L) = L.
Proof. reflexivity. Qed.
Example bitwise_and_case4 : (H & H) = H.
Proof. reflexivity. Qed.

Definition bitwise_xor (b1 b2 : bit) : bit :=
  match b1, b2 with
  | L, H | H, L => H
  | _, _ => L
  end.
Notation "b1 'XOR' b2" := (bitwise_xor b1 b2)
                          (at level 40, left associativity).
Example bitwise_xor_case1 : (L XOR L) = L.
Proof. reflexivity. Qed.
Example bitwise_xor_case2 : (L XOR H) = H.
Proof. reflexivity. Qed.
Example bitwise_xor_case3 : (H XOR L) = H.
Proof. reflexivity. Qed.
Example bitwise_xor_case4 : (H XOR H) = L.
Proof. reflexivity. Qed.

Definition bitwise_or (b1 b2 : bit) : bit :=
  match b1, b2 with
  | H, _ | _, H => H
  | L, L => L
  end.
Notation "b1 | b2" := (bitwise_or b1 b2)
                      (at level 40, left associativity).
Example bitwise_or_case1 : (L | L) = L.
Proof. reflexivity. Qed.
Example bitwise_or_case2 : (L | H) = H.
Proof. reflexivity. Qed.
Example bitwise_or_case3 : (H | L) = H.
Proof. reflexivity. Qed.
Example bitwise_or_case4 : (H | H) = H.
Proof. reflexivity. Qed.

End VerilogOperations.